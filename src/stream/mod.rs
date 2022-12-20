#[cfg(feature = "evercrypt")]
use evercrypt_cryptolib::*;
#[cfg(not(feature = "evercrypt"))]
use hacspec_cryptolib::*;
use hacspec_lib::{ByteSeq, Seq, U8};

use std::{
    convert::TryInto,
    io::{Read, Write},
    net::TcpStream,
};

use crate::{Algorithms, TLSError, INSUFFICIENT_DATA};

mod client;
mod server;

const SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    NamedGroup::X25519,
    false,
    false,
);

const DEFAULT_CIPHERSUITE: Algorithms = SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519;

#[derive(Debug)]
pub enum BertieError {
    InvalidState,
    Io(std::io::Error),
    TLS(TLSError),
}

impl From<std::io::Error> for BertieError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

impl From<TLSError> for BertieError {
    fn from(error: TLSError) -> Self {
        Self::TLS(error)
    }
}

pub trait TlsStream {
    /// Write `bytes` out to the connection, using the underlying TLS connection.
    fn write_tls(&mut self, bytes: &[u8]) -> Result<(), BertieError>;

    /// Read bytes from the TLS connection.
    fn read_tls(&mut self) -> Result<Vec<u8>, BertieError>;

    /// Get hte mutable underlying TCP stream.
    fn stream_mut(&mut self) -> &mut TcpStream;
}

#[derive(Debug)]
pub struct BertieStream<State> {
    state: State,
    host: String,
    port: u16,
    ciphersuites: Vec<Algorithms>,
}

/// Read a TLS record from the TCP stream.
fn read_record<R: Read>(read_buffer: &mut Vec<u8>, input: &mut R) -> Result<Seq<U8>, BertieError> {
    // ```c
    // struct {
    //     ContentType type; (21: alert, 22: handshake, 23: app data)
    //     ProtocolVersion legacy_record_version; (0303)
    //     uint16 length;
    //     opaque fragment[TLSPlaintext.length];
    // } TLSPlaintext/TlsCiphertext;
    // ```
    loop {
        // After reading the first chunk, we check some
        if read_buffer.len() >= 5 {
            let length: usize = u16::from_be_bytes(read_buffer[3..=4].try_into().unwrap()).into();

            if read_buffer.len() >= 5 + length {
                // We've read everything (length bytes)
                // info_record(&self.buffer[..5 + length]);
                // eprintln!("buf[0..10]: {:02x?}", &self.buffer[0..10]);
                return Ok(ByteSeq::from_public_slice(
                    &read_buffer.drain(..5 + length).collect::<Vec<u8>>(),
                ));
            }
        }

        // Buffer to read chunks into.
        let mut tmp = [0u8; 4096];
        match input.read(&mut tmp) {
            Ok(l) => match l {
                0 => {
                    #[cfg(test)]
                    {
                        eprintln!("{:?}", backtrace::Backtrace::new());
                    }
                    return Err(INSUFFICIENT_DATA.into());
                }
                amt => {
                    let data = &tmp[..amt];
                    read_buffer.extend_from_slice(data);
                }
            },
            Err(e) => {
                return Err(e.into());
            }
        }
    }
}

impl<State: TlsStream> BertieStream<State> {
    /// Define the set of ciphersuites to use for this stream.
    pub fn with_ciphersuites(&mut self, ciphersuites: Vec<Algorithms>) {
        self.ciphersuites = ciphersuites;
    }

    fn write_byte_seq(&mut self, bytes: ByteSeq) -> Result<(), BertieError> {
        self.write_all(&bytes.into_native())
    }

    fn write_all(&mut self, bytes: &[u8]) -> Result<(), BertieError> {
        self.state
            .stream_mut()
            .write_all(bytes)
            .map_err(|e| e.into())
    }

    pub fn read(&mut self) -> Result<Vec<u8>, BertieError> {
        self.state.read_tls()
    }

    pub fn write(&mut self, bytes: &[u8]) -> Result<usize, BertieError> {
        self.state.write_tls(bytes)?;
        Ok(bytes.len())
    }
}
