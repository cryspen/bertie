use std::{
    convert::TryInto,
    eprintln,
    io::{Read, Write},
    string::String,
    vec::Vec,
};

use crate::{tls13crypto::*, tls13utils::*};

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

pub trait TlsStream<T: Write + Read> {
    /// Write `bytes` out to the connection, using the underlying TLS connection.
    fn write_tls(&mut self, bytes: &[u8]) -> Result<(), BertieError>;

    /// Read bytes from the TLS connection.
    fn read_tls(&mut self) -> Result<Vec<u8>, BertieError>;

    /// Get the mutable underlying stream of type `T`.
    fn stream_mut(&mut self) -> &mut T;
}

#[derive(Debug)]
pub struct BertieStream<State> {
    pub(super) state: State,
    pub(super) host: String,
    pub(super) ciphersuite: Algorithms,
}

/// Read a TLS record from the stream.
pub(super) fn read_record<R: Read>(
    read_buffer: &mut Vec<u8>,
    input: &mut R,
) -> Result<Vec<u8>, BertieError> {
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
                return Ok(read_buffer.drain(..5 + length).collect::<Vec<u8>>());
            }
        }

        // Buffer to read chunks into.
        let mut tmp = [0u8; 4096];
        match input.read(&mut tmp) {
            Ok(l) => match l {
                0 => {
                    eprintln!("closing ...");
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
