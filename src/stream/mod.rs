#[cfg(feature = "evercrypt")]
use evercrypt_cryptolib::*;
#[cfg(not(feature = "evercrypt"))]
use hacspec_cryptolib::*;
use hacspec_lib::{ByteSeq, Seq, U8};
use rand::{thread_rng, Rng};

use std::{
    convert::TryInto,
    io::{Read, Write},
    net::TcpStream,
};

use crate::{
    app_data, app_data_bytes, client_connect, client_read, client_read_handshake, client_write,
    eq1, Algorithms, Client, TLSError, INSUFFICIENT_DATA,
};

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

const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    NamedGroup::X25519,
    false,
    false,
);
const SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    NamedGroup::X25519,
    false,
    false,
);

const DEFAULT_CIPHERSUITE: Algorithms = SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519;

#[derive(Default)]
struct ClientState {
    cstate: Option<Client>,
}

#[derive(Default, Debug)]
struct ServerState {}

#[derive(Debug)]
pub struct BertieStream<State> {
    stream: TcpStream,
    buffer: Vec<u8>,
    state: State,
    host: String,
    port: u16,
    ciphersuites: Vec<Algorithms>,
}

impl BertieStream<ClientState> {
    /// Create a new Bertie stream connecting to `host:port`.
    ///
    /// This uses a set of default ciphersuites.
    /// If you want to define your own set of ciphersuites, use [`open`],
    /// [`with_ciphersuites`], and [`start`].
    pub fn connect(host: &str, port: u16) -> Result<Self, BertieError> {
        let mut stream = Self::open(host, port)?;
        stream.ciphersuites = vec![DEFAULT_CIPHERSUITE];
        stream.start()?;
        Ok(stream)
    }

    /// Open a connection to `host:port`.
    pub fn open(host: &str, port: u16) -> Result<Self, BertieError> {
        let stream = TcpStream::connect((host, port))?;
        stream.set_nodelay(true)?;
        Ok(Self {
            stream,
            buffer: Vec::new(),
            state: ClientState::default(),
            ciphersuites: vec![],
            host: host.to_string(),
            port,
        })
    }
    /// Open the connection.
    ///
    /// This will fail if the connection wasn't set up correctly.
    pub fn start(&mut self) -> Result<(), BertieError> {
        // Initialize TLS 1.3 client.
        if self.state.cstate.is_some() {
            return Err(BertieError::InvalidState);
        }

        // Client Hello
        let (client_hello, cstate) = {
            let sni = ByteSeq::from_public_slice(self.host.as_bytes());
            let entropy = {
                let mut entropy = [0u8; 64];
                thread_rng().fill(&mut entropy);
                Entropy::from_public_slice(&entropy)
            };

            // TODO: support multiple ciphersuites.
            client_connect(self.ciphersuites[0], &sni, None, None, entropy)?
        };
        // eprintln!("Client Hello: {}", client_hello.to_hex());
        self.write_all(client_hello)?;

        // Server Hello
        let server_hello = self.read_record()?;
        // eprintln!("Server Hello: {}", server_hello.to_hex());

        // Check for alerts
        if eq1(server_hello[0], U8(21)) {
            eprintln!(
                "Server does not support proposed algorithms. {:?}",
                self.ciphersuites
            );
            return Err(UNSUPPORTED_ALGORITHM.into());
        }

        // Read server hello
        let cstate = match client_read_handshake(&server_hello, cstate) {
            Ok((_, cstate)) => cstate,
            Err(e) => {
                match e {
                    6 => eprintln!("Server does not support proposed algorithms."),
                    137 => eprintln!("Wrong TLS protocol version TLS({:?})", e),
                    138 => {
                        eprintln!("Server sent application data instead of a handshake message.")
                    }
                    139 => eprintln!("Hello message was missing a key share."),
                    _ => eprintln!("Bertie client error {}", e),
                }
                return Err(e.into());
            }
        };

        // Read change cipherspec
        // This is sent in many cases for middlebox compatibility. But it's not
        // actually part of TLS 1.3
        let change_cipher_spec = self.read_record()?;

        // Finish the handshake
        let mut cf_rec = None;
        let mut cstate = cstate;
        while cf_rec == None {
            let rec = self.read_record()?;

            let (new_cf_rec, new_cstate) = match client_read_handshake(&rec, cstate) {
                Ok((new_cf_rec, new_cstate)) => (new_cf_rec, new_cstate),
                Err(e) => {
                    match e {
                        7 => eprintln!("Invalid server signature"), // signature verification failed
                        140 => eprintln!("Invalid server signature"), // parsing of the certificate failed
                        _ => eprintln!("Bertie client error {}", e),
                    }
                    return Err(e.into());
                }
            };
            cf_rec = new_cf_rec;
            cstate = new_cstate;
        }

        // Let's pretend to be TLS 1.2 as well.
        let change_cipher_spec = ByteSeq::from_hex("140303000101");
        self.write_all(change_cipher_spec)?;

        let cf_rec = cf_rec.unwrap();
        self.write_all(cf_rec)?;

        // Store the state.
        self.state.cstate = Some(cstate);

        Ok(())
    }

    /// Write bytes to the stream
    pub fn write(&mut self, bytes: &[u8]) -> Result<(), BertieError> {
        let cstate = match self.state.cstate.take() {
            Some(state) => state,
            None => return Err(BertieError::InvalidState),
        };

        let request = ByteSeq::from_public_slice(bytes);

        let (wire_bytes, new_state) = client_write(app_data(request), cstate)?;
        self.state.cstate = Some(new_state);

        // Write out the request
        self.write_all(wire_bytes)
    }

    /// Read bytes from the stream
    pub fn read(&mut self) -> Result<Vec<u8>, BertieError> {
        let cstate = match self.state.cstate.take() {
            Some(state) => state,
            None => return Err(BertieError::InvalidState),
        };

        let mut cstate = cstate;
        let application_data = loop {
            let record = self.read_record()?;
            let ad;
            (ad, cstate) = client_read(&record, cstate)?;
            match ad {
                Some(application_data) => break application_data,
                None => continue,
            }
        };
        let app_data = app_data_bytes(application_data);
        self.state.cstate = Some(cstate);
        Ok(app_data.into_native())
    }
}

impl<State: Default> BertieStream<State> {
    /// Define the set of ciphersuites to use for this stream.
    pub fn with_ciphersuites(&mut self, ciphersuites: Vec<Algorithms>) {
        self.ciphersuites = ciphersuites;
    }

    fn write_all(&mut self, bytes: ByteSeq) -> Result<(), BertieError> {
        self.stream
            .write_all(&bytes.into_native())
            .map_err(|e| e.into())
    }

    /// Read a TLS record from the TCP stream.
    fn read_record(&mut self) -> Result<Seq<U8>, BertieError> {
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
            if self.buffer.len() >= 5 {
                let length: usize =
                    u16::from_be_bytes(self.buffer[3..=4].try_into().unwrap()).into();

                if self.buffer.len() >= 5 + length {
                    // We've read everything (length bytes)
                    // info_record(&self.buffer[..5 + length]);
                    // eprintln!("buf[0..10]: {:02x?}", &self.buffer[0..10]);
                    return Ok(ByteSeq::from_public_slice(
                        &self.buffer.drain(..5 + length).collect::<Vec<u8>>(),
                    ));
                }
            }

            // Buffer to read chunks into.
            let mut tmp = [0u8; 4096];
            match self.stream.read(&mut tmp) {
                Ok(l) => match l {
                    0 => {
                        return Err(INSUFFICIENT_DATA.into());
                    }
                    amt => {
                        let data = &tmp[..amt];
                        self.buffer.extend_from_slice(data);
                    }
                },
                Err(e) => {
                    return Err(e.into());
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::BertieStream;

    #[test]
    fn client() {
        let host = "cloudflare.com";
        let port = 443;
        let mut stream = BertieStream::connect(host, port).expect("Error connecting to server");

        // Send HTTP GET
        let request = format!("GET / HTTP/1.1\r\nHost: {}\r\n\r\n", host);
        stream
            .write(request.as_bytes())
            .expect("Error writing to Bertie stream");
        let response = stream.read().unwrap();
        let response_string = String::from_utf8_lossy(&response);
        eprintln!("{response_string:}");
    }
}
