//! # TLS Client
//!
//! TLS streaming client API.

use rand::CryptoRng;
use std::{
    collections::HashMap,
    eprintln,
    io::{Read, Write},
    net::TcpStream,
    println,
    string::ToString,
    vec,
    vec::Vec,
};
// use tracing::{event, Level};

use super::t13_stream::{read_record, t13Error, t13Stream, TlsStream};
use crate::{
    tls13crypto::*, tls13keyscheduler::key_schedule::TLSkeyscheduler, tls13utils::*, Client,
};

pub struct ClientState<Stream: Read + Write> {
    stream: Stream,
    read_buffer: Vec<u8>,
    cstate: Option<Client>,
}

impl<Stream: Read + Write> ClientState<Stream> {
    /// Create a new client state for a `Stream`.
    pub(crate) fn new(stream: Stream) -> Self {
        Self {
            stream,
            read_buffer: vec![],
            cstate: None,
        }
    }
}

impl<T: Read + Write> TlsStream<T> for ClientState<T> {
    fn write_tls(&mut self, bytes: &[u8]) -> Result<(), t13Error> {
        let cstate = match self.cstate.take() {
            Some(state) => state,
            None => return Err(t13Error::InvalidState),
        };

        let (wire_bytes, new_state) = cstate.write(AppData::new(bytes.into()))?;
        self.cstate = Some(new_state);

        // Write out the request
        self.stream
            .write_all(&wire_bytes.declassify())
            .map_err(|e| e.into())
    }

    fn read_tls(&mut self) -> Result<Vec<u8>, t13Error> {
        let mut state = match self.cstate.take() {
            Some(state) => state,
            None => return Err(t13Error::InvalidState),
        };

        let application_data = loop {
            let record = read_record(&mut self.read_buffer, &mut self.stream)?;
            let ad;
            (ad, state) = state.read(&record.into())?;
            match ad {
                Some(application_data) => break application_data,
                None => continue,
            }
        };
        self.cstate = Some(state);
        Ok(application_data.into_raw().declassify())
    }

    fn stream_mut(&mut self) -> &mut T {
        &mut self.stream
    }
}

impl<Stream: Read + Write> t13Stream<ClientState<Stream>> {
    /// Open a connection with the given stream, ciphersuite, and host.
    pub fn open_with_stream(
        host: &str,
        ciphersuite: Algorithms,
        stream: Stream,
    ) -> Result<Self, t13Error> {
        Ok(Self {
            state: ClientState::new(stream),
            ciphersuite,
            host: host.to_string(),
        })
    }
}

impl t13Stream<ClientState<TcpStream>> {
    /// Create a new t13 stream connecting to `host:port`.
    ///
    /// This uses a set of default ciphersuites.
    /// If you want to define your own set of ciphersuites, use [`open`],
    /// [`with_ciphersuites`], and [`start`].
    pub fn client(
        host: &str,
        port: u16,
        ciphersuite: Algorithms,
        rng: &mut impl CryptoRng,
    ) -> Result<Self, t13Error> {
        let mut stream = Self::open(host, port, ciphersuite)?;
        stream.ciphersuite = ciphersuite;
        stream.start(rng)?;
        Ok(stream)
    }

    /// Open a connection to `host:port`.
    pub fn open(host: &str, port: u16, ciphersuite: Algorithms) -> Result<Self, t13Error> {
        let stream = TcpStream::connect((host, port))?;
        stream.set_nodelay(true)?;
        Ok(Self {
            state: ClientState::new(stream),
            ciphersuite,
            host: host.to_string(),
        })
    }

    /// Open the connection.
    ///
    /// This will fail if the connection wasn't set up correctly.
    pub fn start(&mut self, rng: &mut impl CryptoRng) -> Result<(), t13Error> {
        // Initialize TLS 1.3 client.
        if self.state.cstate.is_some() {
            return Err(t13Error::InvalidState);
        }

        let mut ks: TLSkeyscheduler = TLSkeyscheduler {
            keys: HashMap::new(),
        };

        // Client Hello
        let (client_hello, cstate) = {
            let sni = self.host.as_bytes();
            Client::connect(
                self.ciphersuite,
                &Bytes::from(sni),
                None,
                None,
                rng,
                &mut ks,
            )?
        };
        // event!(Level::TRACE, "client hello: {}", client_hello.as_hex());
        // event!(Level::DEBUG, "  {ciphersuite:?}");
        self.write_all(&client_hello.declassify())?;

        let mut read_buffer = Vec::new();

        // Server Hello
        let server_hello = read_record(&mut read_buffer, &mut self.state.stream)?;

        // Check for alerts
        if server_hello[0] == 21 {
            eprintln!(
                "Server does not support proposed algorithms. {:?}",
                self.ciphersuite
            );
            return Err(UNSUPPORTED_ALGORITHM.into());
        }

        // Read server hello
        let cstate = match cstate.read_handshake(&Bytes::from(server_hello), &mut ks) {
            Ok((_, cstate)) => cstate,
            Err(e) => {
                println!(" >>> ERROR {e}");
                match e {
                    UNSUPPORTED_ALGORITHM => {
                        eprintln!("Server does not support proposed algorithms.")
                    }
                    PROTOCOL_VERSION_ALERT => eprintln!("Wrong TLS protocol version TLS({:?})", e),
                    APPLICATION_DATA_INSTEAD_OF_HANDSHAKE => {
                        eprintln!("Server sent application data instead of a handshake message.")
                    }
                    MISSING_KEY_SHARE => eprintln!("Hello message was missing a key share."),
                    DECODE_ERROR => eprintln!("Decode error."), // parsing of the server hello failed
                    _ => eprintln!("t13 client error {}", e),
                }
                return Err(e.into());
            }
        };

        // Read change cipherspec
        // This is sent in many cases for middlebox compatibility. But it's not
        // actually part of TLS 1.3
        let change_cipher_spec = read_record(&mut read_buffer, &mut self.state.stream)?;

        // Finish the handshake
        let mut cf_rec = None;
        let mut cstate = cstate;
        while cf_rec.is_none() {
            let rec = read_record(&mut read_buffer, &mut self.state.stream)?;

            let (new_cf_rec, new_cstate) = match cstate.read_handshake(&rec.into(), &mut ks) {
                Ok((new_cf_rec, new_cstate)) => (new_cf_rec, new_cstate),
                Err(e) => {
                    match e {
                        // signature verification failed or parsing of the certificate failed
                        INVALID_SIGNATURE => eprintln!("Invalid server signature"),
                        _ => eprintln!("t13 client error {}", e),
                    }
                    return Err(e.into());
                }
            };
            cf_rec = new_cf_rec;
            cstate = new_cstate;
        }

        // Let's pretend to be TLS 1.2 as well.
        let change_cipher_spec = Bytes::from_hex("140303000101");
        self.write_all(&change_cipher_spec.declassify())?;

        let cf_rec = cf_rec.unwrap();
        self.write_all(&cf_rec.declassify())?;

        // Store the state.
        self.state.cstate = Some(cstate);

        Ok(())
    }

    fn write_all(&mut self, bytes: &[u8]) -> Result<(), t13Error> {
        self.state
            .stream_mut()
            .write_all(bytes)
            .map_err(|e| e.into())
    }

    /// Read from the stream.
    ///
    /// This reads from the encrypted TLS channel
    pub fn read(&mut self) -> Result<Vec<u8>, t13Error> {
        self.state.read_tls()
    }

    /// Write to the stream.
    ///
    /// This writes to the encrypted TLS stream.
    pub fn write(&mut self, bytes: &[u8]) -> Result<usize, t13Error> {
        self.state.write_tls(bytes)?;
        Ok(bytes.len())
    }
}

#[cfg(test)]
mod tests {
    use rand::{self, rng};

    use crate::tls13crypto::SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519;

    use super::*;
    use std::{format, string::String};

    #[test]
    fn client() {
        let host = "google.com";
        let port = 443;
        let mut stream = t13Stream::client(
            host,
            port,
            SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519,
            &mut rng(),
        )
        .expect("Error connecting to server");

        // Send HTTP GET
        let request = format!("GET / HTTP/1.1\r\nHost: {}\r\n\r\n", host);
        stream
            .write(request.as_bytes())
            .expect("Error writing to t13 stream");
        let response = stream.read().unwrap();
        let response_string = String::from_utf8_lossy(&response);
        eprintln!("{response_string:}");
    }
}
