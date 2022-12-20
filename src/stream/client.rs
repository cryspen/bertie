#[cfg(feature = "evercrypt")]
use evercrypt_cryptolib::*;
#[cfg(not(feature = "evercrypt"))]
use hacspec_cryptolib::*;

use hacspec_lib::{ByteSeq, U8};

use rand::{thread_rng, Rng};
use std::{io::Write, net::TcpStream};

use crate::{
    app_data, app_data_bytes, client_connect, client_read, client_read_handshake, client_write,
    eq1, Algorithms, Client,
};

use super::{read_record, BertieError, BertieStream, TlsStream, DEFAULT_CIPHERSUITE};

const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    NamedGroup::X25519,
    false,
    false,
);

pub struct ClientState {
    stream: TcpStream,
    read_buffer: Vec<u8>,
    cstate: Option<Client>,
}

impl ClientState {
    /// Create a new client state for a [`TcpStream`].
    pub(crate) fn new(stream: TcpStream) -> Self {
        Self {
            stream,
            read_buffer: vec![],
            cstate: None,
        }
    }
}

impl TlsStream for ClientState {
    fn write_tls(&mut self, bytes: &[u8]) -> Result<(), BertieError> {
        let cstate = match self.cstate.take() {
            Some(state) => state,
            None => return Err(BertieError::InvalidState),
        };

        let request = ByteSeq::from_public_slice(bytes);

        let (wire_bytes, new_state) = client_write(app_data(request), cstate)?;
        self.cstate = Some(new_state);

        // Write out the request
        self.stream
            .write_all(&wire_bytes.into_native())
            .map_err(|e| e.into())
    }

    fn read_tls(&mut self) -> Result<Vec<u8>, BertieError> {
        let cstate = match self.cstate.take() {
            Some(state) => state,
            None => return Err(BertieError::InvalidState),
        };

        let mut cstate = cstate;
        let application_data = loop {
            let record = read_record(&mut self.read_buffer, &mut self.stream)?;
            let ad;
            (ad, cstate) = client_read(&record, cstate)?;
            match ad {
                Some(application_data) => break application_data,
                None => continue,
            }
        };
        let app_data = app_data_bytes(application_data);
        self.cstate = Some(cstate);
        Ok(app_data.into_native())
    }

    fn stream_mut(&mut self) -> &mut TcpStream {
        &mut self.stream
    }
}

impl BertieStream<ClientState> {
    /// Create a new Bertie stream connecting to `host:port`.
    ///
    /// This uses a set of default ciphersuites.
    /// If you want to define your own set of ciphersuites, use [`open`],
    /// [`with_ciphersuites`], and [`start`].
    pub fn client(host: &str, port: u16) -> Result<Self, BertieError> {
        eprintln!("[Client] Starting new Client connection ...");
        eprintln!("         {host}:{port}");
        let mut stream = Self::open(host, port)?;
        eprintln!("Opened Client TCP connection.");
        stream.ciphersuites = vec![DEFAULT_CIPHERSUITE];
        stream.start()?;
        Ok(stream)
    }

    /// Open a connection to `host:port`.
    pub fn open(host: &str, port: u16) -> Result<Self, BertieError> {
        let stream = TcpStream::connect((host, port))?;
        stream.set_nodelay(true)?;
        Ok(Self {
            state: ClientState::new(stream),
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
                // TODO: get better randomness.
                thread_rng().fill(&mut entropy);
                Entropy::from_public_slice(&entropy)
            };

            // TODO: support multiple ciphersuites.
            client_connect(self.ciphersuites[0], &sni, None, None, entropy)?
        };
        // eprintln!("Client Hello: {}", client_hello.to_hex());
        self.write_byte_seq(client_hello)?;

        let mut read_buffer = Vec::new();

        // Server Hello
        let server_hello = read_record(&mut read_buffer, &mut self.state.stream)?;
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
        let change_cipher_spec = read_record(&mut read_buffer, &mut self.state.stream)?;

        // Finish the handshake
        let mut cf_rec = None;
        let mut cstate = cstate;
        while cf_rec == None {
            let rec = read_record(&mut read_buffer, &mut self.state.stream)?;

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
        self.write_byte_seq(change_cipher_spec)?;

        let cf_rec = cf_rec.unwrap();
        self.write_byte_seq(cf_rec)?;

        // Store the state.
        self.state.cstate = Some(cstate);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn client() {
        let host = "cloudflare.com";
        let port = 443;
        let mut stream = BertieStream::client(host, port).expect("Error connecting to server");

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
