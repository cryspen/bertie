use std::{
    fs::File,
    io::{BufReader, Read, Write},
    net::TcpStream,
    collections::HashMap
};

use rand::{CryptoRng, RngCore};

use crate::{
    server::ServerDB,
    tls13cert::{rsa_private_key, verification_key_from_cert},
    tls13crypto::{Algorithms, SignatureKey, SignatureScheme},
    tls13utils::{
        AppData, Bytes, INVALID_COMPRESSION_LIST, MISSING_KEY_SHARE, PARSE_FAILED,
        PROTOCOL_VERSION_ALERT,
    },
    Server,
    tls13keyscheduler::key_schedule::*,
};

use super::bertie_stream::{read_record, BertieError, BertieStream, TlsStream};

/// The server state.
///
/// It holds the stream, the TLS server state, an i/o buffer, and a database
/// with necessary key and certificate information.
pub struct ServerState<Stream: Read + Write> {
    sstate: Option<Server>,
    stream: Stream,
    db: ServerDB,
    read_buffer: Vec<u8>,
}

impl<Stream: Read + Write> ServerState<Stream> {
    /// Create a new client state for a `Stream`.
    pub(crate) fn new(stream: Stream, db: ServerDB) -> Self {
        Self {
            sstate: None,
            stream,
            read_buffer: vec![],
            db,
        }
    }
}

impl<Stream: Read + Write> TlsStream<Stream> for ServerState<Stream> {
    fn write_tls(&mut self, bytes: &[u8]) -> Result<(), BertieError> {
        let sstate = match self.sstate.take() {
            Some(state) => state,
            None => return Err(BertieError::InvalidState),
        };

        let (wire_bytes, new_state) = sstate.write(AppData::new(bytes.into()))?;
        self.sstate = Some(new_state);

        // Write out the request
        self.stream
            .write_all(&wire_bytes.declassify())
            .map_err(|e| e.into())
    }

    fn read_tls(&mut self) -> Result<Vec<u8>, BertieError> {
        let mut sstate = match self.sstate.take() {
            Some(state) => state,
            None => return Err(BertieError::InvalidState),
        };

        let application_data = loop {
            let record = read_record(&mut self.read_buffer, &mut self.stream)?;
            let ad;
            (ad, sstate) = sstate.read(&record.into())?;
            match ad {
                Some(application_data) => break application_data,
                None => continue,
            }
        };
        self.sstate = Some(sstate);
        Ok(application_data.into_raw().declassify())
    }

    fn stream_mut(&mut self) -> &mut Stream {
        &mut self.stream
    }
}

impl<Stream: Read + Write> BertieStream<ServerState<Stream>> {
    /// Open a connection with the given stream, ciphersuite, and host.
    pub fn server_with_stream(
        host: &str,
        ciphersuite: Algorithms,
        stream: Stream,
        cert_file: &str,
        key_file: &str,
    ) -> Result<Self, BertieError> {
        let db = init_db(host, key_file, cert_file)?;

        Ok(Self {
            state: ServerState::new(stream, db),
            ciphersuite,
            host: host.to_string(),
        })
    }
}

impl BertieStream<ServerState<TcpStream>> {
    /// Start a new server TLS connection.
    /// The [`TcpStream`] has to be connected before starting the server.
    ///
    /// A common pattern for the server would look as follows.
    /// ```
    /// use std::{net::{TcpStream, TcpListener}, thread};
    /// use bertie::{stream::BertieStream, tls13crypto::SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519};
    /// use rand::thread_rng;
    ///
    /// let host = "localhost";
    /// let port = 3443;
    ///
    /// // Run a client
    /// eprintln!("[Client] Starting ...");
    /// let client_handle = thread::spawn(move || {
    ///     let mut stream = BertieStream::client(host, port, SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519, &mut thread_rng()).expect("Error connecting to server");
    ///     stream.write(b"Hello, I'm the Bertie test client.").unwrap();
    ///     let server_msg = stream.read().unwrap();
    ///     assert_eq!(
    ///         &b"Greetings, I'm the Bertie test server.\nBy."[..],
    ///         &server_msg[..]
    ///     );
    /// });
    ///
    /// // Listen on and open TCP connection
    /// let listener = TcpListener::bind((host, port)).unwrap();
    /// let (server_tcp_stream, _adr) = listener.accept().unwrap();
    ///
    /// // Server is waiting for the incoming TLS handshake.
    /// let mut server = BertieStream::server(
    ///     host,
    ///     port,
    ///     server_tcp_stream,
    ///     SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519,
    ///     "tests/assets/p256_cert.der",
    ///     "tests/assets/p256_key.der",
    /// )
    /// .expect("Error starting server");
    /// server.connect(&mut thread_rng()).unwrap();
    ///
    /// // Handshake finished.
    ///
    /// // Read client application messages.
    /// let client_msg = server.read().unwrap();
    /// eprintln!("Client says: {}", String::from_utf8_lossy(&client_msg));
    /// assert_eq!(&b"Hello, I'm the Bertie test client."[..], &client_msg[..]);
    /// server
    ///     .write(b"Greetings, I'm the Bertie test server.\nBy.")
    ///     .unwrap();
    ///
    /// // Close the client's thread.
    /// client_handle.join().unwrap();
    /// ```
    pub fn server(
        host: &str,
        port: u16,
        stream: TcpStream,
        ciphersuite: Algorithms,
        cert_file: &str,
        key_file: &str,
    ) -> Result<Self, BertieError> {
        let db = init_db(host, key_file, cert_file)?;

        Ok(Self {
            state: ServerState {
                db,
                stream,
                read_buffer: vec![],
                sstate: None,
            },
            host: host.to_string(),
            ciphersuite,
        })
    }

    /// Connect the incoming TLS stream.
    /// This function blocks until it was able to read the TLS client hello.
    pub fn connect(&mut self, rng: &mut (impl RngCore + CryptoRng)) -> Result<(), BertieError> {
        let client_hello = read_record(&mut self.state.read_buffer, &mut self.state.stream)?;

        let mut ks : TLSkeyscheduler = TLSkeyscheduler {
            keys: HashMap::new(),
        };

        match Server::accept(
            self.ciphersuite,
            self.state.db.clone(),
            &client_hello.into(),
            rng,
            &mut ks,
        ) {
            Err(x) => {
                match x {
                    INVALID_COMPRESSION_LIST => {
                        self.write_all(&[21, 03, 03, 00, 02, 2, 47])?;
                    }
                    PROTOCOL_VERSION_ALERT => {
                        self.write_all(&[21, 03, 03, 00, 02, 2, 70])?;
                    }
                    MISSING_KEY_SHARE => {
                        // alerts here are optional
                        eprintln!("Hello message was missing a key share.");
                    }
                    _ => unimplemented!("unknown error {}", x),
                }
                return Err(x.into());
            }
            Ok((sh, sf, server_state)) => {
                self.write_all(&sh.declassify())?;
                let ccs_rec = Bytes::from_hex("140303000101");
                self.write_all(&ccs_rec.declassify())?;
                self.write_all(&sf.declassify())?;

                let ccs = read_record(&mut self.state.read_buffer, &mut self.state.stream)?;
                self.check_ccs_message(&ccs)?;

                let cf_rec = read_record(&mut self.state.read_buffer, &mut self.state.stream)?;
                let sstate = server_state.read_handshake(&cf_rec.into())?;

                self.state.sstate = Some(sstate);
            }
        }

        Ok(())
    }

    /// Close the connection.
    pub fn close(mut self) -> Result<(), BertieError> {
        // send a close_notify alert
        self.write_all(&[21, 03, 03, 00, 02, 1, 00])?;
        Ok(())
    }

    fn check_ccs_message(&self, buf: &[u8]) -> Result<(), BertieError> {
        if buf.len() == 6
            && buf[0] == 0x14
            && buf[1] == 0x03
            && buf[2] == 0x03
            && buf[3] == 0x00
            && buf[4] == 0x01
            && buf[5] == 0x01
        {
            Ok(())
        } else {
            Err(PARSE_FAILED.into())
        }
    }

    /// Write all `bytes` into the stream.
    ///
    /// Returns an error if not all bytes can be written.
    fn write_all(&mut self, bytes: &[u8]) -> Result<(), BertieError> {
        self.state
            .stream_mut()
            .write_all(bytes)
            .map_err(|e| e.into())
    }

    /// Read from the stream.
    ///
    /// This reads from the encrypted TLS channel
    pub fn read(&mut self) -> Result<Vec<u8>, BertieError> {
        self.state.read_tls()
    }

    /// Write to the stream.
    ///
    /// This writes to the encrypted TLS stream.
    pub fn write(&mut self, bytes: &[u8]) -> Result<usize, BertieError> {
        self.state.write_tls(bytes)?;
        Ok(bytes.len())
    }
}

/// Set up the server database.
pub fn init_db(host: &str, key_file: &str, cert_file: &str) -> Result<ServerDB, BertieError> {
    let sni = host.as_bytes();
    let signature_key = read_file(key_file)?;
    let cert = read_file(cert_file)?.into();

    let spki = verification_key_from_cert(&cert)?;
    let raw_key = match spki.0 {
        SignatureScheme::EcdsaSecp256r1Sha256 => {
            let mut raw_key = vec![];
            for (i, &byte) in signature_key.iter().enumerate() {
                if i == 0 && byte != 0x30
                // We don't handle larger sizes that are differently encoded.
                {
                    return Err(BertieError::TLS(255)); // TODO: error code
                }

                // We only look for the first octet string.
                if byte == 0x04 {
                    let len = signature_key[i + 1];
                    raw_key = signature_key[i + 2..i + 2 + usize::from(len)].to_vec();
                    break;
                }
            }
            raw_key
        }
        SignatureScheme::RsaPssRsaSha256 => {
            // Read the private exponent (d) from the key.
            rsa_private_key(&Bytes::from(signature_key))?.declassify()
        }
        _ => unreachable!("Unsupported signature scheme {:?}", spki.0),
    };
    if raw_key.is_empty() {
        // We weren't able to read the key.
        return Err(BertieError::TLS(255)); // TODO: error code
    }
    Ok(ServerDB::new(
        sni.into(),
        cert,
        SignatureKey::from(raw_key),
        None,
    ))
}

/// Read a binary file, e.g. key or certificate.
fn read_file(file_name: &str) -> Result<Vec<u8>, BertieError> {
    let f = File::open(file_name)?;
    let mut reader = BufReader::new(f);
    let mut buffer = Vec::new();
    reader.read_to_end(&mut buffer)?;

    Ok(buffer)
}
