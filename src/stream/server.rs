use std::{io::Write, net::TcpStream};

#[cfg(feature = "evercrypt")]
use evercrypt_cryptolib::*;
#[cfg(not(feature = "evercrypt"))]
use hacspec_cryptolib::*;
use hacspec_lib::ByteSeq;
use rand::{thread_rng, Rng};

use crate::{
    app_data, app_data_bytes, server_accept, server_read, server_read_handshake, server_write,
    Algorithms, Bytes, Server, ServerDB, PARSE_FAILED,
};

use super::{read_record, BertieError, BertieStream, TlsStream, DEFAULT_CIPHERSUITE};

// TODO: update with support for multiple ciphersuites.
const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    NamedGroup::X25519,
    false,
    false,
);

const default_algs: Algorithms = SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519;

// TODO: read from file.
// Cert and Key
const ECDSA_P256_SHA256_CERT: [u8; 522] = [
    0x30, 0x82, 0x02, 0x06, 0x30, 0x82, 0x01, 0xAC, 0x02, 0x09, 0x00, 0xD1, 0xA2, 0xE4, 0xD5, 0x78,
    0x05, 0x08, 0x61, 0x30, 0x0A, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x02, 0x30,
    0x81, 0x8A, 0x31, 0x0B, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x44, 0x45, 0x31,
    0x0F, 0x30, 0x0D, 0x06, 0x03, 0x55, 0x04, 0x08, 0x0C, 0x06, 0x42, 0x65, 0x72, 0x6C, 0x69, 0x6E,
    0x31, 0x0F, 0x30, 0x0D, 0x06, 0x03, 0x55, 0x04, 0x07, 0x0C, 0x06, 0x42, 0x65, 0x72, 0x6C, 0x69,
    0x6E, 0x31, 0x10, 0x30, 0x0E, 0x06, 0x03, 0x55, 0x04, 0x0A, 0x0C, 0x07, 0x68, 0x61, 0x63, 0x73,
    0x70, 0x65, 0x63, 0x31, 0x0F, 0x30, 0x0D, 0x06, 0x03, 0x55, 0x04, 0x0B, 0x0C, 0x06, 0x62, 0x65,
    0x72, 0x74, 0x69, 0x65, 0x31, 0x17, 0x30, 0x15, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0C, 0x0E, 0x62,
    0x65, 0x72, 0x74, 0x69, 0x65, 0x2E, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63, 0x31, 0x1D, 0x30,
    0x1B, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x09, 0x01, 0x16, 0x0E, 0x62, 0x65,
    0x72, 0x74, 0x69, 0x65, 0x40, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63, 0x30, 0x1E, 0x17, 0x0D,
    0x32, 0x31, 0x30, 0x34, 0x32, 0x39, 0x31, 0x31, 0x34, 0x37, 0x34, 0x35, 0x5A, 0x17, 0x0D, 0x33,
    0x31, 0x30, 0x34, 0x32, 0x37, 0x31, 0x31, 0x34, 0x37, 0x34, 0x35, 0x5A, 0x30, 0x81, 0x8A, 0x31,
    0x0B, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x44, 0x45, 0x31, 0x0F, 0x30, 0x0D,
    0x06, 0x03, 0x55, 0x04, 0x08, 0x0C, 0x06, 0x42, 0x65, 0x72, 0x6C, 0x69, 0x6E, 0x31, 0x0F, 0x30,
    0x0D, 0x06, 0x03, 0x55, 0x04, 0x07, 0x0C, 0x06, 0x42, 0x65, 0x72, 0x6C, 0x69, 0x6E, 0x31, 0x10,
    0x30, 0x0E, 0x06, 0x03, 0x55, 0x04, 0x0A, 0x0C, 0x07, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63,
    0x31, 0x0F, 0x30, 0x0D, 0x06, 0x03, 0x55, 0x04, 0x0B, 0x0C, 0x06, 0x62, 0x65, 0x72, 0x74, 0x69,
    0x65, 0x31, 0x17, 0x30, 0x15, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0C, 0x0E, 0x62, 0x65, 0x72, 0x74,
    0x69, 0x65, 0x2E, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63, 0x31, 0x1D, 0x30, 0x1B, 0x06, 0x09,
    0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x09, 0x01, 0x16, 0x0E, 0x62, 0x65, 0x72, 0x74, 0x69,
    0x65, 0x40, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63, 0x30, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2A,
    0x86, 0x48, 0xCE, 0x3D, 0x02, 0x01, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x03, 0x01, 0x07,
    0x03, 0x42, 0x00, 0x04, 0xD8, 0xE0, 0x74, 0xF7, 0xCB, 0xEF, 0x19, 0xC7, 0x56, 0xA4, 0x52, 0x59,
    0x0C, 0x02, 0x70, 0xCC, 0x9B, 0xFC, 0x45, 0x8D, 0x73, 0x28, 0x39, 0x1D, 0x3B, 0xF5, 0x26, 0x17,
    0x8B, 0x0D, 0x25, 0x04, 0x91, 0xE8, 0xC8, 0x72, 0x22, 0x59, 0x9A, 0x2C, 0xBB, 0x26, 0x31, 0xB1,
    0xCC, 0x6B, 0x6F, 0x5A, 0x10, 0xD9, 0x7D, 0xD7, 0x86, 0x56, 0xFB, 0x89, 0x39, 0x9E, 0x0A, 0x91,
    0x9F, 0x35, 0x81, 0xE7, 0x30, 0x0A, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x02,
    0x03, 0x48, 0x00, 0x30, 0x45, 0x02, 0x21, 0x00, 0xA1, 0x81, 0xB3, 0xD6, 0x8C, 0x9F, 0x62, 0x66,
    0xC6, 0xB7, 0x3F, 0x26, 0xE7, 0xFD, 0x88, 0xF9, 0x4B, 0xD8, 0x15, 0xD1, 0x45, 0xC7, 0x66, 0x69,
    0x40, 0xC2, 0x55, 0x21, 0x84, 0x9F, 0xE6, 0x8C, 0x02, 0x20, 0x10, 0x7E, 0xEF, 0xF3, 0x1D, 0x58,
    0x32, 0x6E, 0xF7, 0xCB, 0x0A, 0x47, 0xF2, 0xBA, 0xEB, 0xBC, 0xB7, 0x8F, 0x46, 0x56, 0xF1, 0x5B,
    0xCC, 0x2E, 0xD5, 0xB3, 0xC4, 0x0F, 0x5B, 0x22, 0xBD, 0x02,
];
const ECDSA_P256_SHA256_Key: [u8; 32] = [
    0xA6, 0xDE, 0x48, 0x21, 0x0E, 0x56, 0x12, 0xDD, 0x95, 0x3A, 0x91, 0x4E, 0x9F, 0x56, 0xC3, 0xA2,
    0xDB, 0x7A, 0x36, 0x20, 0x08, 0xE9, 0x52, 0xEE, 0xDB, 0xCE, 0xAC, 0x3B, 0x26, 0xF9, 0x20, 0xBD,
];

pub struct ServerState {
    sstate: Option<Server>,
    stream: TcpStream,
    db: ServerDB,
    read_buffer: Vec<u8>,
}

impl TlsStream for ServerState {
    fn write_tls(&mut self, bytes: &[u8]) -> Result<(), super::BertieError> {
        let sstate = match self.sstate.take() {
            Some(state) => state,
            None => return Err(BertieError::InvalidState),
        };

        let request = ByteSeq::from_public_slice(bytes);

        let (wire_bytes, new_state) = server_write(app_data(request), sstate)?;
        self.sstate = Some(new_state);

        // Write out the request
        self.stream
            .write_all(&wire_bytes.into_native())
            .map_err(|e| e.into())
    }

    fn read_tls(&mut self) -> Result<Vec<u8>, super::BertieError> {
        let mut sstate = match self.sstate.take() {
            Some(state) => state,
            None => return Err(BertieError::InvalidState),
        };

        let application_data = loop {
            let record = read_record(&mut self.read_buffer, &mut self.stream)?;
            let ad;
            (ad, sstate) = server_read(&record, sstate)?;
            match ad {
                Some(application_data) => break application_data,
                None => continue,
            }
        };
        let app_data = app_data_bytes(application_data);
        self.sstate = Some(sstate);
        Ok(app_data.into_native())
    }

    fn stream_mut(&mut self) -> &mut TcpStream {
        &mut self.stream
    }
}

impl BertieStream<ServerState> {
    /// Start a new server TLS connection.
    /// The [`TcpStream`] has to be connected before starting the server.
    ///
    /// A common pattern for the server would look as follows.
    /// ```
    /// use std::{net::{TcpStream, TcpListener}, thread};
    /// use bertie::stream::BertieStream;
    ///
    /// let host = "localhost";
    /// let port = 3443;
    ///
    /// // Run a client
    /// eprintln!("[Client] Starting ...");
    /// let client_handle = thread::spawn(move || {
    ///     let mut stream = BertieStream::client(host, port).expect("Error connecting to server");
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
    /// let mut server =
    ///     BertieStream::server(host, port, server_tcp_stream).expect("Error starting server");
    /// server.connect().unwrap();
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
    pub fn server(host: &str, port: u16, stream: TcpStream) -> Result<Self, BertieError> {
        let db = {
            let sni = ByteSeq::from_public_slice(host.as_bytes());

            ServerDB(
                sni,
                Bytes::from_public_slice(&ECDSA_P256_SHA256_CERT),
                SignatureKey::from_public_slice(&ECDSA_P256_SHA256_Key),
                None,
            )
        };

        Ok(Self {
            state: ServerState {
                db,
                stream,
                read_buffer: vec![],
                sstate: None,
            },
            host: host.to_string(),
            port,
            ciphersuites: vec![default_algs],
        })
    }

    /// Connect the incoming TLS stream.
    /// This function blocks until it was able to read the TLS client hello.
    pub fn connect(&mut self) -> Result<(), BertieError> {
        let entropy = {
            let mut entropy = [0u8; 64];
            // TODO: better randomness.
            thread_rng().fill(&mut entropy);
            Entropy::from_public_slice(&entropy)
        };
        let client_hello = read_record(&mut self.state.read_buffer, &mut self.state.stream)?;

        match server_accept(
            DEFAULT_CIPHERSUITE,
            self.state.db.clone(),
            &client_hello,
            entropy,
        ) {
            Err(x) => {
                println!("ServerInit Error {}", x);
                match x {
                    136 => {
                        self.write_all(&[21, 03, 03, 00, 02, 2, 47])?;
                    }
                    137 => {
                        self.write_all(&[21, 03, 03, 00, 02, 2, 70])?;
                    }
                    139 => {
                        // alerts here are optional
                        eprintln!("Hello message was missing a key share.");
                    }
                    _ => unimplemented!("unknown error {}", x),
                }
                return Err(x.into());
            }
            Ok((sh, sf, server_state)) => {
                self.write_all(&sh.into_native())?;
                let ccs_rec = ByteSeq::from_hex("140303000101");
                self.write_all(&ccs_rec.into_native())?;
                self.write_all(&sf.into_native())?;

                let ccs = read_record(&mut self.state.read_buffer, &mut self.state.stream)?;
                self.check_ccs_message(ccs.declassify().native_slice())?;

                let cf_rec = read_record(&mut self.state.read_buffer, &mut self.state.stream)?;
                let sstate = server_read_handshake(&cf_rec, server_state)?;

                self.state.sstate = Some(sstate);
            }
        }

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
}

#[cfg(test)]
mod tests {
    use std::{net::TcpListener, thread};

    use super::*;

    #[test]
    fn server() {
        eprintln!("[Test] Starting ...");

        let host = "localhost";
        let port = 3443;

        // Run a client
        eprintln!("[Client] Starting ...");
        let client_handle = thread::spawn(move || {
            let mut stream = BertieStream::client(host, port).expect("Error connecting to server");
            stream.write(b"Hello, I'm the Bertie test client.").unwrap();
            let server_msg = stream.read().unwrap();
            assert_eq!(
                &b"Greetings, I'm the Bertie test server.\nBy."[..],
                &server_msg[..]
            );
        });

        // Listen on and open TCP connection
        let listener = TcpListener::bind((host, port)).unwrap();
        let (server_tcp_stream, _adr) = listener.accept().unwrap();

        // Server is waiting for the incoming TLS handshake.
        let mut server =
            BertieStream::server(host, port, server_tcp_stream).expect("Error starting server");
        server.connect().unwrap();

        // Handshake finished.

        // Read client application messages.
        let client_msg = server.read().unwrap();
        eprintln!("Client says: {}", String::from_utf8_lossy(&client_msg));
        assert_eq!(&b"Hello, I'm the Bertie test client."[..], &client_msg[..]);
        server
            .write(b"Greetings, I'm the Bertie test server.\nBy.")
            .unwrap();

        // Close the client's thread.
        client_handle.join().unwrap();
    }
}
