use std::{
    fs::File,
    io::{BufReader, Read, Write},
    net::TcpStream,
};

#[cfg(feature = "evercrypt")]
use evercrypt_cryptolib::*;
#[cfg(not(feature = "evercrypt"))]
use hacspec_cryptolib::*;
use hacspec_lib::ByteSeq;
use rand::{thread_rng, Rng};

use crate::{
    app_data, app_data_bytes, server_accept, server_read, server_read_handshake, server_write,
    Bytes, Server, ServerDB, PARSE_FAILED,
};

use super::{read_record, BertieError, BertieStream, TlsStream, DEFAULT_CIPHERSUITE};

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
    /// let mut server = BertieStream::server(
    ///     host,
    ///     port,
    ///     server_tcp_stream,
    ///     "tests/assets/p256_cert.der",
    ///     "tests/assets/p256_key.der",
    /// )
    /// .expect("Error starting server");
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
    pub fn server(
        host: &str,
        port: u16,
        stream: TcpStream,
        cert_file: &str,
        key_file: &str,
    ) -> Result<Self, BertieError> {
        let db = {
            let sni = ByteSeq::from_public_slice(host.as_bytes());

            // Parse the DER encoded signature key.
            // FIXME: Only EC for now.
            let signature_key = Self::read_file(key_file)?;
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
            if raw_key.is_empty() {
                // We weren't able to read the key.
                return Err(BertieError::TLS(255)); // TODO: error code
            }

            ServerDB(
                sni,
                Bytes::from_public_slice(&Self::read_file(cert_file)?),
                SignatureKey::from_public_slice(&raw_key),
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
            ciphersuites: vec![DEFAULT_CIPHERSUITE],
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

    /// Read a binary file, e.g. key or certificate.
    fn read_file(file_name: &str) -> Result<Vec<u8>, BertieError> {
        let f = File::open(file_name)?;
        let mut reader = BufReader::new(f);
        let mut buffer = Vec::new();
        reader.read_to_end(&mut buffer)?;

        Ok(buffer)
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
        let mut server = BertieStream::server(
            host,
            port,
            server_tcp_stream,
            "tests/assets/p256_cert.der",
            "tests/assets/p256_key.der",
        )
        .expect("Error starting server");
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
