//! # Public TLS 1.3 API
//!
//! This is the entry point for consumers of Bertie.
//! It defines the public API that users of Bertie use to establish TLS connections.
//!
//! **NOTE:** This is a low level TLS API that needs careful handling.
//!           We will add a more usable API on top in future. But the verifiable
//!           core of the protocol starts here.

use rand::CryptoRng;

use crate::{
    server::ServerDB,
    tls13crypto::*,
    tls13formats::{handshake_data::HandshakeType, *},
    tls13handshake::*,
    tls13keyscheduler::key_schedule::*,
    tls13record::*,
    tls13utils::*,
};

/// The TLS Client state.
pub enum Client {
    /// The initial client handshake state.
    Client0(ClientPostClientHello, Option<ClientCipherState0>),

    /// The client handshake state after receiving the server hello message.
    ClientH(
        ClientPostServerHello,
        Option<ClientCipherState0>,
        DuplexCipherStateH,
        handshake_data::HandshakeData,
    ),

    /// The client handshake state after finishing the handshake.
    Client1(ClientPostClientFinished, DuplexCipherState1),
}

/// Check if the client is using a PSK mode or not.
///
/// Returns `true` if the client is in PSK mode and `false` otherwise.
pub fn in_psk_mode(c: &Client) -> bool {
    match c {
        Client::Client0(cstate, _) => algs_post_client_hello(cstate).psk_mode(),
        Client::ClientH(cstate, _, _, _) => algs_post_server_hello(cstate).psk_mode(),
        Client::Client1(cstate, _) => algs_post_client_finished(cstate).psk_mode(),
    }
}

impl Client {
    /// Start a TLS handshake as client.
    /// Note that Bertie clients only support a single ciphersuite at a time and
    /// do not perform ciphersuite negotiation.
    ///
    /// This function takes the
    /// * `ciphersuite` to use for this client
    /// * `server_name` for the server to connect to
    /// * `session_ticket` for an optional session ticket
    /// * `psk` for an optional pre-shared-key
    /// * `entropy` for the randomness required in the handshake
    ///
    /// The function returns a [`Result`].
    /// When successful, the function returns a tuple with the first element the
    /// client hello record as bytes, and the [`Client`] state as the second element.
    /// If an error occurs, it returns a [`TLSError`].
    pub fn connect(
        ciphersuite: Algorithms,
        server_name: &Bytes,
        session_ticket: Option<Bytes>,
        psk: Option<Key>,
        rng: &mut impl CryptoRng,
        ks: &mut TLSkeyscheduler,
    ) -> Result<(Bytes, Self), TLSError> {
        let (client_hello, cipherstate0, client_state) =
            client_init(ciphersuite, server_name, session_ticket, psk, rng, ks)?;
        let mut client_hello_record = handshake_record(client_hello)?;
        client_hello_record[2] = U8(0x01);
        Ok((
            client_hello_record,
            Client::Client0(client_state, cipherstate0),
        ))
    }

    // This function reads handshake records and decrypts them using the TLS 1.3 record protocol
    // A slightly modified version would work for QUIC
    /// Read the next handshake Message.
    ///
    /// This function takes the current state and `handshake_bytes` and returns
    /// the next state or a [`TLSError`].
    ///
    /// The function returns a [`Result`].
    /// When successful, the function returns a tuple with the first element the
    /// next client handshake message as bytes option, and the next [`Client`] state as
    /// the second element.
    /// If there's no handshake message, the first element is [`None`].
    /// If an error occurs, it returns a [`TLSError`].
    pub fn read_handshake(
        self,
        handshake_bytes: &Bytes,
        ks: &mut TLSkeyscheduler,
    ) -> Result<(Option<Bytes>, Self), TLSError> {
        match self {
            Client::Client0(state, cipher_state) => {
                let sf = get_handshake_record(handshake_bytes)?;
                let (cipher1, cstate) = client_set_params(&sf, state, ks)?;
                let buf = handshake_data::HandshakeData::from(Bytes::new());
                Ok((None, Client::ClientH(cstate, cipher_state, cipher1, buf)))
            }
            Client::ClientH(cstate, cipher0, cipher_hs, buf) => {
                let (hd, cipher_hs) = decrypt_handshake(handshake_bytes, cipher_hs)?;
                let buf = buf.concat(&hd);
                if buf.find_handshake_message(HandshakeType::Finished, 0) {
                    let (cfin, cipher1, cstate) = client_finish(&buf, cstate, ks)?;
                    let (cf_rec, _cipher_hs) = encrypt_handshake(cfin, 0, cipher_hs)?;
                    Ok((Some(cf_rec), Client::Client1(cstate, cipher1)))
                } else {
                    Ok((None, Client::ClientH(cstate, cipher0, cipher_hs, buf)))
                }
            }
            _ => Err(INCORRECT_STATE),
        }
    }

    /// Read application data and session tickets.
    ///
    /// This function can be used when the TLS handshake is complete, to read
    /// application data and session tickets from the server.
    ///
    /// It takes the current state and `message_bytes` and returns
    /// the next state or a [`TLSError`].
    ///
    /// The function returns a [`Result`].
    /// When successful, the function returns a tuple with the first element the
    /// application data as bytes option, and the new [`Client`] state as the second element.
    /// If there's no application data, the first element is [`None`].
    /// If an error occurs, it returns a [`TLSError`].
    pub fn read(self, message_bytes: &Bytes) -> Result<(Option<AppData>, Self), TLSError> {
        match self {
            Client::Client1(state, cipher1) => {
                let (ty, hd, cipher1) = decrypt_data_or_hs(message_bytes, cipher1)?;
                match ty {
                    ContentType::ApplicationData => {
                        Ok((Some(AppData::new(hd)), Client::Client1(state, cipher1)))
                    }
                    ContentType::Handshake => Ok((None, Client::Client1(state, cipher1))),
                    _ => Err(PARSE_FAILED),
                }
            }
            _ => Err(INCORRECT_STATE),
        }
    }

    /// Send application data to the server.
    ///
    /// The function returns a [`Result`].
    /// When successful, the function returns a tuple with the first element the
    /// encrypted `application_data` as bytes, and the new [`Client`] state as the second element.
    /// If an error occurs, it returns a [`TLSError`].
    pub fn write(self, application_data: AppData) -> Result<(Bytes, Client), TLSError> {
        match self {
            Client::Client1(cstate, cipher1) => {
                let (by, cipher1) = encrypt_data(application_data, 0, cipher1)?;
                Ok((by, Client::Client1(cstate, cipher1)))
            }
            _ => Err(INCORRECT_STATE),
        }
    }
}

/// The TLS server state.
pub enum Server {
    /// The initial server state. The server accepts a new connection in this state.
    ServerH(
        ServerPostServerFinished,
        Option<ServerCipherState0>,
        DuplexCipherStateH,
        DuplexCipherState1,
    ),

    /// The final server state. The server communicates via the encrypted TLS
    /// channel in this state.
    Server1(ServerPostClientFinished, DuplexCipherState1),
}

#[hax_lib::attributes]
impl Server {
    /// Start a new TLS handshake as server.
    /// Note that Bertie servers only support a single ciphersuite at a time and
    /// do not perform ciphersuite negotiation.
    ///
    /// This function takes the
    /// * `ciphersuite` to use for this server
    /// * `db` for the server database containing certificates and keys
    /// * `client_hello` for the initial client hello message
    /// * `entropy` for the randomness required in the handshake
    ///
    /// The function returns a [`Result`].
    /// When successful, the function returns a three-tuple with the first element the
    /// server hello record as bytes, the second the server finished record as bytes,
    /// and the new [`Server`] state as the third element.
    /// If an error occurs, it returns a [`TLSError`].
    #[requires(client_hello.len() >= 5)]
    pub fn accept(
        ciphersuite: Algorithms,
        db: ServerDB,
        client_hello: &Bytes,
        rng: &mut impl CryptoRng,
        ks: &mut TLSkeyscheduler,
    ) -> Result<(Bytes, Bytes, Self), TLSError> {
        let mut ch_rec = client_hello.clone();
        ch_rec[2] = U8(0x03);
        let ch = get_handshake_record(&ch_rec)?;
        let (server_hello, server_finished, cipher0, cipher_hs, cipher1, sstate) =
            server_init(ciphersuite, &ch, db, rng, ks)?;
        let sh_rec = handshake_record(server_hello)?;
        let (sf_rec, cipher_hs) = encrypt_handshake(server_finished, 0, cipher_hs)?;
        Ok((
            sh_rec,
            sf_rec,
            Server::ServerH(sstate, cipher0, cipher_hs, cipher1),
        ))
    }

    /// Read the next handshake Message.
    ///
    /// This function takes the current state and `handshake_bytes` and returns
    /// the next state or a [`TLSError`].
    ///
    /// The function returns a [`Result`].
    /// When successful, the function returns the next [`Server`] state.
    /// If an error occurs, it returns a [`TLSError`].
    pub fn read_handshake(
        self,
        handshake_bytes: &Bytes,
        ks: &mut TLSkeyscheduler,
    ) -> Result<Self, TLSError> {
        match self {
            Server::ServerH(sstate, _cipher0, cipher_hs, cipher1) => {
                let (cf, _cipher_hs) = decrypt_handshake(handshake_bytes, cipher_hs)?;
                let sstate = server_finish(&cf, sstate, ks)?;
                Ok(Server::Server1(sstate, cipher1))
            }
            _ => Err(INCORRECT_STATE),
        }
    }

    /// Send application data to the client.
    ///
    /// The function returns a [`Result`].
    /// When successful, the function returns a tuple with the first element the
    /// encrypted `application_data` as bytes, and the new [`Server`] state as the second element.
    /// If an error occurs, it returns a [`TLSError`].
    pub fn write(self, application_data: AppData) -> Result<(Bytes, Self), TLSError> {
        match self {
            Server::Server1(sstate, cipher1) => {
                let (by, cipher1) = encrypt_data(application_data, 0, cipher1)?;
                Ok((by, Server::Server1(sstate, cipher1)))
            }
            _ => Err(INCORRECT_STATE),
        }
    }

    /// Read application data.
    ///
    /// This function can be used when the TLS handshake is complete, to read
    /// application data from the client.
    ///
    /// It takes the current state and `application_data` and returns
    /// the next state or a [`TLSError`].
    ///
    /// The function returns a [`Result`].
    /// When successful, the function returns a tuple with the first element the
    /// application data as bytes option, and the new [`Server`] state as the second element.
    /// If there's no application data, the first element is [`None`].
    /// If an error occurs, it returns a [`TLSError`].
    pub fn read(self, application_data: &Bytes) -> Result<(Option<AppData>, Self), TLSError> {
        match self {
            Server::Server1(sstate, cipher1) => {
                let (ad, cipher1) = decrypt_data(application_data, cipher1)?;
                Ok((Some(ad), Server::Server1(sstate, cipher1)))
            }
            _ => Err(INCORRECT_STATE),
        }
    }
}
