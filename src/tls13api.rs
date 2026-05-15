//! # Public TLS 1.3 API
//!
//! This is the entry point for consumers of Bertie.
//! It defines the public API that users of Bertie use to establish TLS connections.
//!
//! Each handshake/record method takes a `&impl BertieCrypto` (the cryptographic
//! provider) and an `&mut impl CryptoRng` (for randomness-consuming steps).
//! The default in-tree provider is [`crate::crypto_provider::LibcruxBertieProvider`];
//! a tracing wrapper lives in the `bertie-trace-adapter` sibling crate.

use rand::CryptoRng;

use crate::{
    crypto_provider::BertieCrypto,
    server::{ServerDB, ServerPubInfo},
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
pub fn in_psk_mode(c: &Client) -> bool {
    match c {
        Client::Client0(cstate, _) => algs_post_client_hello(cstate).psk_mode(),
        Client::ClientH(cstate, _, _, _) => algs_post_server_hello(cstate).psk_mode(),
        Client::Client1(cstate, _) => algs_post_client_finished(cstate).psk_mode(),
    }
}

/// Retrieves the Server's public information.
pub fn get_server_info(c: &Client) -> ServerPubInfo {
    match c {
        Client::Client0(cstate, _) => server_info_post_client_hello(cstate),
        Client::ClientH(cstate, _, _, _) => server_info_post_server_hello(cstate),
        Client::Client1(cstate, _) => server_info_post_client_finished(cstate),
    }
}

impl Client {
    /// Start a TLS handshake as client.
    pub fn connect<C: BertieCrypto, R: CryptoRng>(
        crypto: &C,
        ciphersuite: Algorithms,
        server_name: &Bytes,
        session_ticket: Option<Bytes>,
        psk: Option<Key>,
        rng: &mut R,
        ks: &mut TLSkeyscheduler,
    ) -> Result<(Bytes, Self), TLSError> {
        let (client_hello, cipherstate0, client_state) =
            client_init(crypto, ciphersuite, server_name, session_ticket, psk, rng, ks)?;
        // Legacy version 0x0301 for the initial ClientHello (TLS 1.0
        // middlebox compat); 0x0303 for every subsequent record.
        let client_hello_record = handshake_record(client_hello, 0x01)?;
        Ok((
            client_hello_record,
            Client::Client0(client_state, cipherstate0),
        ))
    }

    /// Read the next handshake Message.
    pub fn read_handshake<C: BertieCrypto>(
        self,
        crypto: &C,
        handshake_bytes: &Bytes,
        ks: &mut TLSkeyscheduler,
    ) -> Result<(Option<Bytes>, Self), TLSError> {
        match self {
            Client::Client0(state, cipher_state) => {
                let sf = get_handshake_record(handshake_bytes)?;
                let (cipher1, cstate) = client_set_params(crypto, &sf, state, ks)?;
                let buf = handshake_data::HandshakeData::from(Bytes::new());
                Ok((None, Client::ClientH(cstate, cipher_state, cipher1, buf)))
            }
            Client::ClientH(cstate, cipher0, cipher_hs, buf) => {
                let (hd, cipher_hs) = decrypt_handshake(crypto, handshake_bytes, cipher_hs)?;
                let buf = buf.concat(&hd);
                if buf.find_handshake_message(HandshakeType::Finished, 0) {
                    let (cfin, cipher1, cstate) = client_finish(crypto, &buf, cstate, ks)?;
                    let (cf_rec, _cipher_hs) = encrypt_handshake(crypto, cfin, 0, cipher_hs)?;
                    Ok((Some(cf_rec), Client::Client1(cstate, cipher1)))
                } else {
                    Ok((None, Client::ClientH(cstate, cipher0, cipher_hs, buf)))
                }
            }
            _ => Err(INCORRECT_STATE),
        }
    }

    /// Read application data and session tickets.
    pub fn read<C: BertieCrypto>(
        self,
        crypto: &C,
        message_bytes: &Bytes,
    ) -> Result<(Option<AppData>, Self), TLSError> {
        match self {
            Client::Client1(state, cipher1) => {
                let (ty, hd, cipher1) = decrypt_data_or_hs(crypto, message_bytes, cipher1)?;
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
    pub fn write<C: BertieCrypto>(
        self,
        crypto: &C,
        application_data: AppData,
    ) -> Result<(Bytes, Client), TLSError> {
        match self {
            Client::Client1(cstate, cipher1) => {
                let (by, cipher1) = encrypt_data(crypto, application_data, 0, cipher1)?;
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
    #[requires(client_hello.len() >= 5)]
    pub fn accept<C: BertieCrypto, R: CryptoRng>(
        crypto: &C,
        ciphersuite: Algorithms,
        db: ServerDB,
        client_hello: &Bytes,
        rng: &mut R,
        ks: &mut TLSkeyscheduler,
    ) -> Result<(Bytes, Bytes, Self), TLSError> {
        // The wire bytes carry the legacy 0x0301 ClientHello version; the
        // parser expects 0x0303. Mutate a clone (don't touch the wire bytes
        // — `network_source` on the adapter side relies on their stable
        // fingerprint to resolve to the client's installed term).
        let mut ch_rec = client_hello.clone();
        ch_rec[2] = U8(0x03);
        let ch = get_handshake_record(&ch_rec)?;
        let (server_hello, server_finished, cipher0, cipher_hs, cipher1, sstate) =
            server_init(crypto, ciphersuite, &ch, db, rng, ks)?;
        let sh_rec = handshake_record(server_hello, 0x03)?;
        let (sf_rec, cipher_hs) = encrypt_handshake(crypto, server_finished, 0, cipher_hs)?;
        Ok((
            sh_rec,
            sf_rec,
            Server::ServerH(sstate, cipher0, cipher_hs, cipher1),
        ))
    }

    /// Read the next handshake Message.
    pub fn read_handshake<C: BertieCrypto>(
        self,
        crypto: &C,
        handshake_bytes: &Bytes,
        ks: &mut TLSkeyscheduler,
    ) -> Result<Self, TLSError> {
        match self {
            Server::ServerH(sstate, _cipher0, cipher_hs, cipher1) => {
                let (cf, _cipher_hs) = decrypt_handshake(crypto, handshake_bytes, cipher_hs)?;
                let sstate = server_finish(crypto, &cf, sstate, ks)?;
                Ok(Server::Server1(sstate, cipher1))
            }
            _ => Err(INCORRECT_STATE),
        }
    }

    /// Send application data to the client.
    pub fn write<C: BertieCrypto>(
        self,
        crypto: &C,
        application_data: AppData,
    ) -> Result<(Bytes, Self), TLSError> {
        match self {
            Server::Server1(sstate, cipher1) => {
                let (by, cipher1) = encrypt_data(crypto, application_data, 0, cipher1)?;
                Ok((by, Server::Server1(sstate, cipher1)))
            }
            _ => Err(INCORRECT_STATE),
        }
    }

    /// Read application data.
    pub fn read<C: BertieCrypto>(
        self,
        crypto: &C,
        application_data: &Bytes,
    ) -> Result<(Option<AppData>, Self), TLSError> {
        match self {
            Server::Server1(sstate, cipher1) => {
                let (ad, cipher1) = decrypt_data(crypto, application_data, cipher1)?;
                Ok((Some(ad), Server::Server1(sstate, cipher1)))
            }
            _ => Err(INCORRECT_STATE),
        }
    }
}
