//! # TLS 1.3 Server
//!
//! This module implements a simple TLS 1.3 server database to handle the server
//! * name
//! * certificate
//! * private signature key
//! * optional PSKs

use crate::{
    tls13crypto::{Algorithms, Psk, PublicVerificationKey, SignatureKey},
    tls13utils::{check_eq, eq, parse_failed, Bytes, TLSError, PSK_MODE_MISMATCH},
};

/// The Server Database
#[derive(Debug, Clone, Default)]
pub struct ServerDB {
    pub(crate) server_name: Bytes,
    pub(crate) cert: Bytes,
    pub(crate) sk: SignatureKey,
    pub(crate) psk_opt: Option<(Bytes, Psk)>,
}

impl ServerDB {
    /// Create a new server database.
    ///
    /// Note that this only holds one value at a time right now. #51
    pub fn new(
        server_name: Bytes,
        cert: Bytes,
        sk: SignatureKey,
        psk_opt: Option<(Bytes, Psk)>,
    ) -> Self {
        Self {
            server_name,
            cert,
            sk,
            psk_opt,
        }
    }
}

/// Global server information.
pub(crate) struct ServerInfo {
    pub(crate) cert: Bytes,
    pub(crate) sk: SignatureKey,
    pub(crate) psk_opt: Option<Psk>,
}

pub(crate) struct ServerPubInfo {
    pub(crate) server_name: Bytes,
    pub(crate) certificate: Option<Bytes>,
    pub(crate) public_key: Option<PublicVerificationKey>,
    pub(crate) session_ticket: Option<Bytes>,
}

/// Look up a server for the given `ciphersuite`.
///
/// The function returns a server with the first algorithm it finds.
pub(crate) fn lookup_db(
    ciphersuite: Algorithms,
    db: &ServerDB,
    sni: &Bytes,
    tkt: &Option<Bytes>,
) -> Result<ServerInfo, TLSError> {
    if eq(sni, &Bytes::new()) || eq(sni, &db.server_name) {
        match (ciphersuite.psk_mode(), tkt, &db.psk_opt) {
            (true, Some(ctkt), Some((stkt, psk))) => {
                check_eq(ctkt, stkt)?;
                let server = ServerInfo {
                    cert: db.cert.clone(),
                    sk: db.sk.clone(),
                    psk_opt: Some(psk.clone()),
                };
                Ok(server)
            }
            (false, _, _) => {
                let server = ServerInfo {
                    cert: db.cert.clone(),
                    sk: db.sk.clone(),
                    psk_opt: None,
                };
                Ok(server)
            }
            _ => Err(PSK_MODE_MISMATCH),
        }
    } else {
        Err(parse_failed())
    }
}
