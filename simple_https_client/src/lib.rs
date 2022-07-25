//! # Simple TLS 1.3 HTTP Client Implementation
//!
//! It connects to a given host:port, sends an HTTP "GET /", and prints a prefix of the HTTP response.
//!
//! WARNING: This code is not in hacspec since it need to use TCP etc.

#![allow(non_upper_case_globals)]

use std::str;

use anyhow::Result;
use bertie::{tls13api::*, tls13utils::*};
#[cfg(feature = "evercrypt")]
use evercrypt_cryptolib::*;
#[cfg(not(feature = "evercrypt"))]
use hacspec_cryptolib::*;
use hacspec_lib::*;
use rand::*;
use thiserror::Error;
use tracing::{error, info};

use crate::frame::{FramedStream, FramedStreamError};

mod debug;
mod frame;

const SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    NamedGroup::X25519,
    false,
    false,
);

/*
const SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::RsaPssRsaSha256,
    NamedGroup::X25519,
    false,
    false,
);
*/

const default_algs: Algorithms = SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519;

#[derive(Error, Debug)]
pub enum ClientError {
    #[error("Stream error: {0:?}")]
    Stream(FramedStreamError),
    #[error("TLS error: {0:?}")]
    TLS(TLSError),
}

impl From<TLSError> for ClientError {
    fn from(error: TLSError) -> Self {
        ClientError::TLS(error)
    }
}

impl From<FramedStreamError> for ClientError {
    fn from(error: FramedStreamError) -> Self {
        ClientError::Stream(error)
    }
}

#[tracing::instrument(skip(request))]
pub fn tls13client(
    host: &str,
    port: u16,
    request: &str,
) -> Result<(FramedStream, Client, Vec<u8>), ClientError> {
    // # Demo of a simple HTTPS client.
    //
    // The client ...
    //   * connects to host:port via TCP,
    //   * executes a TLS 1.3 handshake,
    //   * sends an encrypted HTTP GET, and
    //   * prints a prefix of the servers HTTP response.

    // # Connect to host:port via TCP.

    // Create TCP stream.
    let mut stream = FramedStream::connect(host, port)?;

    // # Execute the TLS 1.3 handshake.

    // Initialize TLS 1.3 client.
    let (ch_rec, cstate) = {
        let ent = {
            let mut entropy = [0 as u8; 64];
            thread_rng().fill(&mut entropy);
            Entropy::from_public_slice(&entropy)
        };
        let sni = ByteSeq::from_public_slice(&host.as_bytes());

        client_connect(default_algs, &sni, None, None, ent)?
    };

    stream.write_record(ch_rec)?;

    // Process server response.
    let sh_rec = stream.read_record()?;

    if eq1(sh_rec[0], U8(21)) {
        // Alert
        error!("Server does not support proposed algorithms.");
        Err(UNSUPPORTED_ALGORITHM.into())
    } else {
        //println!("Got SH record: {}",sh_rec.len());

        let (_, cstate) = client_read_handshake(&sh_rec, cstate)?;

        //println!("Got SH");

        let rec_ccs = stream.read_record()?;
        verify_ccs_message(rec_ccs)?;

        //println!("Got SCCS");

        let mut cf_rec = None;
        let mut cstate = cstate;
        while cf_rec == None {
            let rec = stream.read_record()?;

            let (new_cf, new_cstate) = client_read_handshake(&rec, cstate)?;
            cf_rec = new_cf;
            cstate = new_cstate;
        }

        /* Complete Connection */

        let ccs_rec = ByteSeq::from_hex("140303000101");
        stream.write_record(ccs_rec)?;

        // Safety: Safe to unwrap().
        let cf_rec = cf_rec.unwrap();
        stream.write_record(cf_rec)?;

        info!("----- Handshake finished -----");

        /* Send HTTP GET  */

        let (ap, cstate) = {
            let http_get = ByteSeq::from_public_slice(request.as_bytes());

            client_write(app_data(http_get), cstate)?
        };

        stream.write_record(ap)?;

        /* Process HTTP response */

        let mut ad = None;
        let mut cstate = cstate;
        while ad == None {
            let rec = stream.read_record()?;

            let (new_ad, new_cstate) = client_read(&rec, cstate)?;
            ad = new_ad;
            cstate = new_cstate;
        }

        let response_prefix = {
            // Safety: Safe to unwrap().
            let body = app_data_bytes(ad.unwrap());

            // Safety: Safe to unwrap().
            // TODO: Provide `Bytes` -> `Vec<u8>` conversion?
            hex::decode(body.to_hex()).unwrap()
        };

        Ok((stream, cstate, response_prefix))
    }
}

pub fn tls13client_continue(
    mut stream: FramedStream,
    cstate: Client,
) -> Result<(FramedStream, Client, Vec<u8>), ClientError> {
    let mut ad = None;
    let mut cstate = cstate;
    while ad == None {
        let rec = stream.read_record()?;

        let (new_ad, new_cstate) = client_read(&rec, cstate)?;
        ad = new_ad;
        cstate = new_cstate;
    }

    let response_prefix = {
        // Safety: Safe to unwrap().
        let body = app_data_bytes(ad.unwrap());

        // Safety: Safe to unwrap().
        // TODO: Provide `Bytes` -> `Vec<u8>` conversion?
        hex::decode(body.to_hex()).unwrap()
    };

    Ok((stream, cstate, response_prefix))
}

pub(crate) fn verify_ccs_message(rec: ByteSeq) -> Result<(), ClientError> {
    let rec = rec.declassify();

    if rec.len() == 6
        && rec[0] == 0x14u8
        && rec[1] == 0x03u8
        && rec[2] == 0x03u8
        && rec[3] == 0x00u8
        && rec[4] == 0x01u8
        && rec[5] == 0x01u8
    {
        Ok(())
    } else {
        Err(PARSE_FAILED.into())
    }
}
