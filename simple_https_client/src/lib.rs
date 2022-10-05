//! # Simple TLS 1.3 HTTP Client Implementation
//!
//! It connects to a given host:port, sends an HTTP "GET /", and prints a prefix of the HTTP response.
//!
//! WARNING: This code is not in hacspec since it need to use TCP etc.

#![allow(non_upper_case_globals)]

use std::io::{Read, Write};

use anyhow::Result;
use bertie::{tls13api::*, tls13utils::*};
#[cfg(feature = "evercrypt")]
use evercrypt_cryptolib::*;
#[cfg(not(feature = "evercrypt"))]
use hacspec_cryptolib::*;
use hacspec_lib::*;
use rand::*;
use record::{AppError, RecordStream};
use tracing::info;

#[allow(dead_code)]
const SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    NamedGroup::X25519,
    false,
    false,
);

const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    NamedGroup::X25519,
    false,
    false,
);

const SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::RsaPssRsaSha256,
    NamedGroup::X25519,
    false,
    false,
);

const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    NamedGroup::Secp256r1,
    false,
    false,
);

const SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::RsaPssRsaSha256,
    NamedGroup::Secp256r1,
    false,
    false,
);

const SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    NamedGroup::Secp256r1,
    false,
    false,
);

pub fn ciphersuites() -> Vec<Algorithms> {
    vec![
        SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256,
        SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256,
        SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519,
        SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519,
        SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256,
        SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519,
    ]
}

#[tracing::instrument(skip(stream, request))]
pub fn tls13client<Stream>(
    host: &str,
    stream: Stream,
    algorithms: impl Into<Option<Algorithms>> + Debug,
    request: &str,
) -> Result<(RecordStream<Stream>, Client, Vec<u8>), AppError>
where
    Stream: Read + Write,
{
    let algorithms = match algorithms.into() {
        Some(a) => a,
        None => SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519,
    };
    // Create a stream that is framed by TLS records.
    let mut stream = RecordStream::new(stream);

    // # Execute the TLS 1.3 handshake.

    // Initialize TLS 1.3 client.
    let (client_hello, cstate) = {
        let sni = ByteSeq::from_public_slice(host.as_bytes());
        let ent = {
            let mut entropy = [0u8; 64];
            thread_rng().fill(&mut entropy);
            Entropy::from_public_slice(&entropy)
        };

        client_connect(algorithms, &sni, None, None, ent)?
    };

    stream.write_record(client_hello)?;

    let server_hello = stream.read_record()?;

    // TODO: Who should do this check?
    if eq1(server_hello[0], U8(21)) {
        // Alert
        eprintln!(
            "Server does not support proposed algorithms. {:?}",
            algorithms
        );
        return Err(UNSUPPORTED_ALGORITHM.into());
    }

    let cstate = match client_read_handshake(&server_hello, cstate) {
        Ok((_, cstate)) => cstate,
        Err(e) => {
            match e {
                6 => eprintln!("Server does not support proposed algorithms."),
                137 => eprintln!("Wrong TLS protocol version TLS({:?})", e),
                138 => eprintln!("Server sent application data instead of a handshake message."),
                139 => eprintln!("Hello message was missing a key share."),
                _ => eprintln!("Bertie client error {}", e),
            }
            return Err(e.into());
        }
    };

    let change_cipher_spec = stream.read_record()?;
    verify_ccs_message(change_cipher_spec)?;

    let mut cf_rec = None;
    let mut cstate = cstate;
    while cf_rec == None {
        let rec = stream.read_record()?;

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

    let change_cipher_spec = ByteSeq::from_hex("140303000101");
    stream.write_record(change_cipher_spec)?;

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

pub fn tls13client_continue<Stream>(
    mut stream: RecordStream<Stream>,
    cstate: Client,
) -> Result<(RecordStream<Stream>, Client, Vec<u8>), AppError>
where
    Stream: Read + Write,
{
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

pub(crate) fn verify_ccs_message(rec: ByteSeq) -> Result<(), AppError> {
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
