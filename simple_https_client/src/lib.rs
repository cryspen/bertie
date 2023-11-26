//! # Simple TLS 1.3 HTTP Client Implementation
//!
//! It connects to a given host:port, sends an HTTP "GET /", and prints a prefix of the HTTP response.
//!
//! WARNING: This code is not in hacspec since it need to use TCP etc.

#![allow(non_upper_case_globals)]

use anyhow::Result;
use bertie::{tls13api::*, tls13crypto::*, tls13utils::*};
use std::fmt::Debug;
use std::io::{Read, Write};

use rand::*;
use record::{AppError, RecordStream};
use tracing::info;

#[allow(dead_code)]
pub const SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::X25519,
    false,
    false,
);

pub const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::X25519,
    false,
    false,
);

pub const SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::X25519,
    false,
    false,
);

pub const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::Secp256r1,
    false,
    false,
);

pub const SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::Secp256r1,
    false,
    false,
);

pub const SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::Secp256r1,
    false,
    false,
);

pub const SHA256_Aes128Gcm_RsaPssRsaSha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::Secp256r1,
    false,
    false,
);

pub const SHA256_Aes128Gcm_RsaPssRsaSha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::X25519,
    false,
    false,
);

pub const SHA384_Aes256Gcm_RsaPssRsaSha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA384,
    AeadAlgorithm::Aes256Gcm,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::X25519,
    false,
    false,
);

pub const SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA384,
    AeadAlgorithm::Aes256Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::X25519,
    false,
    false,
);

pub const SHA384_Aes256Gcm_RsaPssRsaSha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA384,
    AeadAlgorithm::Aes256Gcm,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::Secp256r1,
    false,
    false,
);

pub const SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA384,
    AeadAlgorithm::Aes256Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::Secp256r1,
    false,
    false,
);

pub fn ciphersuite_from_str(s: &str) -> Result<Algorithms> {
    match s {
        "SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519" => {
            Ok(SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519)
        }
        "SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519" => {
            Ok(SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519)
        }
        "SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256" => {
            Ok(SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256)
        }
        "SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256" => {
            Ok(SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256)
        }
        "SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256" => {
            Ok(SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256)
        }
        "SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519" => {
            Ok(SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519)
        }
        "SHA256_Aes128Gcm_RsaPssRsaSha256_P256" => Ok(SHA256_Aes128Gcm_RsaPssRsaSha256_P256),
        "SHA256_Aes128Gcm_RsaPssRsaSha256_X25519" => Ok(SHA256_Aes128Gcm_RsaPssRsaSha256_X25519),
        "SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256" => {
            Ok(SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256)
        }
        "SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519" => {
            Ok(SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519)
        }
        "SHA384_Aes256Gcm_RsaPssRsaSha256_P256" => Ok(SHA384_Aes256Gcm_RsaPssRsaSha256_P256),
        "SHA384_Aes256Gcm_RsaPssRsaSha256_X25519" => Ok(SHA384_Aes256Gcm_RsaPssRsaSha256_X25519),
        _ => Err(anyhow::anyhow!("Invalid ciphersuite description: {}", s)),
    }
}

pub fn ciphersuites() -> Vec<Algorithms> {
    vec![
        SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519,
        SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519,
        SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256,
        SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256,
        SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256,
        SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519,
        SHA256_Aes128Gcm_RsaPssRsaSha256_P256,
        SHA256_Aes128Gcm_RsaPssRsaSha256_X25519,
        SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256,
        SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519,
        SHA384_Aes256Gcm_RsaPssRsaSha256_P256,
        SHA384_Aes256Gcm_RsaPssRsaSha256_X25519,
    ]
}

#[tracing::instrument(skip(stream, request, algorithms))]
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
    let (client_hello, client_state) = {
        let sni = Bytes::from(host.as_bytes());
        let ent = {
            let mut entropy = [0u8; 64];
            thread_rng().fill(&mut entropy);
            Entropy::from(&entropy)
        };

        Client::connect(algorithms, &sni, None, None, ent)?
    };

    stream.write_record(client_hello)?;

    let server_hello = stream.read_record()?;

    // TODO: Who should do this check?
    if eq1(server_hello[0], 21.into()) {
        // Alert
        eprintln!(
            "Server does not support proposed algorithms. {:?}",
            algorithms
        );
        return Err(UNSUPPORTED_ALGORITHM.into());
    }

    let cstate = match client_state.read_handshake(&server_hello) {
        Ok((_, cstate)) => cstate,
        Err(e) => {
            match e {
                UNSUPPORTED_ALGORITHM => eprintln!("Server does not support proposed algorithms."),
                PROTOCOL_VERSION_ALERT => eprintln!("Wrong TLS protocol version TLS({:?})", e),
                APPLICATION_DATA_INSTEAD_OF_HANDSHAKE => {
                    eprintln!("Server sent application data instead of a handshake message.")
                }
                MISSING_KEY_SHARE => eprintln!("Hello message was missing a key share."),
                DECODE_ERROR => eprintln!("Decode error."), // parsing of the server hello failed
                _ => eprintln!("Bertie client error {}", e),
            }
            return Err(e.into());
        }
    };

    let change_cipher_spec = stream.read_record()?;
    verify_ccs_message(change_cipher_spec)?;

    let mut cf_rec = None;
    let mut client_state = cstate;
    while cf_rec.is_none() {
        let rec = stream.read_record()?;

        let (new_cf_rec, new_cstate) = match client_state.read_handshake(&rec) {
            Ok((new_cf_rec, new_cstate)) => (new_cf_rec, new_cstate),
            Err(e) => {
                match e {
                    INVALID_SIGNATURE => eprintln!("Invalid server signature"), // parsing of the certificate failed
                    _ => eprintln!("Bertie client error {}", e),
                }
                return Err(e.into());
            }
        };
        cf_rec = new_cf_rec;
        client_state = new_cstate;
    }

    let change_cipher_spec = Bytes::from_hex("140303000101");
    stream.write_record(change_cipher_spec)?;

    // Safety: Safe to unwrap().
    let cf_rec = cf_rec.unwrap();
    stream.write_record(cf_rec)?;

    info!("----- Handshake finished -----");

    /* Send HTTP GET  */

    let (ap, state) = {
        let http_get = Bytes::from(request.as_bytes());
        client_write(AppData::new(http_get), client_state)?
    };

    stream.write_record(ap)?;

    /* Process HTTP response */

    let mut application_data = None;
    let mut client_state = state;
    while application_data.is_none() {
        let message_bytes = stream.read_record()?;

        let (new_application_data, new_cstate) = client_state.read(&message_bytes)?;
        application_data = new_application_data;
        client_state = new_cstate;
    }

    let response_prefix = {
        // Safety: Safe to unwrap().
        let body = application_data.unwrap().into_raw();

        // Safety: Safe to unwrap().
        hex::decode(body.to_hex()).unwrap()
    };

    Ok((stream, client_state, response_prefix))
}

pub fn tls13client_continue<Stream>(
    mut stream: RecordStream<Stream>,
    cstate: Client,
) -> Result<(RecordStream<Stream>, Client, Vec<u8>), AppError>
where
    Stream: Read + Write,
{
    let mut application_data = None;
    let mut cstate = cstate;
    while application_data.is_none() {
        let message_bytes = stream.read_record()?;

        let (new_ad, new_cstate) = cstate.read(&message_bytes)?;
        application_data = new_ad;
        cstate = new_cstate;
    }

    let response_prefix = {
        // Safety: Safe to unwrap().
        let body = application_data.unwrap().into_raw();

        // Safety: Safe to unwrap().
        hex::decode(body.to_hex()).unwrap()
    };

    Ok((stream, cstate, response_prefix))
}

pub(crate) fn verify_ccs_message(rec: Bytes) -> Result<(), AppError> {
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
