//! # Simple TLS 1.3 HTTP Client Implementation
//!
//! It connects to a given host:port, sends an HTTP "GET /", and prints a prefix of the HTTP response.
//!
//! WARNING: This code is not in hacspec since it need to use TCP etc.

#![allow(non_upper_case_globals)]

use std::{io::prelude::*, net::TcpStream, str, time::Duration};

use bertie::{tls13api::*, tls13utils::*};
#[cfg(feature = "evercrypt")]
use evercrypt_cryptolib::*;
#[cfg(not(feature = "evercrypt"))]
use hacspec_cryptolib::*;
use hacspec_lib::*;
use rand::*;
use tracing::{error, info};

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

#[tracing::instrument(skip(request))]
pub fn tls13client(
    host: &str,
    port: u16,
    request: &str,
) -> Result<(TcpStream, Client, Vec<u8>), TLSError> {
    // # Demo of a simple HTTPS client.
    //
    // The client ...
    //   * connects to host:port via TCP,
    //   * executes a TLS 1.3 handshake,
    //   * sends an encrypted HTTP GET, and
    //   * prints a prefix of the servers HTTP response.

    // # Connect to host:port via TCP.

    // Create TCP stream.
    let mut stream = {
        info!("Initiating connection ...");
        std::io::stdout().flush().unwrap();

        let stream = TcpStream::connect((host, port)).unwrap();
        let duration = Duration::new(1, 0);
        stream
            .set_read_timeout(Some(duration))
            .expect("set_read_timeout call failed");

        info!("Initiating connection done.");

        stream
    };

    // Create input buffer.
    let mut in_buf = [0; 8192];

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

    io::write_record(&mut stream, &ch_rec)?;

    // Process server response.
    let sh_rec = {
        let len = io::read_record(&mut stream, &mut in_buf)?;

        ByteSeq::from_public_slice(&in_buf[0..len])
    };

    if eq1(sh_rec[0], U8(21)) {
        // Alert
        error!("Server does not support proposed algorithms.");
        Err(UNSUPPORTED_ALGORITHM)
    } else {
        //println!("Got SH record: {}",sh_rec.len());

        let (_, cstate) = client_read_handshake(&sh_rec, cstate)?;

        //println!("Got SH");

        io::read_ccs_message(&mut stream, &mut in_buf)?;

        //println!("Got SCCS");

        let mut cf_rec = None;
        let mut cstate = cstate;
        while cf_rec == None {
            let rec = {
                let len = io::read_record(&mut stream, &mut in_buf)?;

                ByteSeq::from_public_slice(&in_buf[0..len])
            };

            let (new_cf, new_cstate) = client_read_handshake(&rec, cstate)?;
            cf_rec = new_cf;
            cstate = new_cstate;
        }

        info!("Received SFIN.");

        // Safety: Safe to unwrap().
        let cf_rec = cf_rec.unwrap();

        /* Complete Connection */

        info!("Sending CSS + CF ...");
        std::io::stdout().flush().unwrap();
        io::write_ccs_message(&mut stream)?;
        io::write_record(&mut stream, &cf_rec)?;
        info!("Sending CSS + CF done.");

        info!("----- Handshake finished -----");

        /* Send HTTP GET  */

        let (ap, cstate) = {
            let http_get = ByteSeq::from_public_slice(request.as_bytes());

            client_write(app_data(http_get), cstate)?
        };

        info!("Sending request ...");
        std::io::stdout().flush().unwrap();
        io::write_record(&mut stream, &ap)?;
        info!("Sending request done.");

        /* Process HTTP response */

        let mut ad = None;
        let mut cstate = cstate;
        while ad == None {
            let rec = {
                let len = io::read_record(&mut stream, &mut in_buf)?;
                ByteSeq::from_public_slice(&in_buf[0..len])
            };

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
    mut stream: TcpStream,
    cstate: Client,
) -> Result<(TcpStream, Client, Vec<u8>), TLSError> {
    // Create input buffer.
    let mut in_buf = [0; 8192];

    let mut ad = None;
    let mut cstate = cstate;
    while ad == None {
        let rec = {
            let len = io::read_record(&mut stream, &mut in_buf)?;
            ByteSeq::from_public_slice(&in_buf[0..len])
        };

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

mod io {
    use std::{
        io::{Read, Write},
        net::TcpStream,
    };

    use bertie::{Bytes, TLSError, INSUFFICIENT_DATA, PARSE_FAILED, PAYLOAD_TOO_LONG};
    use hacspec_lib::ByteSeq;
    use tracing::{debug, error};

    #[tracing::instrument(skip(stream, buf, nbytes))]
    pub(crate) fn read_bytes(
        stream: &mut TcpStream,
        buf: &mut [u8],
        nbytes: usize,
    ) -> Result<usize, TLSError> {
        // TODO: Avoid this invariant.
        assert!(nbytes <= buf.len());

        let mut total = 0;

        loop {
            match stream.read(&mut buf[total..]) {
                Ok(0) => {
                    debug!(%total, "Connection closed.");

                    if total >= nbytes {
                        let extra = total - nbytes;
                        return Ok(extra);
                    } else {
                        return Err(INSUFFICIENT_DATA);
                    }
                }
                Ok(amt) => {
                    total += amt;

                    debug!(%total, %amt, "Data received.");

                    if total >= nbytes {
                        let extra = total - nbytes;
                        return Ok(extra);
                    }
                }
                Err(error) => {
                    error!(%error, "Error received.");

                    return Err(INSUFFICIENT_DATA);
                }
            }
        }
    }

    #[tracing::instrument(skip(stream, buf))]
    pub(crate) fn read_record(stream: &mut TcpStream, buf: &mut [u8]) -> Result<usize, TLSError> {
        let mut b: [u8; 5] = [0; 5];
        let mut len = 0;
        while len < 5 {
            match stream.peek(&mut b) {
                Result::Ok(l) => len = l,
                Result::Err(_) => Err(INSUFFICIENT_DATA)?,
            }
        }
        let l0 = b[3] as usize;
        let l1 = b[4] as usize;
        let len = l0 * 256 + l1;
        if len + 5 > buf.len() {
            Err(INSUFFICIENT_DATA)
        } else {
            let extra = read_bytes(stream, &mut buf[0..len + 5], len + 5)?;
            if extra > 0 {
                Err(PAYLOAD_TOO_LONG)
            } else {
                Ok(len + 5)
            }
        }
    }

    #[tracing::instrument(skip(stream, rec))]
    pub(crate) fn write_record(stream: &mut TcpStream, rec: &Bytes) -> Result<(), TLSError> {
        // Safe to unwrap().
        // TODO: Provide `Bytes` -> `Vec<u8>` conversion?
        let wire = hex::decode(&rec.to_hex()).unwrap();
        // FIXME: Do not use unwrap().
        // Note: Will be fixed in next commit.
        stream.write_all(&wire).unwrap();
        Ok(())
    }

    #[tracing::instrument(skip(stream, buf))]
    pub(crate) fn read_ccs_message(stream: &mut TcpStream, buf: &mut [u8]) -> Result<(), TLSError> {
        let len = read_record(stream, buf)?;
        if len == 6
            && buf[0] == 0x14
            && buf[1] == 0x03
            && buf[2] == 0x03
            && buf[3] == 0x00
            && buf[4] == 0x01
            && buf[5] == 0x01
        {
            Ok(())
        } else {
            Err(PARSE_FAILED)
        }
    }

    #[tracing::instrument(skip(stream))]
    pub(crate) fn write_ccs_message(stream: &mut TcpStream) -> Result<(), TLSError> {
        let ccs_rec = ByteSeq::from_hex("140303000101");
        write_record(stream, &ccs_rec)
    }
}
