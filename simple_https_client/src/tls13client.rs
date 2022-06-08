//! A Simple TLS 1.3 HTTP Client Implementation
//! It connects to a give host at port 443, sends an HTTP "GET /", and prints a prefix of the HTTP response
//! WARNING: This code is not in hacspec since it need to use TCP etc.

#![allow(non_upper_case_globals)]

// Import hacspec and all needed definitions.
use hacspec_lib::*;
use rand::*;
use std::env;
use std::time::Duration;

#[cfg(feature = "evercrypt")]
use evercrypt_cryptolib::*;
#[cfg(not(feature = "evercrypt"))]
use hacspec_cryptolib::*;

use bertie::tls13api::*;
use bertie::tls13utils::*;

use std::io::prelude::*;
use std::net::TcpStream;
use std::str;

fn read_bytes(stream: &mut TcpStream, buf: &mut [u8], nbytes: usize) -> Result<usize, TLSError> {
    match stream.read(&mut buf[..]) {
        Ok(len) => {
            if len >= nbytes {
                Ok(len - nbytes)
            } else {
                read_bytes(stream, &mut buf[len..], nbytes - len)
            }
        }
        Err(_) => Err(INSUFFICIENT_DATA),
    }
}

fn read_record(stream: &mut TcpStream, buf: &mut [u8]) -> Result<usize, TLSError> {
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

fn put_record(stream: &mut TcpStream, rec: &Bytes) -> Result<(), TLSError> {
    let wire = hex::decode(&rec.to_hex()).expect("Record Decoding Failed");
    match stream.write(&wire) {
        Err(_) => Err(INSUFFICIENT_DATA),
        Ok(len) => {
            if len < wire.len() {
                Err(PARSE_FAILED)
            } else {
                Ok(())
            }
        }
    }
}

fn get_ccs_message(stream: &mut TcpStream, buf: &mut [u8]) -> Result<(), TLSError> {
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

fn put_ccs_message(stream: &mut TcpStream) -> Result<(), TLSError> {
    let ccs_rec = ByteSeq::from_hex("140303000101");
    put_record(stream, &ccs_rec)
}

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

pub fn tls13client(host: &str, port: &str) -> Result<(), TLSError> {
    let mut entropy = [0 as u8; 64];
    let d = Duration::new(1, 0);
    thread_rng().fill(&mut entropy);
    let ent_c = Entropy::from_public_slice(&entropy);
    let sni = ByteSeq::from_public_slice(&host.as_bytes());
    let http_get_str = format!("GET / HTTP/1.1\r\nHost: {}\r\n\r\n", host);
    let http_get = ByteSeq::from_public_slice(http_get_str.as_bytes());

    /* Initiate TCP Connection */
    let addr = [host, port].join(":");
    let mut stream = TcpStream::connect(&addr).unwrap();
    stream
        .set_read_timeout(Some(d))
        .expect("set_read_timeout call failed");
    println!("Initiating connection to {}", addr);

    /* Initialize TLS 1.3. Client */
    let (ch_rec, cstate) = client_connect(default_algs, &sni, None, None, ent_c)?;
    put_record(&mut stream, &ch_rec)?;

    /* Process Server Response  */
    let mut in_buf = [0; 8192];
    let len = read_record(&mut stream, &mut in_buf)?;
    let sh_rec = ByteSeq::from_public_slice(&in_buf[0..len]);
    if eq1(sh_rec[0], U8(21)) {
        // Alert
        println!("Server does not support proposed algorithms");
        Err(UNSUPPORTED_ALGORITHM)
    } else {
        //println!("Got SH record: {}",sh_rec.len());

        let (_, cstate) = client_read_handshake(&sh_rec, cstate)?;

        //println!("Got SH");

        get_ccs_message(&mut stream, &mut in_buf)?;

        //println!("Got SCCS");

        let mut cf_rec = None;
        let mut cstate = cstate;
        while cf_rec == None {
            let len = read_record(&mut stream, &mut in_buf)?;
            let rec = ByteSeq::from_public_slice(&in_buf[0..len]);
            let (cf, st) = client_read_handshake(&rec, cstate)?;
            cstate = st;
            cf_rec = cf;
        }
        println!("Got SFIN");
        let cf_rec = cf_rec.unwrap();

        /* Complete Connection */
        put_ccs_message(&mut stream)?;
        put_record(&mut stream, &cf_rec)?;
        println!("Connected to {}:443", host);
        /* Send HTTP GET  */
        let (ap, cstate) = client_write(app_data(http_get), cstate)?;
        put_record(&mut stream, &ap)?;
        println!("Sent HTTP GET to {}:443", host);

        /* Process HTTP Response */
        let mut ad = None;
        let mut cstate = cstate;
        while ad == None {
            let len = read_record(&mut stream, &mut in_buf)?;
            let rec = ByteSeq::from_public_slice(&in_buf[0..len]);
            let (d, st) = client_read(&rec, cstate)?;
            cstate = st;
            ad = d;
        }
        let http_resp_by = ad.unwrap();
        let http_resp = app_data_bytes(http_resp_by);
        let html_by = hex::decode(&http_resp.to_hex()).expect("Decoding HTTP Response failed");
        let html = String::from_utf8_lossy(&html_by);
        println!("Received HTTP Response from {}\n\n{}", host, html);
        Ok(())
    }
}

pub fn main() {
    let args: Vec<String> = env::args().collect();
    let host = if args.len() <= 1 {
        "www.google.com"
    } else {
        &args[1]
    };
    let port = if args.len() <= 2 { "443" } else { &args[2] };
    match tls13client(host, port) {
        Err(x) => {
            println!("Connection to {} failed with {}\n", host, x);
        }
        Ok(()) => {
            println!("Connection to {} succeeded\n", host);
        }
    }
}
