#![allow(dead_code)]

use std::collections::HashMap;
use std::time::{Duration, Instant};

use bertie::{
    stream::init_db,
    tls13crypto::{
        Algorithms,
        // SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256,
        // SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519,
        // SHA256_Aes128Gcm_RsaPssRsaSha256_P256,
        // SHA256_Aes128Gcm_RsaPssRsaSha256_X25519,
        // SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256,
        // SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519,
        // SHA384_Aes256Gcm_RsaPssRsaSha256_P256,
        // SHA384_Aes256Gcm_RsaPssRsaSha256_X25519,
        SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256,
        SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519,
        SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519Kyber768Draft00,
        SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519MlKem768,
        SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256,
        SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519,
        SignatureScheme,
    },
    tls13utils::Bytes,
    Client, Server, TLSkeyscheduler,
};
use rand::RngCore;

fn hs_per_second(d: Duration) -> f64 {
    // ITERATIONS per d
    let d = d.as_nanos() as f64 / 1_000_000_000.0;
    ITERATIONS as f64 / d
}

fn mb_per_second(d: Duration) -> f64 {
    // ITERATIONS per d
    // NUM_PAYLOAD_BYTES / 1024 / 1024 per iteration
    let d = d.as_nanos() as f64 / 1_000_000_000.0;
    let iteration = d / ITERATIONS as f64;
    (NUM_PAYLOAD_BYTES as f64 / 1024.0 / 1024.0) / iteration
}

const ITERATIONS: usize = 1000;
const NUM_PAYLOAD_BYTES: usize = 0x4000;
const CIPHERSUITES: [Algorithms; 6] = [
    // SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256,
    // SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519,
    // SHA256_Aes128Gcm_RsaPssRsaSha256_P256,
    // SHA256_Aes128Gcm_RsaPssRsaSha256_X25519,
    SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256,
    SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519,
    SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256,
    SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519,
    SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519Kyber768Draft00,
    SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519MlKem768,
    // SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256,
    // SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519,
    // SHA384_Aes256Gcm_RsaPssRsaSha256_P256,
    // SHA384_Aes256Gcm_RsaPssRsaSha256_X25519,
];

/// Benchmark the generation of the client hello.
#[cfg(bench)]
fn client_hello() {
    const CLIENT_X25519_PUB: &str = "99 38 1d e5 60 e4 bd 43 d2 3d 8e 43 5a 7d
    ba fe b3 c0 6e 51 c1 3c ae 4d 54 13 69 1e 52 9a af 2c";
    const ITERATIONS: usize = 1000000;

    let cr = Bytes::from(vec![]);
    let gx = Bytes::from_hex(CLIENT_X25519_PUB);
    let sn = Bytes::from(vec![23; 0]);
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _ch = bertie::bench_client_hello(
            &bertie::tls13crypto::SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519,
            cr.clone(),
            &gx,
            &sn,
            &None,
        );
    }
    let end = Instant::now();

    println!(
        "Build client hello: {} μs",
        end.duration_since(start).as_micros() as f64 / ITERATIONS as f64
    );
}

/// Benchmark the parsing of the server hello.
#[cfg(bench)]
fn parse_server_hello() {
    const SERVER_HELLO: &str = "02 00 00 56 03 03 a6 af 06 a4 12 18 60
    dc 5e 6e 60 24 9c d3 4c 95 93 0c 8a c5 cb 14 34 da c1 55 77 2e
    d3 e2 69 28 00 13 01 00 00 2e 00 33 00 24 00 1d 00 20 c9 82 88
    76 11 20 95 fe 66 76 2b db f7 c6 72 e1 56 d6 cc 25 3b 83 3d f1
    dd 69 b1 b0 4e 75 1f 0f 00 2b 00 02 03 04";
    let sh = bertie::HandshakeData::from(Bytes::from_hex(SERVER_HELLO));
    const ITERATIONS: usize = 5000000;

    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _sh = bertie::bench_parse_server_hello(
            &bertie::tls13crypto::SHA256_Aes128Gcm_RsaPssRsaSha256_X25519,
            &sh,
        );
    }
    let end = Instant::now();

    println!(
        "Parse server hello: {} μs",
        end.duration_since(start).as_micros() as f64 / ITERATIONS as f64
    );
}

/// Benchmark the parsing of the server certificate.
#[cfg(bench)]
fn parse_server_certificate() {
    const SERVER_CERTIFICATE: &str = "0b 00 01 b9 00 00 01 b5 00 01 b0 30 82
    01 ac 30 82 01 15 a0 03 02 01 02 02 01 02 30 0d 06 09 2a 86 48
    86 f7 0d 01 01 0b 05 00 30 0e 31 0c 30 0a 06 03 55 04 03 13 03
    72 73 61 30 1e 17 0d 31 36 30 37 33 30 30 31 32 33 35 39 5a 17
    0d 32 36 30 37 33 30 30 31 32 33 35 39 5a 30 0e 31 0c 30 0a 06
    03 55 04 03 13 03 72 73 61 30 81 9f 30 0d 06 09 2a 86 48 86 f7
    0d 01 01 01 05 00 03 81 8d 00 30 81 89 02 81 81 00 b4 bb 49 8f
    82 79 30 3d 98 08 36 39 9b 36 c6 98 8c 0c 68 de 55 e1 bd b8 26
    d3 90 1a 24 61 ea fd 2d e4 9a 91 d0 15 ab bc 9a 95 13 7a ce 6c
    1a f1 9e aa 6a f9 8c 7c ed 43 12 09 98 e1 87 a8 0e e0 cc b0 52
    4b 1b 01 8c 3e 0b 63 26 4d 44 9a 6d 38 e2 2a 5f da 43 08 46 74
    80 30 53 0e f0 46 1c 8c a9 d9 ef bf ae 8e a6 d1 d0 3e 2b d1 93
    ef f0 ab 9a 80 02 c4 74 28 a6 d3 5a 8d 88 d7 9f 7f 1e 3f 02 03
    01 00 01 a3 1a 30 18 30 09 06 03 55 1d 13 04 02 30 00 30 0b 06
    03 55 1d 0f 04 04 03 02 05 a0 30 0d 06 09 2a 86 48 86 f7 0d 01
    01 0b 05 00 03 81 81 00 85 aa d2 a0 e5 b9 27 6b 90 8c 65 f7 3a
    72 67 17 06 18 a5 4c 5f 8a 7b 33 7d 2d f7 a5 94 36 54 17 f2 ea
    e8 f8 a5 8c 8f 81 72 f9 31 9c f3 6b 7f d6 c5 5b 80 f2 1a 03 01
    51 56 72 60 96 fd 33 5e 5e 67 f2 db f1 02 70 2e 60 8c ca e6 be
    c1 fc 63 a4 2a 99 be 5c 3e b7 10 7c 3c 54 e9 b9 eb 2b d5 20 3b
    1c 3b 84 e0 a8 b2 f7 59 40 9b a3 ea c9 d9 1d 40 2d cc 0c c8 f8
    96 12 29 ac 91 87 b4 2b 4d e1 00 00";
    let sc = bertie::HandshakeData::from(Bytes::from_hex(SERVER_CERTIFICATE));
    const ITERATIONS: usize = 10000000;

    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _res = bertie::bench_parse_server_certificate(&sc);
    }
    let end = Instant::now();

    println!(
        "Parse server certificate: {} μs",
        end.duration_since(start).as_micros() as f64 / ITERATIONS as f64
    );
}

/// Benchmark the TLS protocol from the view of the client.
fn protocol() {
    println!("Client");

    for ciphersuite in CIPHERSUITES {
        let mut rng = Drbg::new(digest::Algorithm::Sha256).unwrap();
        let mut ks: TLSkeyscheduler = TLSkeyscheduler {
            keys: HashMap::new(),
        };

        // Server
        let server_name_str = "localhost";
        let server_name: Bytes = server_name_str.as_bytes().into();

        let (cert_file, key_file) = match ciphersuite.signature() {
            SignatureScheme::EcdsaSecp256r1Sha256 => {
                ("tests/assets/p256_cert.der", "tests/assets/p256_key.der")
            }
            SignatureScheme::RsaPssRsaSha256 => {
                ("tests/assets/rsa_cert.der", "tests/assets/rsa_key.der")
            }
            _ => unreachable!("Unknown ciphersuite {:?}", ciphersuite),
        };
        let db = init_db(server_name_str, key_file, cert_file).unwrap();

        let mut handshake_time = Duration::ZERO;
        let mut application_time = Duration::ZERO;
        let mut payload = vec![0u8; NUM_PAYLOAD_BYTES];
        rng.fill_bytes(&mut payload);
        let mut size1: usize = 0;
        let mut size2: usize = 0;
        let mut size3: usize = 0;

        for _ in 0..ITERATIONS {
            let start_time = Instant::now();
            let (client_hello, client) =
                Client::connect(ciphersuite, &server_name, None, None, &mut rng, &mut ks).unwrap();
            let end_time = Instant::now();
            handshake_time += end_time.duration_since(start_time);
            size1 += client_hello.declassify().len();

            let (server_hello, server_finished, server) =
                Server::accept(ciphersuite, db.clone(), &client_hello, &mut rng, &mut ks).unwrap();
            size2 += server_hello.declassify().len();
            size2 += server_finished.declassify().len();

            let start_time = Instant::now();
            let (_client_msg, client) = client.read_handshake(&server_hello, &mut ks).unwrap();
            let (client_msg, client) = client.read_handshake(&server_finished, &mut ks).unwrap();
            let end_time = Instant::now();
            handshake_time += end_time.duration_since(start_time);
            size3 += client_msg.as_ref().unwrap().declassify().len();

            let server = server
                .read_handshake(&client_msg.unwrap(), &mut ks)
                .unwrap();

            let application_data = payload.clone().into();

            let start_time = Instant::now();
            let (c_msg_bytes, _client) = client.write(application_data).unwrap();
            let end_time = Instant::now();
            application_time += end_time.duration_since(start_time);

            let (msg, _server) = server.read(&c_msg_bytes).unwrap();

            assert_eq!(msg.unwrap().as_raw().declassify(), payload);
        }

        println!(
            " - {}:\n\tHandshake: {} μs | {} /s \n\tApplication: {} μs | {} MB/s\n\tMessage Sizes: {}, {}, {} bytes",
            ciphersuite,
            handshake_time.as_micros() / (ITERATIONS as u128),
            hs_per_second(handshake_time),
            application_time.as_micros() / (ITERATIONS as u128),
            mb_per_second(application_time),
            size1/ITERATIONS, size2/ITERATIONS, size3/ITERATIONS
        );
    }
}

fn main() {
    protocol();

    #[cfg(bench)]
    {
        client_hello();
        parse_server_hello();
        parse_server_certificate();
    }
}
