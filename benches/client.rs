#![allow(dead_code)]

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
        SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256,
        SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519,
        SignatureScheme,
    },
    tls13utils::Bytes,
    Client, Server,
};
use libcrux::{digest, drbg::Drbg};

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

const ITERATIONS: usize = 500;
const NUM_PAYLOAD_BYTES: usize = 0x4000;
const CIPHERSUITES: [Algorithms; 4] = [
    // SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256,
    // SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519,
    // SHA256_Aes128Gcm_RsaPssRsaSha256_P256,
    // SHA256_Aes128Gcm_RsaPssRsaSha256_X25519,
    SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256,
    SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519,
    SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256,
    SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519,
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
            &bertie::tls13crypto::SHA256_Aes128Gcm_RsaPssRsaSha256_X25519,
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

/// Benchmark the TLS protocol from the view of the client.
fn protocol() {
    println!("Client");

    for ciphersuite in CIPHERSUITES {
        let mut rng = Drbg::new(digest::Algorithm::Sha256).unwrap();

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
        let payload = rng.generate_vec(NUM_PAYLOAD_BYTES).unwrap();

        for _ in 0..ITERATIONS {
            let start_time = Instant::now();
            let (client_hello, client) =
                Client::connect(ciphersuite, &server_name, None, None, &mut rng).unwrap();
            let end_time = Instant::now();
            handshake_time += end_time.duration_since(start_time);

            let (server_hello, server_finished, server) =
                Server::accept(ciphersuite, db.clone(), &client_hello, &mut rng).unwrap();

            let start_time = Instant::now();
            let (_client_msg, client) = client.read_handshake(&Bytes::from(server_hello)).unwrap();
            let (client_msg, client) = client
                .read_handshake(&Bytes::from(server_finished))
                .unwrap();
            let end_time = Instant::now();
            handshake_time += end_time.duration_since(start_time);

            let server = server.read_handshake(&client_msg.unwrap()).unwrap();

            let application_data = payload.clone().into();

            let start_time = Instant::now();
            let (c_msg_bytes, _client) = client.write(application_data).unwrap();
            let end_time = Instant::now();
            application_time += end_time.duration_since(start_time);

            let (msg, _server) = server.read(&c_msg_bytes).unwrap();

            assert_eq!(msg.unwrap().as_raw().declassify(), payload);
        }

        println!(
            " - {}:\n\tHandshake: {} μs | {} /s \n\tApplication: {} μs | {} MB/s",
            ciphersuite,
            handshake_time.as_micros() / (ITERATIONS as u128),
            hs_per_second(handshake_time),
            application_time.as_micros() / (ITERATIONS as u128),
            mb_per_second(application_time),
        );
    }
}

fn main() {
    protocol();

    #[cfg(bench)]
    {
        client_hello();
    }
}
