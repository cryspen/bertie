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

/// Benchmark the parsing of the client hello.
#[cfg(bench)]
fn parse_client_hello() {
    const CLIENT_HELLO: &str = "01 00 00 c0 03 03 cb 34 ec b1 e7 81 63
ba 1c 38 c6 da cb 19 6a 6d ff a2 1a 8d 99 12 ec 18 a2 ef 62 83
02 4d ec e7 00 00 06 13 01 13 03 13 02 01 00 00 91 00 00 00 0b
00 09 00 00 06 73 65 72 76 65 72 ff 01 00 01 00 00 0a 00 14 00
12 00 1d 00 17 00 18 00 19 01 00 01 01 01 02 01 03 01 04 00 23
00 00 00 33 00 26 00 24 00 1d 00 20 99 38 1d e5 60 e4 bd 43 d2
3d 8e 43 5a 7d ba fe b3 c0 6e 51 c1 3c ae 4d 54 13 69 1e 52 9a
af 2c 00 2b 00 03 02 03 04 00 0d 00 20 00 1e 04 03 05 03 06 03
02 03 08 04 08 05 08 06 04 01 05 01 06 01 02 01 04 02 05 02 06
02 02 02 00 2d 00 02 01 01 00 1c 00 02 40 01";

    const ITERATIONS: usize = 1000000;

    let ch = bertie::HandshakeData::from(Bytes::from_hex(CLIENT_HELLO));
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _res = bertie::bench_parse_client_hello(
            &bertie::tls13crypto::SHA256_Aes128Gcm_RsaPssRsaSha256_X25519,
            &ch,
        );
    }
    let end = Instant::now();
    println!(
        "Parse client hello: {} μs",
        end.duration_since(start).as_micros() as f64 / ITERATIONS as f64
    );
}

fn main() {
    // protocol();

    #[cfg(bench)]
    {
        parse_client_hello();
    }
}

/// Benchmark the TLS 1.3 protocol from the view of the server.
fn protocol() {
    println!("Server");

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
            let (client_hello, client) =
                Client::connect(ciphersuite, &server_name, None, None, &mut rng).unwrap();

            let start_time = Instant::now();
            let (server_hello, server_finished, server) =
                Server::accept(ciphersuite, db.clone(), &client_hello, &mut rng).unwrap();
            let end_time = Instant::now();
            handshake_time += end_time.duration_since(start_time);

            let (_client_msg, client) = client.read_handshake(&Bytes::from(server_hello)).unwrap();
            let (client_msg, client) = client
                .read_handshake(&Bytes::from(server_finished))
                .unwrap();

            let start_time = Instant::now();
            let server = server.read_handshake(&client_msg.unwrap()).unwrap();
            let end_time = Instant::now();
            handshake_time += end_time.duration_since(start_time);

            let application_data = payload.clone().into();
            let (c_msg_bytes, _client) = client.write(application_data).unwrap();

            let start_time = Instant::now();
            let (msg, _server) = server.read(&c_msg_bytes).unwrap();
            let end_time = Instant::now();
            application_time += end_time.duration_since(start_time);

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
