use std::time::{Duration, Instant};

use bertie::{
    server::ServerDB,
    stream::init_db,
    tls13crypto::{
        Algorithms, SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256,
        SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519, SHA256_Aes128Gcm_RsaPssRsaSha256_P256,
        SHA256_Aes128Gcm_RsaPssRsaSha256_X25519, SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256,
        SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519,
        SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256,
        SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519, SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256,
        SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519, SHA384_Aes256Gcm_RsaPssRsaSha256_P256,
        SHA384_Aes256Gcm_RsaPssRsaSha256_X25519, SignatureScheme,
    },
    tls13utils::Bytes,
    Client, Server,
};
use libcrux::{digest, drbg::Drbg};

fn duration(d: Duration) -> f64 {
    ((d.as_secs() as f64) + (d.subsec_nanos() as f64 * 1e-9)) * 1000000f64
}

const ITERATIONS: usize = 50;
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

fn main() {
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

        let mut handshake_time = 0f64;
        let mut application_time = 0f64;
        let payload = rng.generate_vec(NUM_PAYLOAD_BYTES).unwrap();

        for _ in 0..ITERATIONS {
            let (client_hello, client) =
                Client::connect(ciphersuite, &server_name, None, None, &mut rng).unwrap();

            let start_time = Instant::now();
            let (server_hello, server_finished, server) =
                Server::accept(ciphersuite, db.clone(), &client_hello, &mut rng).unwrap();
            let end_time = Instant::now();
            handshake_time += duration(end_time.duration_since(start_time));

            let (_client_msg, client) = client.read_handshake(&Bytes::from(server_hello)).unwrap();
            let (client_msg, client) = client
                .read_handshake(&Bytes::from(server_finished))
                .unwrap();

            let start_time = Instant::now();
            let server = server.read_handshake(&client_msg.unwrap()).unwrap();
            let end_time = Instant::now();
            handshake_time += duration(end_time.duration_since(start_time));

            let application_data = payload.clone().into();
            let (c_msg_bytes, _client) = client.write(application_data).unwrap();

            let start_time = Instant::now();
            let (msg, _server) = server.read(&c_msg_bytes).unwrap();
            let end_time = Instant::now();
            application_time += duration(end_time.duration_since(start_time));

            assert_eq!(msg.unwrap().as_raw().declassify(), payload);
        }

        println!(
            " - {}:\n\tHandshake: {} μs\n\tApplication: {} μs",
            ciphersuite,
            handshake_time / (ITERATIONS as f64),
            application_time / (ITERATIONS as f64)
        );
    }
}
