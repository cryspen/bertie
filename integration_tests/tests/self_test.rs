use rand::thread_rng;
use std::net::TcpListener;

use bertie::{
    stream::BertieStream,
    tls13crypto::SignatureScheme,
    tls13crypto::{
        SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256, SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519,
        SHA256_Aes128Gcm_RsaPssRsaSha256_P256, SHA256_Aes128Gcm_RsaPssRsaSha256_X25519,
        SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256,
        SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519,
        SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256,
        SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519, SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256,
        SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519, SHA384_Aes256Gcm_RsaPssRsaSha256_P256,
        SHA384_Aes256Gcm_RsaPssRsaSha256_X25519,
    },
};

#[test]
fn test_sha256_chacha20_poly1305_rsa_pss_rsa_sha256_x25519() {
    self_test_algorithm(SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519);
}
#[test]
fn test_sha256_chacha20_poly1305_ecdsa_secp256r1_sha256_x25519() {
    self_test_algorithm(SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519);
}
#[test]
fn test_sha256_chacha20_poly1305_ecdsa_secp256r1_sha256_p256() {
    self_test_algorithm(SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256);
}
#[test]
fn test_sha256_chacha20_poly1305_rsa_pss_rsa_sha256_p256() {
    self_test_algorithm(SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256);
}
#[test]
fn test_sha256_aes128_gcm_ecdsa_secp256r1_sha256_p256() {
    if libcrux_platform::aes_ni_support() && cfg!(target_arch = "x64") {
        self_test_algorithm(SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256);
    }
}
#[test]
fn test_sha256_aes128_gcm_ecdsa_secp256r1_sha256_x25519() {
    if libcrux_platform::aes_ni_support() && cfg!(target_arch = "x64") {
        self_test_algorithm(SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519);
    }
}
#[test]
fn test_sha256_aes128_gcm_rsa_pss_rsa_sha256_p256() {
    if libcrux_platform::aes_ni_support() && cfg!(target_arch = "x64") {
        self_test_algorithm(SHA256_Aes128Gcm_RsaPssRsaSha256_P256);
    }
}
#[test]
fn test_sha256_aes128_gcm_rsa_pss_rsa_sha256_x25519() {
    if libcrux_platform::aes_ni_support() && cfg!(target_arch = "x64") {
        self_test_algorithm(SHA256_Aes128Gcm_RsaPssRsaSha256_X25519);
    }
}
#[test]
fn test_sha384_aes256_gcm_ecdsa_secp256r1_sha256_p256() {
    if libcrux_platform::aes_ni_support() && cfg!(target_arch = "x64") {
        self_test_algorithm(SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256);
    }
}
#[test]
fn test_sha384_aes256_gcm_ecdsa_secp256r1_sha256_x25519() {
    if libcrux_platform::aes_ni_support() && cfg!(target_arch = "x64") {
        self_test_algorithm(SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519);
    }
}
#[test]
fn test_sha384_aes256_gcm_rsa_pss_rsa_sha256_p256() {
    if libcrux_platform::aes_ni_support() && cfg!(target_arch = "x64") {
        self_test_algorithm(SHA384_Aes256Gcm_RsaPssRsaSha256_P256);
    }
}
#[test]
fn test_sha384_aes256_gcm_rsa_pss_rsa_sha256_x25519() {
    if libcrux_platform::aes_ni_support() && cfg!(target_arch = "x64") {
        self_test_algorithm(SHA384_Aes256Gcm_RsaPssRsaSha256_X25519);
    }
}

fn self_test_algorithm(ciphersuite: bertie::tls13crypto::Algorithms) {
    let _ = tracing_subscriber::fmt::try_init();

    let (tx, rx) = std::sync::mpsc::channel();

    // Server thread.
    let server = std::thread::spawn(move || {
        // We use an ephemeral (free) port (by using ":0") ...
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let port = listener.local_addr().unwrap().port();
        eprintln!("Server listens on 127.0.0.1:{}.", port);

        // ... and let the client thread know.
        tx.send(port).unwrap();

        let (stream, _) = listener.accept().unwrap();

        // tls13server(stream, "127.0.0.1", Some(algorithms)).unwrap();

        let (cert_file, key_file) = match ciphersuite.signature() {
            SignatureScheme::EcdsaSecp256r1Sha256 => (
                "../tests/assets/p256_cert.der",
                "../tests/assets/p256_key.der",
            ),
            SignatureScheme::RsaPssRsaSha256 => (
                "../tests/assets/rsa_cert.der",
                "../tests/assets/rsa_key.der",
            ),
            _ => unreachable!("Unknown ciphersuite {:?}", ciphersuite),
        };
        let mut server =
            BertieStream::server("127.0.0.1", port, stream, ciphersuite, cert_file, key_file)
                .unwrap();

        eprintln!("Server setup finished.");
        server.connect(&mut thread_rng()).unwrap();
        server
    });

    // Client thread.
    let port = rx.recv().unwrap();

    let mut client = BertieStream::client("127.0.0.1", port, ciphersuite, &mut thread_rng())
        .expect("Error connecting to server");
    eprintln!("Client connected to 127.0.0.1:{}.", port);

    client
        .write("GET / HTTP/1.1\r\nHost: 127.0.0.1\r\n\r\n".as_bytes())
        .expect("Error writing to Bertie stream");

    // Exchange a message on the TLS channel.
    let msg = "Hello from the Bertie server. Congratulations on the successful interop.".as_bytes();
    let mut server = server.join().unwrap();
    server.write(msg).unwrap();

    let data = client.read().unwrap();
    assert_eq!(data, msg);
    eprintln!("{}", std::str::from_utf8(&data).unwrap());

    eprintln!("Client finished.");
}
