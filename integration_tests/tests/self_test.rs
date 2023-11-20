use std::net::{TcpListener, TcpStream};

use simple_https_client::tls13client;
use simple_https_server::tls13server;

#[test]
#[should_panic]
fn test_sha256_chacha20_poly1305_rsa_pss_rsa_sha256_x25519() {
    self_test_algorithm(simple_https_client::SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519);
}
#[test]
fn test_sha256_chacha20_poly1305_ecdsa_secp256r1_sha256_x25519() {
    self_test_algorithm(simple_https_client::SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519);
}
#[test]
fn test_sha256_chacha20_poly1305_ecdsa_secp256r1_sha256_p256() {
    self_test_algorithm(simple_https_client::SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256);
}
#[test]
#[should_panic]
fn test_sha256_chacha20_poly1305_rsa_pss_rsa_sha256_p256() {
    self_test_algorithm(simple_https_client::SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256);
}
#[test]
fn test_sha256_aes128_gcm_ecdsa_secp256r1_sha256_p256() {
    if libcrux_platform::aes_ni_support() {
        self_test_algorithm(simple_https_client::SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256);
    }
}
#[test]
fn test_sha256_aes128_gcm_ecdsa_secp256r1_sha256_x25519() {
    if libcrux_platform::aes_ni_support() {
        self_test_algorithm(simple_https_client::SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519);
    }
}
#[test]
#[should_panic]
fn test_sha256_aes128_gcm_rsa_pss_rsa_sha256_p256() {
    if libcrux_platform::aes_ni_support() {
        self_test_algorithm(simple_https_client::SHA256_Aes128Gcm_RsaPssRsaSha256_P256);
    }
}
#[test]
#[should_panic]
fn test_sha256_aes128_gcm_rsa_pss_rsa_sha256_x25519() {
    if libcrux_platform::aes_ni_support() {
        self_test_algorithm(simple_https_client::SHA256_Aes128Gcm_RsaPssRsaSha256_X25519);
    }
}
#[test]
fn test_sha384_aes256_gcm_ecdsa_secp256r1_sha256_p256() {
    if libcrux_platform::aes_ni_support() {
        self_test_algorithm(simple_https_client::SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256);
    }
}
#[test]
fn test_sha384_aes256_gcm_ecdsa_secp256r1_sha256_x25519() {
    if libcrux_platform::aes_ni_support() {
        self_test_algorithm(simple_https_client::SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519);
    }
}
#[test]
#[should_panic]
fn test_sha384_aes256_gcm_rsa_pss_rsa_sha256_p256() {
    if libcrux_platform::aes_ni_support() {
        self_test_algorithm(simple_https_client::SHA384_Aes256Gcm_RsaPssRsaSha256_P256);
    }
}
#[test]
#[should_panic]
fn test_sha384_aes256_gcm_rsa_pss_rsa_sha256_x25519() {
    if libcrux_platform::aes_ni_support() {
        self_test_algorithm(simple_https_client::SHA384_Aes256Gcm_RsaPssRsaSha256_X25519);
    }
}

fn self_test_algorithm(algorithms: bertie::tls13crypto::Algorithms) {
    let (tx, rx) = std::sync::mpsc::channel();

    // Server thread.
    let server = std::thread::spawn(move || {
        let (stream, _) = {
            // We use an ephemeral (free) port (by using ":0") ...
            let listener = TcpListener::bind("127.0.0.1:0").unwrap();
            let port = listener.local_addr().unwrap().port();
            println!("Server listens on 127.0.0.1:{}.", port);

            // ... and let the client thread know.
            tx.send(port).unwrap();

            listener.accept().unwrap()
        };

        tls13server(stream, "127.0.0.1", Some(algorithms)).unwrap();

        println!("Server finished.");
    });

    // Client thread.
    let port = rx.recv().unwrap();

    let client = TcpStream::connect(("127.0.0.1", port)).unwrap();

    println!("Client connected to 127.0.0.1:{}.", port);

    let (_, _, data) = tls13client(
        "127.0.0.1",
        client,
        Some(algorithms),
        "GET / HTTP/1.1\r\nHost: 127.0.0.1\r\n\r\n",
    )
    .unwrap();

    println!("{}", std::str::from_utf8(&data).unwrap());

    println!("Client finished.");

    server.join().unwrap();
}
