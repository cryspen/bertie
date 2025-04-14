#![allow(dead_code)]

use bytesize::ByteSize;
use std::alloc;
use std::net::TcpListener;

use t13::{
    stream::t13Stream,
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
};
const STACK_SIZE: usize = 8000 * 1024; // ~8MB of stack
const STACK_ALIGN: usize = 4096;

macro_rules! measure {
    ($name:literal, $fut: expr) => {
        let layout = alloc::Layout::from_size_align(STACK_SIZE, STACK_ALIGN).unwrap();

        unsafe {
            let paintstack = alloc::alloc(layout);
            assert!(!paintstack.is_null(), "allocations must succeed!");
            for i in (0..STACK_SIZE).step_by(4) {
                *paintstack.add(i) = 0xfe;
                *paintstack.add(i + 1) = 0xca;
                *paintstack.add(i + 2) = 0xfe;
                *paintstack.add(i + 3) = 0xca;
            }

            psm::on_stack(paintstack, STACK_SIZE, || {
                let _ = $fut;
            });

            for i in (0..STACK_SIZE).step_by(4) {
                let s = std::slice::from_raw_parts(paintstack.add(i), 4);
                if s != [0xfe, 0xca, 0xfe, 0xca] {
                    let highest_stack_usage = STACK_SIZE - i;
                    println!(
                        "[{: <14}] Highest stack usage: {}",
                        $name,
                        ByteSize(highest_stack_usage.try_into().unwrap())
                    );
                    break;
                }
            }
            alloc::dealloc(paintstack, layout);
        }
    };
}

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

/// Measure stack usage of the TLS protocol from the view of the client.
fn protocol() {
    println!("Client Stack Usage:");
    println!("===================");

    for ciphersuite in CIPHERSUITES {
        println!("\nCiphersuite: {ciphersuite}");
        let (tx, rx) = std::sync::mpsc::channel();

        // Server thread.
        let server = std::thread::spawn(move || {
            // We use an ephemeral (free) port (by using ":0") ...
            let listener = TcpListener::bind("127.0.0.1:0").unwrap();
            let port = listener.local_addr().unwrap().port();

            // ... and let the client thread know.
            tx.send(port).unwrap();

            let (stream, _) = listener.accept().unwrap();

            // tls13server(stream, "127.0.0.1", Some(algorithms)).unwrap();

            let (cert_file, key_file) = match ciphersuite.signature() {
                SignatureScheme::EcdsaSecp256r1Sha256 => (
                    "./tests/assets/p256_cert.der",
                    "./tests/assets/p256_key.der",
                ),
                SignatureScheme::RsaPssRsaSha256 => {
                    ("./tests/assets/rsa_cert.der", "./tests/assets/rsa_key.der")
                }
                _ => unreachable!("Unknown ciphersuite {:?}", ciphersuite),
            };
            let mut server =
                t13Stream::server("127.0.0.1", port, stream, ciphersuite, cert_file, key_file)
                    .unwrap();

            server.connect(&mut rand::rng()).unwrap();
            server
        });

        // Client thread.
        let port = rx.recv().unwrap();

        let mut client;
        let layout = alloc::Layout::from_size_align(STACK_SIZE, STACK_ALIGN).unwrap();
        unsafe {
            let paintstack = alloc::alloc(layout);
            assert!(!paintstack.is_null(), "allocations must succeed!");
            for i in (0..STACK_SIZE).step_by(4) {
                *paintstack.add(i) = 0xfe;
                *paintstack.add(i + 1) = 0xca;
                *paintstack.add(i + 2) = 0xfe;
                *paintstack.add(i + 3) = 0xca;
            }

            client = psm::on_stack(paintstack, STACK_SIZE, || {
                t13Stream::client("127.0.0.1", port, ciphersuite, &mut rand::rng()).unwrap()
            });

            for i in (0..STACK_SIZE).step_by(4) {
                let s = std::slice::from_raw_parts(paintstack.add(i), 4);
                if s != [0xfe, 0xca, 0xfe, 0xca] {
                    let highest_stack_usage = STACK_SIZE - i;
                    println!(
                        "[{: <14}] Highest stack usage: {}",
                        "Client Connect",
                        ByteSize(highest_stack_usage.try_into().unwrap())
                    );
                    break;
                }
            }
            alloc::dealloc(paintstack, layout);
        }

        measure!("Client Write", || client
            .write("GET / HTTP/1.1\r\nHost: 127.0.0.1\r\n\r\n".as_bytes()));

        // Exchange a message on the TLS channel.
        let msg =
            "Hello from the t13 server. Congratulations on the successful interop.".as_bytes();
        let mut server = server.join().unwrap();
        server.write(msg).unwrap();

        let data;
        let layout = alloc::Layout::from_size_align(STACK_SIZE, STACK_ALIGN).unwrap();
        unsafe {
            let paintstack = alloc::alloc(layout);
            assert!(!paintstack.is_null(), "allocations must succeed!");
            for i in (0..STACK_SIZE).step_by(4) {
                *paintstack.add(i) = 0xfe;
                *paintstack.add(i + 1) = 0xca;
                *paintstack.add(i + 2) = 0xfe;
                *paintstack.add(i + 3) = 0xca;
            }

            data = psm::on_stack(paintstack, STACK_SIZE, || client.read().unwrap());

            for i in (0..STACK_SIZE).step_by(4) {
                let s = std::slice::from_raw_parts(paintstack.add(i), 4);
                if s != [0xfe, 0xca, 0xfe, 0xca] {
                    let highest_stack_usage = STACK_SIZE - i;
                    println!(
                        "[{: <14}] Highest stack usage: {}",
                        "Client Read",
                        ByteSize(highest_stack_usage.try_into().unwrap())
                    );
                    break;
                }
            }
            alloc::dealloc(paintstack, layout);
        }

        assert_eq!(data, msg);
    }
}

fn main() {
    protocol();
}
