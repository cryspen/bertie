//! # Ciphersuites
//!
//! This module defines TLS 1.3 ciphersuites to use with Bertie.

use crate::tls13crypto::{AeadAlgorithm, Algorithms, HashAlgorithm, KemScheme, SignatureScheme};

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
