//! TLS 1.3 cryptographic types and ciphersuite metadata.
//!
//! Bertie's cryptographic *operations* live on the [`BertieCrypto`] trait in
//! [`crate::crypto_provider`]; this module holds only the value types
//! (`HashAlgorithm`, `AeadKey`, `PublicVerificationKey`, `Algorithms`, …) that
//! flow between Bertie and its provider. The default backend that calls the
//! libcrux crates lives in [`crate::crypto_provider::LibcruxBertieProvider`].

#[cfg(feature = "hax-pv")]
use hax_lib::{proverif, pv_constructor};

use crate::std::{fmt::Display, format};
use crate::tls13utils::{
    check_mem, length_u16_encoded, tlserr, Bytes, Error, TLSError, U8, UNSUPPORTED_ALGORITHM,
};

pub(crate) type Random = Bytes;
pub type SignatureKey = Bytes;
pub(crate) type Psk = Bytes;
// The following aliases are exposed publicly so adapters (e.g. the
// `bertie-trace-adapter` symbolic-tracing wrapper) can implement the
// `BertieCrypto` trait outside this crate.
pub type Key = Bytes;
pub type MacKey = Bytes;
pub type KemPk = Bytes;
pub type KemSk = Bytes;
pub type Hmac = Bytes;
pub type Digest = Bytes;
pub type AeadIV = Bytes;
pub(crate) type VerificationKey = Bytes;

/// An AEAD key and iv package.
pub(crate) struct AeadKeyIV {
    pub(crate) key: AeadKey,
    pub(crate) iv: Bytes,
}

impl AeadKeyIV {
    /// Create a new [`AeadKeyIV`].
    pub(crate) fn new(key: AeadKey, iv: Bytes) -> Self {
        Self { key, iv }
    }
}

/// An AEAD key.
pub struct AeadKey {
    bytes: Bytes,
    _alg: AeadAlgorithm,
}

impl AeadKey {
    /// Create a new AEAD key from the raw bytes and the algorithm.
    pub(crate) fn new(bytes: Bytes, _alg: AeadAlgorithm) -> Self {
        Self { bytes, _alg }
    }

    /// Get the raw bytes of the key.
    pub fn bytes(&self) -> &Bytes {
        &self.bytes
    }
}

/// An RSA public key.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "hax-pv", hax_lib::opaque)]
pub struct RsaVerificationKey {
    pub modulus: Bytes,
    pub exponent: Bytes,
}

/// Bertie public verification keys.
#[derive(Debug, Clone)]
#[cfg_attr(
    feature = "hax-pv",
    proverif::replace(
        "fun ${PublicVerificationKey::EcDsa}(bitstring): bitstring [data].
fun ${PublicVerificationKey::Rsa}(bitstring): bitstring [data].
"
    )
)]
pub enum PublicVerificationKey {
    EcDsa(VerificationKey),  // Uncompressed point 0x04...
    Rsa(RsaVerificationKey), // N, e
}

/// Bertie hash algorithms.
#[derive(Clone, Copy, Eq, PartialEq, Debug, Hash)]
pub enum HashAlgorithm {
    SHA256,
    SHA384,
    SHA512,
}

#[hax_lib::attributes]
impl HashAlgorithm {
    /// Get the size of the hash digest in bytes.
    #[hax_lib::ensures(|result| result <= 64)]
    #[cfg_attr(feature = "hax-pv", hax_lib::pv_stub("nat_lit(0)"))]
    pub(crate) fn hash_len(&self) -> usize {
        match self {
            HashAlgorithm::SHA256 => 32,
            HashAlgorithm::SHA384 => 48,
            HashAlgorithm::SHA512 => 64,
        }
    }

    /// Get the size of the hmac tag.
    #[cfg_attr(feature = "hax-pv", hax_lib::pv_stub("nat_lit(0)"))]
    pub(crate) fn hmac_tag_len(&self) -> usize {
        self.hash_len()
    }
}

/// Get an empty key of the correct size.
pub(crate) fn zero_key(alg: &HashAlgorithm) -> Bytes {
    Bytes::zeroes(alg.hash_len())
}

/// AEAD Algorithms for Bertie
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum AeadAlgorithm {
    Chacha20Poly1305,
    Aes128Gcm,
    Aes256Gcm,
}

impl AeadAlgorithm {
    /// Get the key length of the AEAD algorithm in bytes.
    #[cfg_attr(feature = "hax-pv", hax_lib::pv_stub("nat_lit(0)"))]
    pub(crate) fn key_len(&self) -> usize {
        match self {
            AeadAlgorithm::Chacha20Poly1305 => 32,
            AeadAlgorithm::Aes128Gcm => 16,
            AeadAlgorithm::Aes256Gcm => 32,
        }
    }

    /// Get the length of the IV for this algorithm.
    #[cfg_attr(feature = "hax-pv", hax_lib::pv_stub("nat_lit(0)"))]
    pub(crate) fn iv_len(self) -> usize {
        match self {
            AeadAlgorithm::Chacha20Poly1305 => 12,
            AeadAlgorithm::Aes128Gcm => 12,
            AeadAlgorithm::Aes256Gcm => 12,
        }
    }
}

/// Signature schemes for Bertie.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum SignatureScheme {
    RsaPssRsaSha256,
    EcdsaSecp256r1Sha256,
    ED25519,
}

/// Bertie KEM schemes.
///
/// This includes ECDH curves.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum KemScheme {
    X25519,
    Secp256r1,
    X448,
    Secp384r1,
    Secp521r1,
    X25519Kyber768Draft00,
    X25519MlKem768,
}

/// The algorithms for Bertie.
///
/// Note that this is more than the TLS 1.3 ciphersuite. It contains all
/// necessary cryptographic algorithms and options.
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Algorithms {
    pub(crate) hash: HashAlgorithm,
    pub(crate) aead: AeadAlgorithm,
    pub(crate) signature: SignatureScheme,
    pub(crate) kem: KemScheme,
    pub(crate) psk_mode: bool,
    pub(crate) zero_rtt: bool,
}

#[hax_lib::attributes]
impl Algorithms {
    /// Create a new [`Algorithms`] object for the TLS 1.3 ciphersuite.
    pub const fn new(
        hash: HashAlgorithm,
        aead: AeadAlgorithm,
        sig: SignatureScheme,
        kem: KemScheme,
        psk: bool,
        zero_rtt: bool,
    ) -> Self {
        Self {
            hash,
            aead,
            signature: sig,
            kem,
            psk_mode: psk,
            zero_rtt,
        }
    }

    /// Get the [`HashAlgorithm`].
    pub fn hash(&self) -> HashAlgorithm {
        self.hash
    }

    /// Get the [`AeadAlgorithm`].
    pub fn aead(&self) -> AeadAlgorithm {
        self.aead
    }

    /// Get the [`SignatureAlgorithm`].
    pub fn signature(&self) -> SignatureScheme {
        self.signature
    }

    /// Get the [`KemScheme`].
    pub fn kem(&self) -> KemScheme {
        self.kem
    }

    /// Returns `true` when using the PSK mode and `false` otherwise.
    pub fn psk_mode(&self) -> bool {
        self.psk_mode
    }

    /// Returns `true` when using zero rtt and `false` otherwise.
    pub fn zero_rtt(&self) -> bool {
        self.zero_rtt
    }

    /// Returns the TLS ciphersuite for the given algorithm when it is supported, or
    /// a [`TLSError`] otherwise.
    #[hax_lib::ensures(|result| match result {
                                    Ok(b) => b.len() == 2,
                                    Err(_) => true})]
    pub(crate) fn ciphersuite(&self) -> Result<Bytes, TLSError> {
        match (self.hash, self.aead) {
            (HashAlgorithm::SHA256, AeadAlgorithm::Aes128Gcm) => Ok([0x13, 0x01].into()),
            (HashAlgorithm::SHA384, AeadAlgorithm::Aes256Gcm) => Ok([0x13, 0x02].into()),
            (HashAlgorithm::SHA256, AeadAlgorithm::Chacha20Poly1305) => Ok([0x13, 0x03].into()),
            _ => tlserr(UNSUPPORTED_ALGORITHM),
        }
    }

    /// Returns the curve id for the given algorithm when it is supported, or a [`TLSError`]
    /// otherwise.
    #[inline(always)]
    #[hax_lib::ensures(|result| match result {
        Ok(b) => b.len() == 2,
        Err(_) => true})]
    pub(crate) fn supported_group(&self) -> Result<Bytes, TLSError> {
        match self.kem() {
            KemScheme::X25519 => Ok([0x00, 0x1D].into()),
            KemScheme::Secp256r1 => Ok([0x00, 0x17].into()),
            KemScheme::X448 => tlserr(UNSUPPORTED_ALGORITHM),
            KemScheme::Secp384r1 => tlserr(UNSUPPORTED_ALGORITHM),
            KemScheme::Secp521r1 => tlserr(UNSUPPORTED_ALGORITHM),
            KemScheme::X25519Kyber768Draft00 => Ok([0x63, 0x99].into()),
            KemScheme::X25519MlKem768 => Ok([0x11, 0xec].into()),
        }
    }

    /// Returns the signature id for the given algorithm when it is supported, or a
    ///  [`TLSError`] otherwise.
    #[hax_lib::ensures(|result| match result {
        Ok(b) => b.len() == 2,
        Err(_) => true})]
    pub(crate) fn signature_algorithm(&self) -> Result<Bytes, TLSError> {
        match self.signature() {
            SignatureScheme::RsaPssRsaSha256 => Ok([0x08, 0x04].into()),
            SignatureScheme::EcdsaSecp256r1Sha256 => Ok([0x04, 0x03].into()),
            SignatureScheme::ED25519 => tlserr(UNSUPPORTED_ALGORITHM),
        }
    }

    /// Check the ciphersuite in `bytes` against this ciphersuite.
    #[hax_lib::ensures(|result| match result {
                                    Result::Ok(len) => bytes.len() >= len && len < 65538,
                                    _ => true
                                })]
    pub(crate) fn check(&self, bytes: &[U8]) -> Result<usize, TLSError> {
        let len = length_u16_encoded(bytes)?;
        let cs = self.ciphersuite()?;
        let csl = &bytes[2..2 + len];
        check_mem(cs.as_raw(), csl)?;
        Ok(len + 2)
    }
}

#[hax_lib::opaque]
impl TryFrom<&str> for Algorithms {
    type Error = Error;

    /// Get the ciphersuite from a string description.
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519" => {
                Ok(SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519)
            }
            "SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519" => {
                Ok(SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519)
            }
            "SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256" => {
                Ok(SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256)
            }
            "SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256" => {
                Ok(SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256)
            }
            "SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519Kyber768Draft00" => {
                Ok(SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519Kyber768Draft00)
            }
            "SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519MLKEM768" => {
                Ok(SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519MlKem768)
            }
            _ => Err(Error::UnknownCiphersuite(format!(
                "Invalid ciphersuite description: {}",
                s
            ))),
        }
    }
}

impl Display for Algorithms {
    fn fmt(&self, f: &mut crate::std::fmt::Formatter<'_>) -> crate::std::fmt::Result {
        write!(
            f,
            "TLS_{:?}_{:?} w/ {:?} | {:?}",
            self.aead, self.hash, self.signature, self.kem
        )
    }
}

/// `TLS_CHACHA20_POLY1305_SHA256` + x25519 + EcDSA P256 SHA256.
pub const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::X25519,
    false,
    false,
);

/// `TLS_CHACHA20_POLY1305_SHA256` + X25519Kyber768Draft00 + EcDSA P256 SHA256.
pub const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519Kyber768Draft00: Algorithms =
    Algorithms::new(
        HashAlgorithm::SHA256,
        AeadAlgorithm::Chacha20Poly1305,
        SignatureScheme::EcdsaSecp256r1Sha256,
        KemScheme::X25519Kyber768Draft00,
        false,
        false,
    );

/// `TLS_CHACHA20_POLY1305_SHA256` + X25519MlKem768 + EcDSA P256 SHA256.
pub const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519MlKem768: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::X25519MlKem768,
    false,
    false,
);

/// `TLS_CHACHA20_POLY1305_SHA256` + x25519 + RSA PSS SHA256.
pub const SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::X25519,
    false,
    false,
);

/// `TLS_CHACHA20_POLY1305_SHA256` + P256 + EcDSA P256 SHA256.
pub const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::Secp256r1,
    false,
    false,
);

/// `TLS_CHACHA20_POLY1305_SHA256` + P256 + RSA PSS SHA256.
pub const SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::Secp256r1,
    false,
    false,
);
