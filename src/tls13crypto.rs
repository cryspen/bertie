use std::fmt::Display;

use libcrux::{
    kem::{Ct, PrivateKey, PublicKey},
    signature::rsa_pss::{RsaPssKeySize, RsaPssPrivateKey, RsaPssPublicKey},
    *,
};
use rand::{CryptoRng, RngCore};

use crate::tls13utils::{
    check_mem, eq, length_u16_encoded, tlserr, Bytes, Error, TLSError, CRYPTO_ERROR,
    INVALID_SIGNATURE, UNSUPPORTED_ALGORITHM,
};

pub(crate) type Random = Bytes;
pub type SignatureKey = Bytes;
pub(crate) type Psk = Bytes;
pub(crate) type Key = Bytes;
pub(crate) type MacKey = Bytes;
pub(crate) type KemPk = Bytes;
pub(crate) type KemSk = Bytes;
pub(crate) type Hmac = Bytes;
pub(crate) type Digest = Bytes;
pub(crate) type AeadIV = Bytes;
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
pub(crate) struct AeadKey {
    bytes: Bytes,
    alg: AeadAlgorithm,
}

impl AeadKey {
    /// Create a new AEAD key from the raw bytes and the algorithm.
    pub(crate) fn new(bytes: Bytes, alg: AeadAlgorithm) -> Self {
        Self { bytes, alg }
    }

    /// Convert a raw AEAD key into a usable libcrux key.
    ///
    /// This copies the key.
    fn as_libcrux_key(&self) -> Result<aead::Key, TLSError> {
        match self.alg {
            AeadAlgorithm::Chacha20Poly1305 => Ok(aead::Key::Chacha20Poly1305(aead::Chacha20Key(
                self.bytes.declassify_array()?,
            ))),
            AeadAlgorithm::Aes128Gcm => Ok(aead::Key::Aes128(aead::Aes128Key(
                self.bytes.declassify_array()?,
            ))),
            AeadAlgorithm::Aes256Gcm => Ok(aead::Key::Aes256(aead::Aes256Key(
                self.bytes.declassify_array()?,
            ))),
        }
    }

    /// Get the raw bytes of the key.
    #[cfg(test)]
    pub(crate) fn bytes(&self) -> &Bytes {
        &self.bytes
    }
}

/// An RSA public key.
#[derive(Debug)]
pub(crate) struct RsaVerificationKey {
    pub(crate) modulus: Bytes,
    pub(crate) exponent: Bytes,
}

/// Bertie public verification keys.
#[derive(Debug)]
pub(crate) enum PublicVerificationKey {
    EcDsa(VerificationKey),  // Uncompressed point 0x04...
    Rsa(RsaVerificationKey), // N, e
}

/// Bertie hash algorithms.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum HashAlgorithm {
    SHA256,
    SHA384,
    SHA512,
}

impl HashAlgorithm {
    /// Get the libcrux hash algorithm
    fn libcrux_algorithm(&self) -> Result<digest::Algorithm, TLSError> {
        match self {
            HashAlgorithm::SHA256 => Ok(digest::Algorithm::Sha256),
            HashAlgorithm::SHA384 => Ok(digest::Algorithm::Sha384),
            HashAlgorithm::SHA512 => Ok(digest::Algorithm::Sha512),
        }
    }

    /// Hash `data` with the given `algorithm`.
    ///
    /// Returns the digest or an [`TLSError`].
    pub(crate) fn hash(&self, data: &Bytes) -> Result<Bytes, TLSError> {
        Ok(digest::hash(self.libcrux_algorithm()?, &data.declassify()).into())
    }

    /// Get the size of the hash digest.
    pub(crate) fn hash_len(&self) -> usize {
        match self {
            HashAlgorithm::SHA256 => digest::digest_size(digest::Algorithm::Sha256),
            HashAlgorithm::SHA384 => digest::digest_size(digest::Algorithm::Sha384),
            HashAlgorithm::SHA512 => digest::digest_size(digest::Algorithm::Sha512),
        }
    }

    /// Get the libcrux hmac algorithm.
    fn hmac_algorithm(&self) -> Result<hmac::Algorithm, TLSError> {
        match self {
            HashAlgorithm::SHA256 => Ok(hmac::Algorithm::Sha256),
            HashAlgorithm::SHA384 => Ok(hmac::Algorithm::Sha384),
            HashAlgorithm::SHA512 => Ok(hmac::Algorithm::Sha512),
        }
    }

    /// Get the size of the hmac tag.
    pub(crate) fn hmac_tag_len(&self) -> usize {
        self.hash_len()
    }
}

/// Compute the HMAC tag.
///
/// Returns the tag [`Hmac`] or a [`TLSError`].
pub(crate) fn hmac_tag(alg: &HashAlgorithm, mk: &MacKey, input: &Bytes) -> Result<Hmac, TLSError> {
    Ok(hmac::hmac(
        alg.hmac_algorithm()?,
        &mk.declassify(),
        &input.declassify(),
        None,
    )
    .into())
}

/// Verify a given HMAC `tag`.
///
/// Returns `()` if successful or a [`TLSError`].
pub(crate) fn hmac_verify(
    alg: &HashAlgorithm,
    mk: &MacKey,
    input: &Bytes,
    tag: &Bytes,
) -> Result<(), TLSError> {
    if eq(&hmac_tag(alg, mk, input)?, tag) {
        Ok(())
    } else {
        tlserr(CRYPTO_ERROR)
    }
}

/// Get an empty key of the correct size.
pub(crate) fn zero_key(alg: &HashAlgorithm) -> Bytes {
    Bytes::zeroes(alg.hash_len())
}

/// Get the libcrux HKDF algorithm.
fn hkdf_algorithm(alg: &HashAlgorithm) -> Result<hkdf::Algorithm, TLSError> {
    match alg {
        HashAlgorithm::SHA256 => Ok(hkdf::Algorithm::Sha256),
        HashAlgorithm::SHA384 => Ok(hkdf::Algorithm::Sha384),
        HashAlgorithm::SHA512 => Ok(hkdf::Algorithm::Sha512),
    }
}

/// HKDF Extract.
///
/// Returns the result as [`Bytes`] or a [`TLSError`].
pub(crate) fn hkdf_extract(
    alg: &HashAlgorithm,
    ikm: &Bytes,
    salt: &Bytes,
) -> Result<Bytes, TLSError> {
    Ok(hkdf::extract(hkdf_algorithm(alg)?, salt.declassify(), ikm.declassify()).into())
}

/// HKDF Expand.
///
/// Returns the result as [`Bytes`] or a [`TLSError`].
pub(crate) fn hkdf_expand(
    alg: &HashAlgorithm,
    prk: &Bytes,
    info: &Bytes,
    len: usize,
) -> Result<Bytes, TLSError> {
    match hkdf::expand(
        hkdf_algorithm(alg)?,
        prk.declassify(),
        info.declassify(),
        len,
    ) {
        Ok(x) => Ok(x.into()),
        Err(_) => tlserr(CRYPTO_ERROR),
    }
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
    pub(crate) fn key_len(&self) -> usize {
        match self {
            AeadAlgorithm::Chacha20Poly1305 => 32,
            AeadAlgorithm::Aes128Gcm => 16,
            AeadAlgorithm::Aes256Gcm => 32,
        }
    }

    /// Get the length of the IV for this algorithm.
    pub(crate) fn iv_len(self) -> usize {
        match self {
            AeadAlgorithm::Chacha20Poly1305 => 12,
            AeadAlgorithm::Aes128Gcm => 12,
            AeadAlgorithm::Aes256Gcm => 12,
        }
    }
}

/// AEAD encrypt
pub(crate) fn aead_encrypt(
    k: &AeadKey,
    iv: &AeadIV,
    plain: &Bytes,
    aad: &Bytes,
) -> Result<Bytes, TLSError> {
    let res = aead::encrypt_detached(
        &k.as_libcrux_key()?,
        plain.declassify(),
        aead::Iv(iv.declassify_array()?),
        aad.declassify(),
    );
    match res {
        Ok((tag, cip)) => {
            let cipby: Bytes = cip.into();
            let tagby: Bytes = tag.as_ref().into();
            Ok(cipby.concat(&tagby))
        }
        Err(_) => tlserr(CRYPTO_ERROR),
    }
}

/// AEAD decrypt.
pub(crate) fn aead_decrypt(
    k: &AeadKey,
    iv: &AeadIV,
    cip: &Bytes,
    aad: &Bytes,
) -> Result<Bytes, TLSError> {
    // event!(Level::DEBUG, "AEAD decrypt with {:?}", k.alg);

    let tag = cip.slice(cip.len() - 16, 16);
    let cip = cip.slice(0, cip.len() - 16);
    let tag: [u8; 16] = tag.declassify_array()?;
    let plain = aead::decrypt_detached(
        &k.as_libcrux_key()?,
        cip.declassify(),
        aead::Iv(iv.declassify_array()?),
        aad.declassify(),
        &aead::Tag::from(tag),
    );
    match plain {
        Ok(plain) => Ok(plain.into()),
        Err(_) => tlserr(CRYPTO_ERROR),
    }
}

/// Signature schemes for Bertie.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum SignatureScheme {
    RsaPssRsaSha256,
    EcdsaSecp256r1Sha256,
    ED25519,
}

impl SignatureScheme {
    /// Get the libcrux signature algorithm from the [`SignatureScheme`].
    fn libcrux_scheme(&self) -> Result<signature::Algorithm, TLSError> {
        match self {
            SignatureScheme::RsaPssRsaSha256 => Ok(signature::Algorithm::RsaPss(
                signature::DigestAlgorithm::Sha256,
            )),
            SignatureScheme::ED25519 => Ok(signature::Algorithm::Ed25519),
            SignatureScheme::EcdsaSecp256r1Sha256 => Ok(signature::Algorithm::EcDsaP256(
                signature::DigestAlgorithm::Sha256,
            )),
        }
    }
}

/// Sign the `input` with the provided RSA key.
pub(crate) fn sign_rsa(
    sk: &Bytes,
    pk_modulus: &Bytes,
    pk_exponent: &Bytes,
    cert_scheme: SignatureScheme,
    input: &Bytes,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<Bytes, TLSError> {
    // salt must be same length as digest output length
    let mut salt = [0u8; 32];
    rng.fill_bytes(&mut salt);

    if !matches!(cert_scheme, SignatureScheme::RsaPssRsaSha256) {
        return tlserr(CRYPTO_ERROR); // XXX: Right error type?
    }

    if !valid_rsa_exponent(pk_exponent.declassify()) {
        return tlserr(UNSUPPORTED_ALGORITHM);
    }

    let key_size = supported_rsa_key_size(pk_modulus)?;
    let pk =
        RsaPssPublicKey::new(key_size, &pk_modulus.declassify()[1..]).map_err(|_| CRYPTO_ERROR)?;

    let sk = RsaPssPrivateKey::new(&pk, &sk.declassify()).map_err(|_| CRYPTO_ERROR)?;

    let msg = &input.declassify();
    let sig = sk.sign(signature::DigestAlgorithm::Sha256, &salt, msg);
    sig.map(|sig| sig.as_bytes().into())
        .map_err(|_| CRYPTO_ERROR)
}

/// Sign the bytes in `input` with the signature key `sk` and `algorithm`.
pub(crate) fn sign(
    algorithm: &SignatureScheme,
    sk: &Bytes,
    input: &Bytes,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<Bytes, TLSError> {
    let sig = match algorithm {
        SignatureScheme::EcdsaSecp256r1Sha256 => signature::sign(
            algorithm.libcrux_scheme()?,
            &input.declassify(),
            &sk.declassify(),
            rng,
        ),
        SignatureScheme::ED25519 => signature::sign(
            algorithm.libcrux_scheme()?,
            &input.declassify(),
            &sk.declassify(),
            rng,
        ),
        SignatureScheme::RsaPssRsaSha256 => {
            panic!("wrong function, use sign_rsa")
        }
    };
    match sig {
        Ok(signature::Signature::Ed25519(sig)) => Ok(sig.as_bytes().into()),
        Ok(signature::Signature::EcDsaP256(sig)) => {
            let (r, s) = sig.as_bytes();
            Ok(Bytes::from(r).concat(&Bytes::from(s)))
        }
        Ok(signature::Signature::RsaPss(sig)) => panic!("wrong function, use sign_rsa"),
        Err(_) => tlserr(CRYPTO_ERROR),
    }
}

/// Verify the `input` bytes against the provided `signature`.
///
/// Return `Ok(())` if the verification succeeds, and a [`TLSError`] otherwise.
pub(crate) fn verify(
    alg: &SignatureScheme,
    pk: &PublicVerificationKey,
    input: &Bytes,
    sig: &Bytes,
) -> Result<(), TLSError> {
    match (alg, pk) {
        (SignatureScheme::ED25519, PublicVerificationKey::EcDsa(pk)) => {
            let res = signature::verify(
                &input.declassify(),
                &signature::Signature::Ed25519(signature::Ed25519Signature::from_bytes(
                    sig.declassify_array()?,
                )),
                &pk.declassify(),
            );
            match res {
                Ok(res) => Ok(res),
                Err(_) => tlserr(INVALID_SIGNATURE),
            }
        }
        (SignatureScheme::EcdsaSecp256r1Sha256, PublicVerificationKey::EcDsa(pk)) => {
            let res = signature::verify(
                &input.declassify(),
                &signature::Signature::EcDsaP256(signature::EcDsaP256Signature::from_bytes(
                    sig.declassify_array()?,
                    signature::Algorithm::EcDsaP256(signature::DigestAlgorithm::Sha256),
                )),
                &pk.declassify(),
            );
            match res {
                Ok(res) => Ok(res),
                Err(_) => tlserr(INVALID_SIGNATURE),
            }
        }
        (
            SignatureScheme::RsaPssRsaSha256,
            PublicVerificationKey::Rsa(RsaVerificationKey {
                modulus: n,
                exponent: e,
            }),
        ) => {
            if !valid_rsa_exponent(e.declassify()) {
                tlserr(UNSUPPORTED_ALGORITHM)
            } else {
                let key_size = supported_rsa_key_size(n)?;
                let pk = RsaPssPublicKey::new(key_size, &n.declassify()[1..])
                    .map_err(|_| CRYPTO_ERROR)?;
                let res = pk.verify(
                    signature::DigestAlgorithm::Sha256,
                    &sig.declassify().into(),
                    &input.declassify(),
                    32, // salt must be same length as digest ouput length
                );
                match res {
                    Ok(res) => Ok(res),
                    Err(_) => tlserr(CRYPTO_ERROR),
                }
            }
        }
        _ => tlserr(UNSUPPORTED_ALGORITHM),
    }
}

/// Determine if given modulus conforms to one of the key sizes supported by
/// `libcrux`.
fn supported_rsa_key_size(n: &Bytes) -> Result<RsaPssKeySize, u8> {
    let key_size = match n.len() as u16 {
        // The format includes an extra 0-byte in front to disambiguate from negative numbers
        257 => RsaPssKeySize::N2048,
        385 => RsaPssKeySize::N3072,
        513 => RsaPssKeySize::N4096,
        769 => RsaPssKeySize::N6144,
        1025 => RsaPssKeySize::N8192,
        _ => return tlserr(UNSUPPORTED_ALGORITHM),
    };
    Ok(key_size)
}

/// Determine if given public exponent is supported by `libcrux`, i.e. whether
///  `e == 0x010001`.
fn valid_rsa_exponent(e: Vec<u8>) -> bool {
    e.len() == 3 && e[0] == 0x1 && e[1] == 0x0 && e[2] == 0x1
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
}

impl KemScheme {
    /// Get the libcrux algorithm for this [`KemScheme`].
    fn libcrux_algorithm(self) -> Result<kem::Algorithm, TLSError> {
        match self {
            KemScheme::X25519 => Ok(kem::Algorithm::X25519),
            KemScheme::Secp256r1 => Ok(kem::Algorithm::Secp256r1),
            _ => tlserr(UNSUPPORTED_ALGORITHM),
        }
    }
}

/// Generate a new KEM key pair.
pub(crate) fn kem_keygen(
    alg: KemScheme,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<(KemSk, KemPk), TLSError> {
    let res = kem::key_gen(alg.libcrux_algorithm()?, rng);
    match res {
        Ok((sk, pk)) => {
            // event!(
            //     Level::TRACE,
            //     "Generated KEM public key: {}",
            //     Bytes::from(pk.encode()).as_hex()
            // );
            Ok((
                Bytes::from(sk.encode()),
                encoding_prefix(alg).concat(&Bytes::from(pk.encode())),
            ))
        }
        Err(_) => tlserr(CRYPTO_ERROR),
    }
}

/// Note that the `encode` in libcrux currently returns the raw
/// concatenation of bytes. We have to prepend the 0x04 for
/// uncompressed points on NIST curves.
fn encoding_prefix(alg: KemScheme) -> Bytes {
    if alg == KemScheme::Secp256r1 || alg == KemScheme::Secp384r1 || alg == KemScheme::Secp521r1 {
        Bytes::from([0x04])
    } else {
        Bytes::new()
    }
}

/// Note that the `encode` in libcrux operates on the raw
/// concatenation of bytes. We have to work with uncompressed NIST points here.
fn into_raw(alg: KemScheme, point: Bytes) -> Bytes {
    if alg == KemScheme::Secp256r1 || alg == KemScheme::Secp384r1 || alg == KemScheme::Secp521r1 {
        point.slice_range(1..point.len())
    } else {
        point
    }
}

/// KEM encapsulation
pub(crate) fn kem_encap(
    alg: KemScheme,
    pk: &Bytes,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<(Bytes, Bytes), TLSError> {
    // event!(Level::DEBUG, "KEM Encaps with {alg:?}");
    // event!(Level::TRACE, "  pk:  {}", pk.as_hex());

    let pk = into_raw(alg, pk.clone());
    let pk = PublicKey::decode(alg.libcrux_algorithm()?, &pk.declassify()).unwrap();
    let res = kem::encapsulate(&pk, rng);
    match res {
        Ok((shared_secret, ct)) => {
            let ct = encoding_prefix(alg).concat(&Bytes::from(ct.encode()));
            let shared_secret = to_shared_secret(alg, Bytes::from(shared_secret.encode()));
            // event!(Level::TRACE, "  output ciphertext: {}", ct.as_hex());
            Ok((shared_secret, ct))
        }
        Err(_) => tlserr(CRYPTO_ERROR),
    }
}

/// We only want the X coordinate for points on NIST curves.
fn to_shared_secret(alg: KemScheme, shared_secret: Bytes) -> Bytes {
    if alg == KemScheme::Secp256r1 {
        shared_secret.slice_range(0..32)
    } else if alg == KemScheme::Secp384r1 || alg == KemScheme::Secp521r1 {
        unimplemented!("not supported yet");
    } else {
        shared_secret
    }
}

/// KEM decapsulation
pub(crate) fn kem_decap(alg: KemScheme, ct: &Bytes, sk: &Bytes) -> Result<Bytes, TLSError> {
    // event!(Level::DEBUG, "KEM Decaps with {alg:?}");
    // event!(Level::TRACE, "  with ciphertext: {}", ct.as_hex());

    let librux_algorithm = alg.libcrux_algorithm()?;
    let sk = PrivateKey::decode(librux_algorithm, &sk.declassify()).unwrap();
    let ct = into_raw(alg, ct.clone()).declassify();
    let ct = Ct::decode(librux_algorithm, &ct).unwrap();
    let res = kem::decapsulate(&ct, &sk);
    match res {
        Ok(shared_secret) => {
            let shared_secret: Bytes = shared_secret.encode().into();
            // event!(Level::TRACE, "  shared secret: {}", shared_secret.as_hex());
            let shared_secret = to_shared_secret(alg, shared_secret);
            Ok(shared_secret)
        }
        Err(_) => tlserr(CRYPTO_ERROR),
    }
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
    pub(crate) fn supported_group(&self) -> Result<Bytes, TLSError> {
        match self.kem() {
            KemScheme::X25519 => Ok([0x00, 0x1D].into()),
            KemScheme::Secp256r1 => Ok([0x00, 0x17].into()),
            KemScheme::X448 => tlserr(UNSUPPORTED_ALGORITHM),
            KemScheme::Secp384r1 => tlserr(UNSUPPORTED_ALGORITHM),
            KemScheme::Secp521r1 => tlserr(UNSUPPORTED_ALGORITHM),
        }
    }

    /// Returns the signature id for the given algorithm when it is supported, or a
    ///  [`TLSError`] otherwise.
    pub(crate) fn signature_algorithm(&self) -> Result<Bytes, TLSError> {
        match self.signature() {
            SignatureScheme::RsaPssRsaSha256 => Ok([0x08, 0x04].into()),
            SignatureScheme::EcdsaSecp256r1Sha256 => Ok([0x04, 0x03].into()),
            SignatureScheme::ED25519 => tlserr(UNSUPPORTED_ALGORITHM),
        }
    }

    /// Check the ciphersuite in `bytes` against this ciphersuite.
    pub(crate) fn check(&self, bytes: &Bytes) -> Result<usize, TLSError> {
        let len = length_u16_encoded(bytes)?;
        let cs = self.ciphersuite()?;
        let csl = bytes.slice_range(2..2 + len);
        check_mem(&cs, &csl)?;
        Ok(len + 2)
    }
}

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
            "SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256" => {
                Ok(SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256)
            }
            "SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519" => {
                Ok(SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519)
            }
            "SHA256_Aes128Gcm_RsaPssRsaSha256_P256" => Ok(SHA256_Aes128Gcm_RsaPssRsaSha256_P256),
            "SHA256_Aes128Gcm_RsaPssRsaSha256_X25519" => {
                Ok(SHA256_Aes128Gcm_RsaPssRsaSha256_X25519)
            }
            "SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256" => {
                Ok(SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256)
            }
            "SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519" => {
                Ok(SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519)
            }
            "SHA384_Aes256Gcm_RsaPssRsaSha256_P256" => Ok(SHA384_Aes256Gcm_RsaPssRsaSha256_P256),
            "SHA384_Aes256Gcm_RsaPssRsaSha256_X25519" => {
                Ok(SHA384_Aes256Gcm_RsaPssRsaSha256_X25519)
            }
            _ => Err(Error::UnknownCiphersuite(format!(
                "Invalid ciphersuite description: {}",
                s
            ))),
        }
    }
}

impl Display for Algorithms {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "TLS_{:?}_{:?} w/ {:?} | {:?}",
            self.aead, self.hash, self.signature, self.kem
        )
    }
}

/// `TLS_AES_128_GCM_SHA256`
/// with
/// * x25519 for key exchange
/// * EcDSA P256 SHA256 for signatures
pub const SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::X25519,
    false,
    false,
);

/// `TLS_CHACHA20_POLY1305_SHA256`
/// with
/// * x25519 for key exchange
/// * EcDSA P256 SHA256 for signatures
pub const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::X25519,
    false,
    false,
);

/// `TLS_CHACHA20_POLY1305_SHA256`
/// with
/// * x25519 for key exchange
/// * RSA PSS SHA256 for signatures
pub const SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::X25519,
    false,
    false,
);

/// `TLS_CHACHA20_POLY1305_SHA256`
/// with
/// * P256 for key exchange
/// * EcDSA P256 SHA256 for signatures
pub const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::Secp256r1,
    false,
    false,
);

/// `TLS_CHACHA20_POLY1305_SHA256`
/// with
/// * P256 for key exchange
/// * RSA PSSS SHA256 for signatures
pub const SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::Secp256r1,
    false,
    false,
);

/// `TLS_AES_128_GCM_SHA256`
/// with
/// * P256 for key exchange
/// * EcDSA P256 SHA256 for signatures
pub const SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::Secp256r1,
    false,
    false,
);

/// `TLS_AES_128_GCM_SHA256`
/// with
/// * P256 for key exchange
/// * RSA PSS SHA256 for signatures
pub const SHA256_Aes128Gcm_RsaPssRsaSha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::Secp256r1,
    false,
    false,
);

/// `TLS_AES_128_GCM_SHA256`
/// with
/// * x25519 for key exchange
/// * RSA PSS SHA256 for signatures
pub const SHA256_Aes128Gcm_RsaPssRsaSha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::X25519,
    false,
    false,
);

/// `TLS_AES_256_GCM_SHA384`
/// with
/// * x25519 for key exchange
/// * RSA PSS SHA256 for signatures
pub const SHA384_Aes256Gcm_RsaPssRsaSha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA384,
    AeadAlgorithm::Aes256Gcm,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::X25519,
    false,
    false,
);

/// `TLS_AES_256_GCM_SHA384`
/// with
/// * x25519 for key exchange
/// * EcDSA P256 SHA256 for signatures
pub const SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms::new(
    HashAlgorithm::SHA384,
    AeadAlgorithm::Aes256Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::X25519,
    false,
    false,
);

/// `TLS_AES_256_GCM_SHA384`
/// with
/// * P256 for key exchange
/// * RSA PSS SHA256 for signatures
pub const SHA384_Aes256Gcm_RsaPssRsaSha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA384,
    AeadAlgorithm::Aes256Gcm,
    SignatureScheme::RsaPssRsaSha256,
    KemScheme::Secp256r1,
    false,
    false,
);

/// `TLS_AES_256_GCM_SHA384`
/// with
/// * P256 for key exchange
/// * EcDSA P256 SHA256 for signatures
pub const SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256: Algorithms = Algorithms::new(
    HashAlgorithm::SHA384,
    AeadAlgorithm::Aes256Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::Secp256r1,
    false,
    false,
);
