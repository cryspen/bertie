use libcrux::{
    kem::{Ct, PrivateKey, PublicKey},
    signature::rsa_pss::{RsaPssKeySize, RsaPssPublicKey},
    *,
};
use rand::{CryptoRng, RngCore};

use crate::tls13utils::{
    eq, tlserr, Bytes, TLSError, CRYPTO_ERROR, INVALID_SIGNATURE, UNSUPPORTED_ALGORITHM,
};

pub(crate) type Random = Bytes; //was [U8;32]
pub type Entropy = Bytes;
pub type SignatureKey = Bytes;
pub(crate) type PSK = Bytes;
pub(crate) type Key = Bytes;
pub(crate) type MacKey = Bytes;
pub(crate) type KemPk = Bytes;
pub(crate) type KemSk = Bytes;
pub(crate) type HMAC = Bytes;
pub(crate) type Digest = Bytes;
pub(crate) type AeadKey = Bytes;
pub(crate) type AeadIV = Bytes;
pub(crate) type AeadKeyIV = (Bytes, Bytes);
pub(crate) type VerificationKey = Bytes;
pub(crate) type RsaVerificationKey = (Bytes, Bytes); // N, e

#[derive(Debug)]
pub(crate) enum PublicVerificationKey {
    EcDsa(VerificationKey),  // Uncompressed point 0x04...
    Rsa(RsaVerificationKey), // N, e
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum HashAlgorithm {
    SHA256,
    SHA384,
    SHA512,
}

pub(crate) fn to_libcrux_hash_alg(alg: &HashAlgorithm) -> Result<digest::Algorithm, TLSError> {
    match alg {
        HashAlgorithm::SHA256 => Ok(digest::Algorithm::Sha256),
        HashAlgorithm::SHA384 => Ok(digest::Algorithm::Sha384),
        HashAlgorithm::SHA512 => Ok(digest::Algorithm::Sha512),
    }
}

pub(crate) fn hash(alg: &HashAlgorithm, data: &Bytes) -> Result<Bytes, TLSError> {
    Ok(digest::hash(to_libcrux_hash_alg(alg)?, &data.declassify()).into())
}

pub(crate) fn hash_len(alg: &HashAlgorithm) -> usize {
    match alg {
        HashAlgorithm::SHA256 => digest::digest_size(digest::Algorithm::Sha256),
        HashAlgorithm::SHA384 => digest::digest_size(digest::Algorithm::Sha384),
        HashAlgorithm::SHA512 => digest::digest_size(digest::Algorithm::Sha512),
    }
}

pub(crate) fn to_libcrux_hmac_alg(alg: &HashAlgorithm) -> Result<hmac::Algorithm, TLSError> {
    match alg {
        HashAlgorithm::SHA256 => Ok(hmac::Algorithm::Sha256),
        HashAlgorithm::SHA384 => Ok(hmac::Algorithm::Sha384),
        HashAlgorithm::SHA512 => Ok(hmac::Algorithm::Sha512),
    }
}
pub(crate) fn hmac_tag_len(alg: &HashAlgorithm) -> usize {
    hash_len(alg)
}

pub(crate) fn hmac_tag(alg: &HashAlgorithm, mk: &MacKey, input: &Bytes) -> Result<HMAC, TLSError> {
    Ok(hmac::hmac(
        to_libcrux_hmac_alg(alg)?,
        &mk.declassify(),
        &input.declassify(),
        None,
    )
    .into())
}

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

pub(crate) fn zero_key(alg: &HashAlgorithm) -> Bytes {
    Bytes::zeroes(hash_len(alg))
}

pub(crate) fn to_libcrux_hkdf_alg(alg: &HashAlgorithm) -> Result<hkdf::Algorithm, TLSError> {
    match alg {
        HashAlgorithm::SHA256 => Ok(hkdf::Algorithm::Sha256),
        HashAlgorithm::SHA384 => Ok(hkdf::Algorithm::Sha384),
        HashAlgorithm::SHA512 => Ok(hkdf::Algorithm::Sha512),
    }
}

pub(crate) fn hkdf_extract(
    alg: &HashAlgorithm,
    ikm: &Bytes,
    salt: &Bytes,
) -> Result<Bytes, TLSError> {
    Ok(hkdf::extract(
        to_libcrux_hkdf_alg(alg)?,
        salt.declassify(),
        ikm.declassify(),
    )
    .into())
}

pub(crate) fn hkdf_expand(
    alg: &HashAlgorithm,
    prk: &Bytes,
    info: &Bytes,
    len: usize,
) -> Result<Bytes, TLSError> {
    match hkdf::expand(
        to_libcrux_hkdf_alg(alg)?,
        prk.declassify(),
        info.declassify(),
        len,
    ) {
        Ok(x) => Ok(x.into()),
        Err(_) => tlserr(CRYPTO_ERROR),
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum AeadAlgorithm {
    Chacha20Poly1305,
    Aes128Gcm,
    Aes256Gcm,
}

pub(crate) fn to_libcrux_aead_alg(alg: &AeadAlgorithm) -> Result<aead::Algorithm, TLSError> {
    match alg {
        AeadAlgorithm::Chacha20Poly1305 => Ok(aead::Algorithm::Chacha20Poly1305),
        AeadAlgorithm::Aes128Gcm => Ok(aead::Algorithm::Aes128Gcm),
        AeadAlgorithm::Aes256Gcm => Ok(aead::Algorithm::Aes256Gcm),
    }
}
pub(crate) fn ae_key_len(alg: &AeadAlgorithm) -> usize {
    match alg {
        AeadAlgorithm::Chacha20Poly1305 => 32,
        AeadAlgorithm::Aes128Gcm => 16,
        AeadAlgorithm::Aes256Gcm => 32,
    }
}

pub(crate) fn ae_key_wrap(alg: &AeadAlgorithm, k: &AeadKey) -> Result<aead::Key, TLSError> {
    match alg {
        AeadAlgorithm::Chacha20Poly1305 => Ok(aead::Key::Chacha20Poly1305(aead::Chacha20Key(
            k.declassify_array()?,
        ))),
        AeadAlgorithm::Aes128Gcm => Ok(aead::Key::Aes128(aead::Aes128Key(k.declassify_array()?))),
        AeadAlgorithm::Aes256Gcm => Ok(aead::Key::Aes256(aead::Aes256Key(k.declassify_array()?))),
    }
}

pub(crate) fn ae_iv_len(alg: &AeadAlgorithm) -> usize {
    match alg {
        AeadAlgorithm::Chacha20Poly1305 => 12,
        AeadAlgorithm::Aes128Gcm => 12,
        AeadAlgorithm::Aes256Gcm => 12,
    }
}

pub(crate) fn aead_encrypt(
    alg: &AeadAlgorithm,
    k: &AeadKey,
    iv: &AeadIV,
    plain: &Bytes,
    aad: &Bytes,
) -> Result<Bytes, TLSError> {
    println!("enc key {}\n nonce: {}", k.to_hex(), iv.to_hex());
    let res = aead::encrypt_detached(
        &ae_key_wrap(alg, k)?,
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

pub(crate) fn aead_decrypt(
    alg: &AeadAlgorithm,
    k: &AeadKey,
    iv: &AeadIV,
    cip: &Bytes,
    aad: &Bytes,
) -> Result<Bytes, TLSError> {
    println!("dec key {}\n nonce: {}", k.to_hex(), iv.to_hex());
    let tag = cip.slice(cip.len() - 16, 16);
    let cip = cip.slice(0, cip.len() - 16);
    let tag: [u8; 16] = tag.declassify_array()?;
    let plain = aead::decrypt_detached(
        &ae_key_wrap(alg, k)?,
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

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum SignatureScheme {
    RsaPssRsaSha256,
    EcdsaSecp256r1Sha256,
    ED25519,
}

pub(crate) fn to_libcrux_sig_alg(a: &SignatureScheme) -> Result<signature::Algorithm, TLSError> {
    match a {
        SignatureScheme::RsaPssRsaSha256 => Ok(signature::Algorithm::RsaPss(
            signature::DigestAlgorithm::Sha256,
        )),
        SignatureScheme::ED25519 => Ok(signature::Algorithm::Ed25519),
        SignatureScheme::EcdsaSecp256r1Sha256 => Ok(signature::Algorithm::EcDsaP256(
            signature::DigestAlgorithm::Sha256,
        )),
    }
}

pub(crate) fn sign_rsa(
    sk: &Bytes,
    pk_modulus: &Bytes, // TODO: `cert` added to allow reconstructing full signing key for RSA-PSS. Rework this. (cf. issue #72)
    pk_exponent: &Bytes,
    cert_scheme: SignatureScheme,
    input: &Bytes,
    ent: Bytes, // TODO: Rework handling of randomness, `libcrux` may want an `impl CryptoRng + RngCore` instead of raw bytes. (cf. issue #73)
) -> Result<Bytes, TLSError> {
    // salt must be same length as digest output length
    let mut salt = [0u8; 32];
    rand::thread_rng().fill_bytes(&mut salt);

    if !matches!(cert_scheme, SignatureScheme::RsaPssRsaSha256) {
        return tlserr(CRYPTO_ERROR); // XXX: Right error type?
    }

    if !valid_rsa_exponent(pk_exponent.declassify()) {
        return tlserr(UNSUPPORTED_ALGORITHM);
    }

    let key_size = supported_rsa_key_size(&pk_modulus)?;

    let pk =
        RsaPssPublicKey::new(key_size, &pk_modulus.declassify()[1..]).map_err(|_| CRYPTO_ERROR)?;

    let sk = signature::rsa_pss::RsaPssPrivateKey::new(&pk, &sk.declassify())
        .map_err(|_| CRYPTO_ERROR)?;

    let sig = sk.sign(
        signature::DigestAlgorithm::Sha256,
        &salt,
        &input.declassify(),
    );
    sig.map(|sig| sig.as_bytes().into())
        .map_err(|_| CRYPTO_ERROR)
}

pub(crate) fn sign(
    alg: &SignatureScheme,
    sk: &Bytes,
    cert: &Bytes, // TODO: `cert` added to allow reconstructing full signing key for RSA-PSS. Rework this. (cf. issue #72)
    input: &Bytes,
    ent: Bytes, // TODO: Rework handling of randomness, `libcrux` may want an `impl CryptoRng + RngCore` instead of raw bytes. (cf. issue #73)
) -> Result<Bytes, TLSError> {
    let sig = match alg {
        SignatureScheme::EcdsaSecp256r1Sha256 => signature::sign(
            to_libcrux_sig_alg(alg)?,
            &input.declassify(),
            &sk.declassify(),
            &mut rand::thread_rng(),
        ),
        SignatureScheme::ED25519 => signature::sign(
            to_libcrux_sig_alg(alg)?,
            &input.declassify(),
            &sk.declassify(),
            &mut rand::thread_rng(),
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
        (SignatureScheme::RsaPssRsaSha256, PublicVerificationKey::Rsa((n, e))) => {
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

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum KemScheme {
    X25519,
    Secp256r1,
    X448,
    Secp384r1,
    Secp521r1,
}

pub(crate) fn kem_priv_len(alg: &KemScheme) -> usize {
    match alg {
        KemScheme::X25519 => 32,
        KemScheme::Secp256r1 => 32,
        _ => 64, //Check
    }
}

pub(crate) fn to_libcrux_kem_alg(alg: &KemScheme) -> Result<kem::Algorithm, TLSError> {
    match alg {
        KemScheme::X25519 => Ok(kem::Algorithm::X25519),
        KemScheme::Secp256r1 => Ok(kem::Algorithm::Secp256r1),
        _ => tlserr(UNSUPPORTED_ALGORITHM),
    }
}
pub(crate) fn kem_keygen(
    alg: &KemScheme,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<(KemSk, KemPk), TLSError> {
    let res = kem::key_gen(to_libcrux_kem_alg(alg)?, rng);
    match res {
        Ok((sk, pk)) => Ok((Bytes::from(sk.encode()), Bytes::from(pk.encode()))),
        Err(_) => tlserr(CRYPTO_ERROR),
    }
}

pub(crate) fn kem_encap(
    alg: &KemScheme,
    pk: &Bytes,
    ent: Bytes,
) -> Result<(Bytes, Bytes), TLSError> {
    let pk = PublicKey::decode(to_libcrux_kem_alg(alg)?, &pk.declassify()).unwrap();
    let res = kem::encapsulate(&pk, &mut rand::thread_rng());
    match res {
        Ok((gxy, gy)) => Ok((Bytes::from(gxy.encode()), Bytes::from(gy.encode()))),
        Err(_) => tlserr(CRYPTO_ERROR),
    }
}

pub(crate) fn kem_decap(alg: &KemScheme, ct: &Bytes, sk: &Bytes) -> Result<Bytes, TLSError> {
    let alg = to_libcrux_kem_alg(alg)?;
    let sk = PrivateKey::decode(alg, &sk.declassify()).unwrap();
    let ct = Ct::decode(alg, &ct.declassify()).unwrap();
    let res = kem::decapsulate(&ct, &sk);
    match res {
        Ok(x) => Ok(x.encode().into()),
        Err(_) => tlserr(CRYPTO_ERROR),
    }
}

// Algorithmns(ha, ae, sa, gn, psk_mode, zero_rtt)
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Algorithms(
    pub(crate) HashAlgorithm,
    pub(crate) AeadAlgorithm,
    pub(crate) SignatureScheme,
    pub(crate) KemScheme,
    pub(crate) bool,
    pub(crate) bool,
);

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
        Self(hash, aead, sig, kem, psk, zero_rtt)
    }

    pub fn hash_alg(&self) -> HashAlgorithm {
        self.0
    }
    pub fn aead_alg(&self) -> AeadAlgorithm {
        self.1
    }
    pub fn sig_alg(&self) -> SignatureScheme {
        self.2
    }
    pub fn kem_alg(&self) -> KemScheme {
        self.3
    }
    pub fn psk_mode(&self) -> bool {
        self.4
    }
    pub fn zero_rtt(&self) -> bool {
        self.5
    }
}
