#[cfg(feature = "hax-pv")]
use hax_lib::{proverif, pv_constructor};

use rand::CryptoRng;

use crate::std::{fmt::Display, format, vec, vec::Vec};

use crate::tls13utils::{
    bytes2, check_mem, eq, length_u16_encoded, tlserr, Bytes, Error, TLSError, CRYPTO_ERROR,
    INCORRECT_ARRAY_LENGTH, INVALID_SIGNATURE, U8, UNSUPPORTED_ALGORITHM,
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
    _alg: AeadAlgorithm,
}

impl AeadKey {
    /// Create a new AEAD key from the raw bytes and the algorithm.
    pub(crate) fn new(bytes: Bytes, _alg: AeadAlgorithm) -> Self {
        Self { bytes, _alg }
    }

    /// Get the raw bytes of the key.
    #[cfg(test)]
    pub(crate) fn bytes(&self) -> &Bytes {
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
        "type $:{PublicVerificationKey}.

fun $:{PublicVerificationKey}_to_bitstring(
      $:{PublicVerificationKey}
    )
    : bitstring [typeConverter].
fun $:{PublicVerificationKey}_from_bitstring(bitstring)
    : $:{PublicVerificationKey} [typeConverter].
const $:{PublicVerificationKey}_default_value: $:{PublicVerificationKey}.
letfun $:{PublicVerificationKey}_default() =
       $:{PublicVerificationKey}_default_value.
letfun $:{PublicVerificationKey}_err() =
       let x = construct_fail() in $:{PublicVerificationKey}_default_value.
fun ${PublicVerificationKey::EcDsa}($:{Bytes}
    )
    : $:{PublicVerificationKey} [data].

fun ${PublicVerificationKey::Rsa}(
      $:{RsaVerificationKey}
    )
    : $:{PublicVerificationKey} [data].
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

/// Hash `data` with the given `algorithm`.
///
/// Returns the digest or an [`TLSError`].
#[cfg_attr(feature = "hax-pv", pv_constructor)]
pub(crate) fn hash(ha: &HashAlgorithm, data: &Bytes) -> Result<Bytes, TLSError> {
    Ok(libcrux_hash(*ha, &data.declassify()).into())
}

#[hax_lib::attributes]
impl HashAlgorithm {
    /// Get the size of the hash digest.
    #[hax_lib::ensures(|result| result <= 64)]
    #[cfg_attr(feature = "hax-pv", proverif::replace_body("0"))]
    pub(crate) fn hash_len(&self) -> usize {
        match self {
            HashAlgorithm::SHA256 => 32,
            HashAlgorithm::SHA384 => 48,
            HashAlgorithm::SHA512 => 64,
        }
    }

    /// Get the size of the hmac tag.
    #[cfg_attr(feature = "hax-pv", hax_lib::proverif::replace_body("0"))]
    pub(crate) fn hmac_tag_len(&self) -> usize {
        self.hash_len()
    }
}

/// Compute the HMAC tag.
///
/// Returns the tag [`Hmac`] or a [`TLSError`].
#[hax_lib::pv_constructor]
pub(crate) fn hmac_tag(alg: &HashAlgorithm, mk: &MacKey, input: &Bytes) -> Result<Hmac, TLSError> {
    Ok(libcrux_hmac(*alg, &mk.declassify(), &input.declassify()).into())
}

/// Verify a given HMAC `tag`.
///
/// Returns `()` if successful or a [`TLSError`].
#[cfg_attr(
    feature = "hax-pv",
    proverif::replace(
        "
reduc
  forall
        alg : $:{HashAlgorithm},
         mk : $:{Bytes},
      input : $:{Bytes};
        ${hmac_verify}(
            alg,
            mk,
            input,
            ${hmac_tag}(alg, mk, input)
         ) = ()."
    )
)]
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

/// HKDF Extract.
///
/// Returns the result as [`Bytes`] or a [`TLSError`].
#[hax_lib::pv_constructor]
pub(crate) fn hkdf_extract(
    alg: &HashAlgorithm,
    ikm: &Bytes,
    salt: &Bytes,
) -> Result<Bytes, TLSError> {
    match libcrux_hkdf_extract(*alg, &salt.declassify(), &ikm.declassify()) {
        Some(prk) => Ok(prk.into()),
        None => tlserr(CRYPTO_ERROR),
    }
}

/// HKDF Expand.
///
/// Returns the result as [`Bytes`] or a [`TLSError`].
#[hax_lib::pv_constructor]
pub(crate) fn hkdf_expand(
    alg: &HashAlgorithm,
    prk: &Bytes,
    info: &Bytes,
    len: usize,
) -> Result<Bytes, TLSError> {
    match libcrux_hkdf_expand(*alg, &prk.declassify(), &info.declassify(), len) {
        Some(okm) => Ok(okm.into()),
        None => tlserr(CRYPTO_ERROR),
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
    #[cfg_attr(feature = "hax-pv", proverif::replace_body("0"))]
    pub(crate) fn key_len(&self) -> usize {
        match self {
            AeadAlgorithm::Chacha20Poly1305 => 32,
            AeadAlgorithm::Aes128Gcm => 16,
            AeadAlgorithm::Aes256Gcm => 32,
        }
    }

    /// Get the length of the IV for this algorithm.
    #[cfg_attr(feature = "hax-pv", proverif::replace_body("0"))]
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
    // We only support Chacha20Poly1305 right now.
    let key = k
        .bytes
        .declassify_array()
        .map_err(|_| INCORRECT_ARRAY_LENGTH)?;

    let iv = iv.declassify_array()?;
    match libcrux_chacha20poly1305_encrypt(&key, &iv, &aad.declassify(), &plain.declassify()) {
        Some(ctxt) => Ok(ctxt.into()),
        None => tlserr(CRYPTO_ERROR),
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

    if cip.len() < 16 {
        return tlserr(CRYPTO_ERROR);
    }
    let tag = cip.slice(cip.len() - 16, 16);
    let ctxt = cip.slice(0, cip.len() - 16);
    let tag: [u8; 16] = tag.declassify_array()?;
    let key = k
        .bytes
        .declassify_array()
        .map_err(|_| INCORRECT_ARRAY_LENGTH)?;
    let iv = iv.declassify_array()?;
    match libcrux_chacha20poly1305_decrypt(&key, &iv, &aad.declassify(), &ctxt.declassify(), &tag) {
        Some(plain) => Ok(plain.into()),
        None => tlserr(CRYPTO_ERROR),
    }
}

/// Signature schemes for Bertie.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum SignatureScheme {
    RsaPssRsaSha256,
    EcdsaSecp256r1Sha256,
    ED25519,
}

/// Sign the `input` with the provided RSA key.
pub(crate) fn sign_rsa(
    sk: &Bytes,
    pk_modulus: &Bytes,
    pk_exponent: &Bytes,
    cert_scheme: SignatureScheme,
    input: &Bytes,
    rng: &mut impl CryptoRng,
) -> Result<Bytes, TLSError> {
    if !matches!(cert_scheme, SignatureScheme::RsaPssRsaSha256) {
        return tlserr(CRYPTO_ERROR); // XXX: Right error type?
    }

    if !valid_rsa_exponent(pk_exponent.declassify()) {
        return tlserr(UNSUPPORTED_ALGORITHM);
    }

    supported_rsa_key_size(pk_modulus)?;
    let modulus = pk_modulus.declassify();
    let signature =
        libcrux_rsa_pss_sign(&modulus[1..], &sk.declassify(), &input.declassify(), rng)?;
    Ok(signature.into())
}

/// Sign the bytes in `input` with the signature key `sk` and `algorithm`.
#[cfg_attr(
    feature = "hax-pv",
    proverif::before(
        "fun extern__sign_inner(
         $:{SignatureScheme},
         $:{Bytes}, (* sk *)
         $:{Bytes}  (* input *)
     )
     : $:{Bytes}."
    )
)]
#[cfg_attr(
    feature = "hax-pv",
    proverif::replace_body(
        "(extern__sign_inner(
              algorithm,
              sk,
              input
          )
       )"
    )
)]
pub(crate) fn sign(
    algorithm: &SignatureScheme,
    sk: &Bytes,
    input: &Bytes,
    rng: &mut impl CryptoRng,
) -> Result<Bytes, TLSError> {
    match algorithm {
        SignatureScheme::EcdsaSecp256r1Sha256 => {
            let sk = sk.declassify_array()?;
            Ok(libcrux_ecdsa_p256_sign(&sk, &input.declassify(), rng)?.into())
        }
        SignatureScheme::ED25519 => {
            let sk = sk.declassify_array()?;
            Ok(libcrux_ed25519_sign(&sk, &input.declassify())?.into())
        }
        SignatureScheme::RsaPssRsaSha256 => tlserr(UNSUPPORTED_ALGORITHM),
    }
}

/// Verify the `input` bytes against the provided `signature`.
///
/// Return `Ok(())` if the verification succeeds, and a [`TLSError`] otherwise.
#[cfg_attr(
    feature = "hax-pv",
    proverif::replace(
        "
fun extern__vk_from_sk($:{Bytes}): $:{PublicVerificationKey}.

fun extern__sign_inner_rsa(
                 $:{Bytes}, (* sk *)
                 $:{Bytes}  (* input *)
             )
             : $:{Bytes}.

fun ${verify}(
            $:{SignatureScheme}, 
            $:{PublicVerificationKey},
            $:{Bytes}, (* input *)
            $:{Bytes}  (* sig *)
        )
    : bitstring

  reduc forall
                     sk: $:{Bytes},
                  input: $:{Bytes};

        ${verify}(
            ${SignatureScheme::RsaPssRsaSha256},
            extern__vk_from_sk(sk),
            input,
            extern__sign_inner_rsa(
                sk,
                input
            )
        )
        = ()

  otherwise forall
                sk                   : $:{Bytes},
                input                : $:{Bytes};

        ${verify}(
            ${SignatureScheme::EcdsaSecp256r1Sha256},
            extern__vk_from_sk(sk),
            input,
            extern__sign_inner(
                ${SignatureScheme::EcdsaSecp256r1Sha256},
                sk,
                input
            )
        )
        = ()."
    )
)]
pub(crate) fn verify(
    alg: &SignatureScheme,
    pk: &PublicVerificationKey,
    input: &Bytes,
    sig: &Bytes,
) -> Result<(), TLSError> {
    match (alg, pk) {
        (SignatureScheme::ED25519, PublicVerificationKey::EcDsa(pk)) => {
            let pk = pk.declassify_array()?;
            let sig = sig.declassify_array()?;
            libcrux_ed25519_verify(&pk, &input.declassify(), &sig)
        }

        (SignatureScheme::EcdsaSecp256r1Sha256, PublicVerificationKey::EcDsa(pk)) => {
            let sig = sig.declassify_array()?;
            let pk = pk.declassify_array()?;
            libcrux_ecdsa_p256_verify(&pk, &input.declassify(), &sig)
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
                supported_rsa_key_size(n)?;
                let n_vec = n.declassify();
                libcrux_rsa_pss_verify(&n_vec[1..], &input.declassify(), &sig.declassify())
            }
        }
        _ => tlserr(UNSUPPORTED_ALGORITHM),
    }
}

/// Determine if given modulus conforms to one of the key sizes supported by
/// `libcrux`.
#[hax_lib::ensures(|result| match result {
    Ok(()) => n.len() >= 257,
    _ => true })]
fn supported_rsa_key_size(n: &Bytes) -> Result<(), u8> {
    match n.len() {
        // The format includes an extra 0-byte in front to disambiguate from negative numbers
        257 | 385 | 513 | 769 | 1025 => Ok(()),
        _ => tlserr(UNSUPPORTED_ALGORITHM),
    }
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
    X25519MlKem768,
}

/// Length of a raw public key, without the [`encoding_prefix`].
fn raw_public_key_len(alg: KemScheme) -> Result<usize, TLSError> {
    match alg {
        KemScheme::X25519 => Ok(32),
        KemScheme::Secp256r1 => Ok(64),
        KemScheme::X25519MlKem768 => Ok(1216),
        _ => tlserr(UNSUPPORTED_ALGORITHM),
    }
}

/// Length of a private key.
fn private_key_len(alg: KemScheme) -> Result<usize, TLSError> {
    match alg {
        KemScheme::X25519 | KemScheme::Secp256r1 => Ok(32),
        KemScheme::X25519MlKem768 => Ok(2432),
        _ => tlserr(UNSUPPORTED_ALGORITHM),
    }
}

/// Generate a new KEM key pair.
#[cfg_attr(
    feature = "hax-pv",
    proverif::before("fun extern__kem_pk_from_sk($:{Bytes}): $:{Bytes}.")
)]
#[cfg_attr(
    feature = "hax-pv",
    proverif::replace_body(
        "(new kem_sk: $:{Bytes};
       let kem_pk = extern__kem_pk_from_sk(kem_sk) in
       (kem_sk, kem_pk))"
    )
)]
pub(crate) fn kem_keygen(
    alg: KemScheme,
    rng: &mut impl CryptoRng,
) -> Result<(KemSk, KemPk), TLSError> {
    raw_public_key_len(alg)?;
    match libcrux_kem_keygen(alg, rng) {
        Some((sk, pk)) => Ok((
            Bytes::from(sk),
            encoding_prefix(alg).concat(Bytes::from(pk)),
        )),
        None => tlserr(CRYPTO_ERROR),
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
    if (alg == KemScheme::Secp256r1 || alg == KemScheme::Secp384r1 || alg == KemScheme::Secp521r1)
        && point.len() >= 1
    {
        point.slice_range(1..point.len())
    } else {
        point
    }
}

/// KEM encapsulation
#[cfg_attr(
    feature = "hax-pv",
    proverif::before("fun extern__kem_encapsulation($:{Bytes}, $:{Bytes}): $:{Bytes}.")
)]
#[cfg_attr(
    feature = "hax-pv",
    proverif::replace_body(
        "(new shared_secret: $:{Bytes};
          let ct = extern__kem_encapsulation(pk, shared_secret) in
          (shared_secret, ct))"
    )
)]
pub(crate) fn kem_encap(
    alg: KemScheme,
    pk: &Bytes,
    rng: &mut impl CryptoRng,
) -> Result<(Bytes, Bytes), TLSError> {
    // event!(Level::DEBUG, "KEM Encaps with {alg:?}");
    // event!(Level::TRACE, "  pk:  {}", pk.as_hex());

    let pk = into_raw(alg, pk.clone());
    if pk.len() != raw_public_key_len(alg)? {
        return tlserr(CRYPTO_ERROR);
    }
    match libcrux_kem_encap(alg, &pk.declassify(), rng) {
        Some((shared_secret, ct)) => {
            let ct = encoding_prefix(alg).concat(Bytes::from(ct));
            let shared_secret = to_shared_secret(alg, Bytes::from(shared_secret))?;
            Ok((shared_secret, ct))
        }
        None => tlserr(CRYPTO_ERROR),
    }
}

/// We only want the X coordinate for points on NIST curves.
fn to_shared_secret(alg: KemScheme, shared_secret: Bytes) -> Result<Bytes, TLSError> {
    match alg {
        KemScheme::Secp256r1 => {
            if shared_secret.len() >= 32 {
                Ok(shared_secret.slice_range(0..32))
            } else {
                tlserr(CRYPTO_ERROR)
            }
        }
        KemScheme::X25519 | KemScheme::X25519MlKem768 => Ok(shared_secret),
        _ => tlserr(UNSUPPORTED_ALGORITHM),
    }
}

/// KEM decapsulation
#[cfg_attr(
    feature = "hax-pv",
    proverif::replace(
        "reduc forall alg: $:{KemScheme}, kem_sk: $:{Bytes}, shared_secret: $:{Bytes};
     ${kem_decap}(
     alg, extern__kem_encapsulation(extern__kem_pk_from_sk(kem_sk), shared_secret), kem_sk
     ) = shared_secret."
    )
)]
pub(crate) fn kem_decap(alg: KemScheme, ct: &Bytes, sk: &Bytes) -> Result<Bytes, TLSError> {
    // event!(Level::DEBUG, "KEM Decaps with {alg:?}");
    // event!(Level::TRACE, "  with ciphertext: {}", ct.as_hex());

    if sk.len() != private_key_len(alg)? {
        return tlserr(CRYPTO_ERROR);
    }
    let ct = into_raw(alg, ct.clone()).declassify();
    match libcrux_kem_decap(alg, &ct, &sk.declassify()) {
        Some(shared_secret) => to_shared_secret(alg, Bytes::from(shared_secret)),
        None => tlserr(CRYPTO_ERROR),
    }
}

// The calls into libcrux. hax extracts only the contracts of these functions,
// so they are trusted not to panic on inputs that satisfy them.
#[hax_lib::exclude]
fn libcrux_sha2(ha: HashAlgorithm) -> libcrux_sha2::Algorithm {
    match ha {
        HashAlgorithm::SHA256 => libcrux_sha2::Algorithm::Sha256,
        HashAlgorithm::SHA384 => libcrux_sha2::Algorithm::Sha384,
        HashAlgorithm::SHA512 => libcrux_sha2::Algorithm::Sha512,
    }
}

#[hax_lib::exclude]
fn libcrux_kem_algorithm(alg: KemScheme) -> Option<libcrux_kem::Algorithm> {
    match alg {
        KemScheme::X25519 => Some(libcrux_kem::Algorithm::X25519),
        KemScheme::Secp256r1 => Some(libcrux_kem::Algorithm::Secp256r1),
        KemScheme::X25519MlKem768 => Some(libcrux_kem::Algorithm::X25519MlKem768Draft00),
        _ => None,
    }
}

#[hax_lib::opaque]
#[hax_lib::ensures(|result| result.len() == ha.hash_len())]
fn libcrux_hash(ha: HashAlgorithm, data: &[u8]) -> Vec<u8> {
    let mut digest = vec![0u8; ha.hash_len()];
    libcrux_sha2(ha).hash(data, &mut digest);
    digest
}

#[hax_lib::opaque]
#[hax_lib::ensures(|result| result.len() == ha.hash_len())]
fn libcrux_hmac(ha: HashAlgorithm, key: &[u8], data: &[u8]) -> Vec<u8> {
    let alg = match ha {
        HashAlgorithm::SHA256 => libcrux_hmac::Algorithm::Sha256,
        HashAlgorithm::SHA384 => libcrux_hmac::Algorithm::Sha384,
        HashAlgorithm::SHA512 => libcrux_hmac::Algorithm::Sha512,
    };
    libcrux_hmac::hmac(alg, key, data, None)
}

#[hax_lib::exclude]
fn libcrux_hkdf_algorithm(ha: HashAlgorithm) -> libcrux_hkdf::Algorithm {
    match ha {
        HashAlgorithm::SHA256 => libcrux_hkdf::Algorithm::Sha256,
        HashAlgorithm::SHA384 => libcrux_hkdf::Algorithm::Sha384,
        HashAlgorithm::SHA512 => libcrux_hkdf::Algorithm::Sha512,
    }
}

#[hax_lib::opaque]
#[hax_lib::ensures(|result| match result {
    Some(prk) => prk.len() == ha.hash_len(),
    None => true })]
fn libcrux_hkdf_extract(ha: HashAlgorithm, salt: &[u8], ikm: &[u8]) -> Option<Vec<u8>> {
    let mut prk = vec![0u8; ha.hash_len()];
    libcrux_hkdf::extract(libcrux_hkdf_algorithm(ha), &mut prk, salt, ikm).ok()?;
    Some(prk)
}

#[hax_lib::opaque]
#[hax_lib::ensures(|result| match result {
    Some(okm) => okm.len() == len,
    None => true })]
fn libcrux_hkdf_expand(ha: HashAlgorithm, prk: &[u8], info: &[u8], len: usize) -> Option<Vec<u8>> {
    let mut okm = vec![0u8; len];
    libcrux_hkdf::expand(libcrux_hkdf_algorithm(ha), &mut okm, prk, info).ok()?;
    Some(okm)
}

/// Returns the ciphertext followed by the 16-byte tag.
#[hax_lib::opaque]
fn libcrux_chacha20poly1305_encrypt(
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    ptxt: &[u8],
) -> Option<Vec<u8>> {
    let mut ctxt = vec![0u8; ptxt.len()];
    let mut tag = [0u8; 16];
    libcrux_chacha20poly1305::encrypt_detached(key, ptxt, &mut ctxt, &mut tag, aad, nonce).ok()?;
    ctxt.extend_from_slice(&tag);
    Some(ctxt)
}

#[hax_lib::opaque]
fn libcrux_chacha20poly1305_decrypt(
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    ctxt: &[u8],
    tag: &[u8; 16],
) -> Option<Vec<u8>> {
    let mut ptxt = vec![0u8; ctxt.len()];
    libcrux_chacha20poly1305::decrypt_detached(key, &mut ptxt, ctxt, tag, aad, nonce).ok()?;
    Some(ptxt)
}

/// Returns the signature `r || s`.
#[hax_lib::opaque]
fn libcrux_ecdsa_p256_sign(
    sk: &[u8; 32],
    msg: &[u8],
    rng: &mut impl CryptoRng,
) -> Result<Vec<u8>, TLSError> {
    let sk =
        libcrux_ecdsa::p256::PrivateKey::try_from(&sk[..]).map_err(|_| INCORRECT_ARRAY_LENGTH)?;
    let sig =
        libcrux_ecdsa::p256::rand::sign(libcrux_ecdsa::DigestAlgorithm::Sha256, msg, &sk, rng)
            .map_err(|_| CRYPTO_ERROR)?;
    let (r, s) = sig.as_bytes();
    let mut out = r.to_vec();
    out.extend_from_slice(s);
    Ok(out)
}

#[hax_lib::opaque]
fn libcrux_ed25519_sign(sk: &[u8; 32], msg: &[u8]) -> Result<Vec<u8>, TLSError> {
    libcrux_ed25519::sign(msg, sk)
        .map(|s| s.to_vec())
        .map_err(|_| CRYPTO_ERROR)
}

#[hax_lib::opaque]
fn libcrux_ed25519_verify(pk: &[u8; 32], msg: &[u8], sig: &[u8; 64]) -> Result<(), TLSError> {
    libcrux_ed25519::verify(msg, pk, sig).map_err(|_| INVALID_SIGNATURE)
}

#[hax_lib::opaque]
fn libcrux_ecdsa_p256_verify(pk: &[u8; 64], msg: &[u8], sig: &[u8; 64]) -> Result<(), TLSError> {
    let pk = libcrux_ecdsa::p256::PublicKey::try_from(pk).map_err(|_| CRYPTO_ERROR)?;
    libcrux_ecdsa::p256::verify(
        libcrux_ecdsa::DigestAlgorithm::Sha256,
        msg,
        &libcrux_ecdsa::p256::Signature::from_bytes(*sig),
        &pk,
    )
    .map_err(|_| INVALID_SIGNATURE)
}

/// RSA-PSS with SHA-256 and a 32-byte salt. `modulus` excludes the leading
/// zero byte.
#[hax_lib::opaque]
fn libcrux_rsa_pss_sign(
    modulus: &[u8],
    sk: &[u8],
    msg: &[u8],
    rng: &mut impl CryptoRng,
) -> Result<Vec<u8>, TLSError> {
    let mut salt = [0u8; 32];
    rng.fill_bytes(&mut salt);
    let sk = libcrux_rsa::VarLenPrivateKey::from_components(modulus, sk)
        .map_err(|_| INCORRECT_ARRAY_LENGTH)?;
    let mut signature = [0u8; 512];
    libcrux_rsa::sign_varlen(
        libcrux_rsa::DigestAlgorithm::Sha2_256,
        &sk,
        msg,
        &salt,
        &mut signature,
    )
    .map_err(|_| CRYPTO_ERROR)?;
    Ok(signature.to_vec())
}

/// RSA-PSS with SHA-256 and a 32-byte salt. `modulus` excludes the leading
/// zero byte.
#[hax_lib::opaque]
fn libcrux_rsa_pss_verify(modulus: &[u8], msg: &[u8], sig: &[u8]) -> Result<(), TLSError> {
    let pk = libcrux_rsa::VarLenPublicKey::try_from(modulus).map_err(|_| INCORRECT_ARRAY_LENGTH)?;
    libcrux_rsa::verify_varlen(libcrux_rsa::DigestAlgorithm::Sha2_256, &pk, msg, 32, sig)
        .map_err(|_| CRYPTO_ERROR)
}

/// Returns the private key and the raw public key.
#[hax_lib::opaque]
fn libcrux_kem_keygen(alg: KemScheme, rng: &mut impl CryptoRng) -> Option<(Vec<u8>, Vec<u8>)> {
    let (sk, pk) = libcrux_kem::key_gen(libcrux_kem_algorithm(alg)?, rng).ok()?;
    Some((sk.encode(), pk.encode()))
}

/// Returns the shared secret and the raw ciphertext.
#[hax_lib::opaque]
#[hax_lib::requires(match raw_public_key_len(alg) {
    Ok(len) => pk.len() == len,
    Err(_) => false })]
fn libcrux_kem_encap(
    alg: KemScheme,
    pk: &[u8],
    rng: &mut impl CryptoRng,
) -> Option<(Vec<u8>, Vec<u8>)> {
    let alg = libcrux_kem_algorithm(alg)?;
    let pk = libcrux_kem::PublicKey::decode(alg, pk).ok()?;
    let (shared_secret, ct) = pk.encapsulate(rng).ok()?;
    Some((shared_secret.encode(), ct.encode()))
}

#[hax_lib::opaque]
#[hax_lib::requires(match private_key_len(alg) {
    Ok(len) => sk.len() == len,
    Err(_) => false })]
fn libcrux_kem_decap(alg: KemScheme, ct: &[u8], sk: &[u8]) -> Option<Vec<u8>> {
    let alg = libcrux_kem_algorithm(alg)?;
    let sk = libcrux_kem::PrivateKey::decode(alg, sk).ok()?;
    let ct = libcrux_kem::Ct::decode(alg, ct).ok()?;
    let shared_secret = ct.decapsulate(&sk).ok()?;
    Some(shared_secret.encode())
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
            (HashAlgorithm::SHA256, AeadAlgorithm::Aes128Gcm) => Ok(bytes2(0x13, 0x01)),
            (HashAlgorithm::SHA384, AeadAlgorithm::Aes256Gcm) => Ok(bytes2(0x13, 0x02)),
            (HashAlgorithm::SHA256, AeadAlgorithm::Chacha20Poly1305) => Ok(bytes2(0x13, 0x03)),
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
            KemScheme::X25519 => Ok(bytes2(0x00, 0x1D)),
            KemScheme::Secp256r1 => Ok(bytes2(0x00, 0x17)),
            KemScheme::X448 => tlserr(UNSUPPORTED_ALGORITHM),
            KemScheme::Secp384r1 => tlserr(UNSUPPORTED_ALGORITHM),
            KemScheme::Secp521r1 => tlserr(UNSUPPORTED_ALGORITHM),
            KemScheme::X25519MlKem768 => Ok(bytes2(0x11, 0xec)), // cf. https://datatracker.ietf.org/doc/draft-kwiatkowski-tls-ecdhe-mlkem/
        }
    }

    /// Returns the signature id for the given algorithm when it is supported, or a
    ///  [`TLSError`] otherwise.
    #[hax_lib::ensures(|result| match result {
        Ok(b) => b.len() == 2,
        Err(_) => true})]
    pub(crate) fn signature_algorithm(&self) -> Result<Bytes, TLSError> {
        match self.signature() {
            SignatureScheme::RsaPssRsaSha256 => Ok(bytes2(0x08, 0x04)),
            SignatureScheme::EcdsaSecp256r1Sha256 => Ok(bytes2(0x04, 0x03)),
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
            // "SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256" => {
            //     Ok(SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256)
            // }
            // "SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519" => {
            //     Ok(SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519)
            // }
            // "SHA256_Aes128Gcm_RsaPssRsaSha256_P256" => Ok(SHA256_Aes128Gcm_RsaPssRsaSha256_P256),
            // "SHA256_Aes128Gcm_RsaPssRsaSha256_X25519" => {
            //     Ok(SHA256_Aes128Gcm_RsaPssRsaSha256_X25519)
            // }
            // "SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256" => {
            //     Ok(SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256)
            // }
            // "SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519" => {
            //     Ok(SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519)
            // }
            // "SHA384_Aes256Gcm_RsaPssRsaSha256_P256" => Ok(SHA384_Aes256Gcm_RsaPssRsaSha256_P256),
            // "SHA384_Aes256Gcm_RsaPssRsaSha256_X25519" => {
            //     Ok(SHA384_Aes256Gcm_RsaPssRsaSha256_X25519)
            // }
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

#[hax_lib::exclude]
impl Display for Algorithms {
    fn fmt(&self, f: &mut crate::std::fmt::Formatter<'_>) -> crate::std::fmt::Result {
        write!(
            f,
            "TLS_{:?}_{:?} w/ {:?} | {:?}",
            self.aead, self.hash, self.signature, self.kem
        )
    }
}

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
/// * X25519MlKem768 for key exchange (cf. https://datatracker.ietf.org/doc/draft-kwiatkowski-tls-ecdhe-mlkem/)
/// * EcDSA P256 SHA256 for signatures
pub const SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519MlKem768: Algorithms = Algorithms::new(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    KemScheme::X25519MlKem768,
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

// We don't support AES right now.

// /// `TLS_AES_128_GCM_SHA256`
// /// with
// /// * x25519 for key exchange
// /// * EcDSA P256 SHA256 for signatures
// pub const SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms::new(
//     HashAlgorithm::SHA256,
//     AeadAlgorithm::Aes128Gcm,
//     SignatureScheme::EcdsaSecp256r1Sha256,
//     KemScheme::X25519,
//     false,
//     false,
// );

// /// `TLS_AES_128_GCM_SHA256`
// /// with
// /// * P256 for key exchange
// /// * EcDSA P256 SHA256 for signatures
// pub const SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256: Algorithms = Algorithms::new(
//     HashAlgorithm::SHA256,
//     AeadAlgorithm::Aes128Gcm,
//     SignatureScheme::EcdsaSecp256r1Sha256,
//     KemScheme::Secp256r1,
//     false,
//     false,
// );

// /// `TLS_AES_128_GCM_SHA256`
// /// with
// /// * P256 for key exchange
// /// * RSA PSS SHA256 for signatures
// pub const SHA256_Aes128Gcm_RsaPssRsaSha256_P256: Algorithms = Algorithms::new(
//     HashAlgorithm::SHA256,
//     AeadAlgorithm::Aes128Gcm,
//     SignatureScheme::RsaPssRsaSha256,
//     KemScheme::Secp256r1,
//     false,
//     false,
// );

// /// `TLS_AES_128_GCM_SHA256`
// /// with
// /// * x25519 for key exchange
// /// * RSA PSS SHA256 for signatures
// pub const SHA256_Aes128Gcm_RsaPssRsaSha256_X25519: Algorithms = Algorithms::new(
//     HashAlgorithm::SHA256,
//     AeadAlgorithm::Aes128Gcm,
//     SignatureScheme::RsaPssRsaSha256,
//     KemScheme::X25519,
//     false,
//     false,
// );

// /// `TLS_AES_256_GCM_SHA384`
// /// with
// /// * x25519 for key exchange
// /// * RSA PSS SHA256 for signatures
// pub const SHA384_Aes256Gcm_RsaPssRsaSha256_X25519: Algorithms = Algorithms::new(
//     HashAlgorithm::SHA384,
//     AeadAlgorithm::Aes256Gcm,
//     SignatureScheme::RsaPssRsaSha256,
//     KemScheme::X25519,
//     false,
//     false,
// );

// /// `TLS_AES_256_GCM_SHA384`
// /// with
// /// * x25519 for key exchange
// /// * EcDSA P256 SHA256 for signatures
// pub const SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519: Algorithms = Algorithms::new(
//     HashAlgorithm::SHA384,
//     AeadAlgorithm::Aes256Gcm,
//     SignatureScheme::EcdsaSecp256r1Sha256,
//     KemScheme::X25519,
//     false,
//     false,
// );

// /// `TLS_AES_256_GCM_SHA384`
// /// with
// /// * P256 for key exchange
// /// * RSA PSS SHA256 for signatures
// pub const SHA384_Aes256Gcm_RsaPssRsaSha256_P256: Algorithms = Algorithms::new(
//     HashAlgorithm::SHA384,
//     AeadAlgorithm::Aes256Gcm,
//     SignatureScheme::RsaPssRsaSha256,
//     KemScheme::Secp256r1,
//     false,
//     false,
// );

// /// `TLS_AES_256_GCM_SHA384`
// /// with
// /// * P256 for key exchange
// /// * EcDSA P256 SHA256 for signatures
// pub const SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256: Algorithms = Algorithms::new(
//     HashAlgorithm::SHA384,
//     AeadAlgorithm::Aes256Gcm,
//     SignatureScheme::EcdsaSecp256r1Sha256,
//     KemScheme::Secp256r1,
//     false,
//     false,
// );

#[cfg(test)]
mod tests {
    use super::*;

    const KEMS: [KemScheme; 3] = [
        KemScheme::X25519,
        KemScheme::Secp256r1,
        KemScheme::X25519MlKem768,
    ];

    #[test]
    fn kem_rejects_malformed_inputs() {
        let mut rng = rand::rng();
        for alg in KEMS {
            let (sk, pk) = kem_keygen(alg, &mut rng).unwrap();
            for len in [0, 1, 31, 33, 1183, 1184, 1217] {
                let short: Bytes = vec![U8(4); len].into();
                assert!(kem_encap(alg, &short, &mut rng).is_err());
                assert!(kem_decap(alg, &short, &sk).is_err());
            }
            let (ss, ct) = kem_encap(alg, &pk, &mut rng).unwrap();
            assert!(eq(&kem_decap(alg, &ct, &sk).unwrap(), &ss));
            assert!(kem_decap(alg, &ct, &Bytes::new()).is_err());
        }
    }

    #[test]
    fn aead_decrypt_rejects_short_ciphertext() {
        let key = AeadKey::new(vec![U8(0); 32].into(), AeadAlgorithm::Chacha20Poly1305);
        let iv: Bytes = vec![U8(0); 12].into();
        for len in [0, 1, 15] {
            let cip: Bytes = vec![U8(0); len].into();
            assert!(aead_decrypt(&key, &iv, &cip, &Bytes::new()).is_err());
        }
    }

    #[test]
    fn sign_rejects_rsa() {
        let mut rng = rand::rng();
        let sk: Bytes = vec![U8(0); 32].into();
        let input: Bytes = vec![U8(0); 32].into();
        assert!(sign(&SignatureScheme::RsaPssRsaSha256, &sk, &input, &mut rng).is_err());
    }
}
