//! Cryptographic provider trait surface for Bertie.
//!
//! Bertie's TLS code dispatches every cryptographic primitive through a
//! [`BertieCrypto`] implementation rather than calling the underlying libcrux
//! crates directly. The default in-tree [`LibcruxBertieProvider`] preserves
//! the historical behaviour; the `bertie-trace-adapter` sibling crate (in the
//! `symbolic-trace` workspace) ships a tracing wrapper that records every
//! call into a [`symbolic_trace::session::TracerSession`].
//!
//! The randomness side stays modeled after `rand::CryptoRng`: the
//! [`BertieRand`] marker subtrait is satisfied automatically by anything that
//! is already a `rand::CryptoRng`, so existing test RNGs continue to work
//! without changes. The trace adapter ships a `TracingRand` that records each
//! `fill_bytes` draw and forwards to an inner `CryptoRng`.

use libcrux_chacha20poly1305::{decrypt_detached, encrypt_detached};
use libcrux_ecdsa::DigestAlgorithm as EcDsaDigestAlgorithm;
use libcrux_hkdf::{expand, extract, Algorithm as HkdfAlgorithm};
use libcrux_hmac::{hmac, Algorithm as HmacAlgorithm};
use libcrux_kem::{Ct, PrivateKey, PublicKey};
use libcrux_rsa::{
    sign_varlen, verify_varlen, DigestAlgorithm as RsaDigestAlgorithm, VarLenPrivateKey,
    VarLenPublicKey,
};
use libcrux_sha2::Algorithm as Sha2Algorithm;
use rand::CryptoRng;

use crate::std::vec;
use crate::std::vec::Vec;
use crate::tls13crypto::{
    AeadIV, AeadKey, HashAlgorithm, Hmac, KemPk, KemScheme, KemSk, MacKey, PublicVerificationKey,
    RsaVerificationKey, SignatureScheme,
};
use crate::tls13utils::{
    eq, Bytes, TLSError, CRYPTO_ERROR, INCORRECT_ARRAY_LENGTH, INVALID_SIGNATURE,
    UNSUPPORTED_ALGORITHM,
};

/// Marker subtrait of `rand::CryptoRng`. Implemented automatically for every
/// `CryptoRng`. Bertie's crypto trait takes `&mut impl BertieRand` (rather than
/// `&mut impl CryptoRng` directly) so adapter wrappers like `TracingRand` show
/// up as the expected randomness boundary.
pub trait BertieRand: CryptoRng {}
impl<T: CryptoRng + ?Sized> BertieRand for T {}

/// Bertie's cryptographic primitive surface.
///
/// Every primitive Bertie's TLS handshake / record layer calls passes through
/// this trait. The default [`LibcruxBertieProvider`] implementation preserves
/// historical behaviour bit-for-bit; tracing wrappers can layer instrumentation
/// over any inner provider that also implements [`BertieCrypto`].
pub trait BertieCrypto {
    fn hash(&self, ha: &HashAlgorithm, data: &Bytes) -> Result<Bytes, TLSError>;

    fn hmac_tag(&self, alg: &HashAlgorithm, mk: &MacKey, input: &Bytes)
        -> Result<Hmac, TLSError>;

    fn hmac_verify(
        &self,
        alg: &HashAlgorithm,
        mk: &MacKey,
        input: &Bytes,
        tag: &Bytes,
    ) -> Result<(), TLSError> {
        if eq(&self.hmac_tag(alg, mk, input)?, tag) {
            Ok(())
        } else {
            Err(CRYPTO_ERROR)
        }
    }

    fn hkdf_extract(
        &self,
        alg: &HashAlgorithm,
        ikm: &Bytes,
        salt: &Bytes,
    ) -> Result<Bytes, TLSError>;

    fn hkdf_expand(
        &self,
        alg: &HashAlgorithm,
        prk: &Bytes,
        info: &Bytes,
        len: usize,
    ) -> Result<Bytes, TLSError>;

    fn aead_encrypt(
        &self,
        key: &AeadKey,
        iv: &AeadIV,
        plain: &Bytes,
        aad: &Bytes,
    ) -> Result<Bytes, TLSError>;

    fn aead_decrypt(
        &self,
        key: &AeadKey,
        iv: &AeadIV,
        cip: &Bytes,
        aad: &Bytes,
    ) -> Result<Bytes, TLSError>;

    fn sign_rsa<R: BertieRand>(
        &self,
        sk: &Bytes,
        pk_modulus: &Bytes,
        pk_exponent: &Bytes,
        cert_scheme: SignatureScheme,
        input: &Bytes,
        rng: &mut R,
    ) -> Result<Bytes, TLSError>;

    fn sign<R: BertieRand>(
        &self,
        algorithm: &SignatureScheme,
        sk: &Bytes,
        input: &Bytes,
        rng: &mut R,
    ) -> Result<Bytes, TLSError>;

    fn verify(
        &self,
        alg: &SignatureScheme,
        pk: &PublicVerificationKey,
        input: &Bytes,
        sig: &Bytes,
    ) -> Result<(), TLSError>;

    fn kem_keygen<R: BertieRand>(
        &self,
        alg: KemScheme,
        rng: &mut R,
    ) -> Result<(KemSk, KemPk), TLSError>;

    fn kem_encap<R: BertieRand>(
        &self,
        alg: KemScheme,
        pk: &Bytes,
        rng: &mut R,
    ) -> Result<(Bytes, Bytes), TLSError>;

    fn kem_decap(&self, alg: KemScheme, ct: &Bytes, sk: &Bytes) -> Result<Bytes, TLSError>;
}

/// The default Bertie crypto provider: dispatches everything to the libcrux
/// crates that Bertie historically depended on. Preserves bit-for-bit
/// behaviour from before the provider refactor.
#[derive(Debug, Clone, Copy, Default)]
pub struct LibcruxBertieProvider;

impl LibcruxBertieProvider {
    pub const fn new() -> Self {
        Self
    }
}

fn libcrux_hash_alg(alg: &HashAlgorithm) -> Result<Sha2Algorithm, TLSError> {
    match alg {
        HashAlgorithm::SHA256 => Ok(Sha2Algorithm::Sha256),
        HashAlgorithm::SHA384 => Ok(Sha2Algorithm::Sha384),
        HashAlgorithm::SHA512 => Ok(Sha2Algorithm::Sha512),
    }
}

fn libcrux_hmac_alg(alg: &HashAlgorithm) -> Result<HmacAlgorithm, TLSError> {
    match alg {
        HashAlgorithm::SHA256 => Ok(HmacAlgorithm::Sha256),
        HashAlgorithm::SHA384 => Ok(HmacAlgorithm::Sha384),
        HashAlgorithm::SHA512 => Ok(HmacAlgorithm::Sha512),
    }
}

fn libcrux_hkdf_alg(alg: &HashAlgorithm) -> Result<HkdfAlgorithm, TLSError> {
    match alg {
        HashAlgorithm::SHA256 => Ok(HkdfAlgorithm::Sha256),
        HashAlgorithm::SHA384 => Ok(HkdfAlgorithm::Sha384),
        HashAlgorithm::SHA512 => Ok(HkdfAlgorithm::Sha512),
    }
}

fn libcrux_kem_alg(alg: KemScheme) -> Result<libcrux_kem::Algorithm, TLSError> {
    match alg {
        KemScheme::X25519 => Ok(libcrux_kem::Algorithm::X25519),
        KemScheme::Secp256r1 => Ok(libcrux_kem::Algorithm::Secp256r1),
        KemScheme::X25519Kyber768Draft00 => Ok(libcrux_kem::Algorithm::X25519Kyber768Draft00),
        KemScheme::X25519MlKem768 => Ok(libcrux_kem::Algorithm::X25519MlKem768Draft00),
        _ => Err(UNSUPPORTED_ALGORITHM),
    }
}

fn encoding_prefix(alg: KemScheme) -> Bytes {
    if alg == KemScheme::Secp256r1 || alg == KemScheme::Secp384r1 || alg == KemScheme::Secp521r1 {
        Bytes::from([0x04])
    } else {
        Bytes::new()
    }
}

fn into_raw(alg: KemScheme, point: Bytes) -> Bytes {
    if alg == KemScheme::Secp256r1 || alg == KemScheme::Secp384r1 || alg == KemScheme::Secp521r1 {
        point.slice_range(1..point.len())
    } else {
        point
    }
}

fn to_shared_secret(alg: KemScheme, shared_secret: Bytes) -> Bytes {
    if alg == KemScheme::Secp256r1 {
        shared_secret.slice_range(0..32)
    } else if alg == KemScheme::Secp384r1 || alg == KemScheme::Secp521r1 {
        unimplemented!("not supported yet");
    } else {
        shared_secret
    }
}

fn supported_rsa_key_size(n: &Bytes) -> Result<(), u8> {
    match n.len() as u16 {
        257 | 385 | 513 | 769 | 1025 => Ok(()),
        _ => Err(UNSUPPORTED_ALGORITHM),
    }
}

fn valid_rsa_exponent(e: Vec<u8>) -> bool {
    e.len() == 3 && e[0] == 0x1 && e[1] == 0x0 && e[2] == 0x1
}

impl BertieCrypto for LibcruxBertieProvider {
    fn hash(&self, ha: &HashAlgorithm, data: &Bytes) -> Result<Bytes, TLSError> {
        let hasher = libcrux_hash_alg(ha)?;
        let mut digest = vec![0u8; hasher.hash_len()];
        hasher.hash(&data.declassify(), &mut digest);
        Ok(digest.into())
    }

    fn hmac_tag(
        &self,
        alg: &HashAlgorithm,
        mk: &MacKey,
        input: &Bytes,
    ) -> Result<Hmac, TLSError> {
        Ok(hmac(
            libcrux_hmac_alg(alg)?,
            &mk.declassify(),
            &input.declassify(),
            None,
        )
        .into())
    }

    fn hkdf_extract(
        &self,
        alg: &HashAlgorithm,
        ikm: &Bytes,
        salt: &Bytes,
    ) -> Result<Bytes, TLSError> {
        extract(libcrux_hkdf_alg(alg)?, salt.declassify(), ikm.declassify())
            .map(|bytes| bytes.into())
            .map_err(|_| CRYPTO_ERROR)
    }

    fn hkdf_expand(
        &self,
        alg: &HashAlgorithm,
        prk: &Bytes,
        info: &Bytes,
        len: usize,
    ) -> Result<Bytes, TLSError> {
        match expand(
            libcrux_hkdf_alg(alg)?,
            prk.declassify(),
            info.declassify(),
            len,
        ) {
            Ok(x) => Ok(x.into()),
            Err(_) => Err(CRYPTO_ERROR),
        }
    }

    fn aead_encrypt(
        &self,
        key: &AeadKey,
        iv: &AeadIV,
        plain: &Bytes,
        aad: &Bytes,
    ) -> Result<Bytes, TLSError> {
        let key = key
            .bytes()
            .declassify_array()
            .map_err(|_| INCORRECT_ARRAY_LENGTH)?;

        let mut ctxt = vec![0u8; plain.len()];
        let mut tag = [0u8; libcrux_chacha20poly1305::TAG_LEN];
        let result = encrypt_detached(
            &key,
            &plain.declassify(),
            &mut ctxt,
            &mut tag,
            &aad.declassify(),
            &iv.declassify_array()?,
        );

        match result {
            Ok(_) => {
                let cipby: Bytes = ctxt.into();
                let tagby: Bytes = tag.as_ref().into();
                Ok(cipby.concat(tagby))
            }
            Err(_) => Err(CRYPTO_ERROR),
        }
    }

    fn aead_decrypt(
        &self,
        key: &AeadKey,
        iv: &AeadIV,
        cip: &Bytes,
        aad: &Bytes,
    ) -> Result<Bytes, TLSError> {
        let tag = cip.slice(cip.len() - 16, 16);
        let ctxt = cip.slice(0, cip.len() - 16);
        let tag: [u8; 16] = tag.declassify_array()?;
        let key = key
            .bytes()
            .declassify_array()
            .map_err(|_| INCORRECT_ARRAY_LENGTH)?;
        let mut ptxt = vec![0u8; ctxt.len()];

        let result = decrypt_detached(
            &key,
            &mut ptxt,
            &ctxt.declassify(),
            &tag,
            &aad.declassify(),
            &iv.declassify_array()?,
        );

        match result {
            Ok(plain) => Ok(plain.into()),
            Err(_) => Err(CRYPTO_ERROR),
        }
    }

    fn sign_rsa<R: BertieRand>(
        &self,
        sk: &Bytes,
        pk_modulus: &Bytes,
        pk_exponent: &Bytes,
        cert_scheme: SignatureScheme,
        input: &Bytes,
        rng: &mut R,
    ) -> Result<Bytes, TLSError> {
        let mut salt = [0u8; 32];
        rng.fill_bytes(&mut salt);

        if !matches!(cert_scheme, SignatureScheme::RsaPssRsaSha256) {
            return Err(CRYPTO_ERROR);
        }

        if !valid_rsa_exponent(pk_exponent.declassify()) {
            return Err(UNSUPPORTED_ALGORITHM);
        }

        supported_rsa_key_size(pk_modulus)?;
        let _pk = VarLenPublicKey::try_from(&pk_modulus.declassify()[1..])
            .map_err(|_| INCORRECT_ARRAY_LENGTH)?;

        let pk_modulus_vec = pk_modulus.declassify();
        let sk_vec = sk.declassify();
        let sk = VarLenPrivateKey::from_components(&pk_modulus_vec[1..], &sk_vec)
            .map_err(|_| INCORRECT_ARRAY_LENGTH)?;

        let msg = &input.declassify();
        let mut signature = [0u8; 512];
        sign_varlen(
            RsaDigestAlgorithm::Sha2_256,
            &sk,
            msg,
            &salt,
            &mut signature,
        )
        .map_err(|_| CRYPTO_ERROR)?;

        Ok(signature.into())
    }

    fn sign<R: BertieRand>(
        &self,
        algorithm: &SignatureScheme,
        sk: &Bytes,
        input: &Bytes,
        rng: &mut R,
    ) -> Result<Bytes, TLSError> {
        match algorithm {
            SignatureScheme::EcdsaSecp256r1Sha256 => libcrux_ecdsa::p256::rand::sign(
                EcDsaDigestAlgorithm::Sha256,
                &input.declassify(),
                &sk.declassify()
                    .as_slice()
                    .try_into()
                    .map_err(|_| INCORRECT_ARRAY_LENGTH)?,
                rng,
            )
            .map_err(|_| CRYPTO_ERROR)
            .map(|s| {
                let (r, s) = s.as_bytes();
                Bytes::from(r).concat(Bytes::from(s))
            }),

            SignatureScheme::ED25519 => libcrux_ed25519::sign(
                &input.declassify(),
                &sk.declassify()
                    .try_into()
                    .map_err(|_| INCORRECT_ARRAY_LENGTH)?,
            )
            .map_err(|_| CRYPTO_ERROR)
            .map(|s| s.into()),

            SignatureScheme::RsaPssRsaSha256 => panic!("wrong function, use sign_rsa"),
        }
    }

    fn verify(
        &self,
        alg: &SignatureScheme,
        pk: &PublicVerificationKey,
        input: &Bytes,
        sig: &Bytes,
    ) -> Result<(), TLSError> {
        match (alg, pk) {
            (SignatureScheme::ED25519, PublicVerificationKey::EcDsa(pk)) => libcrux_ed25519::verify(
                &input.declassify(),
                &pk.declassify()
                    .try_into()
                    .map_err(|_| INCORRECT_ARRAY_LENGTH)?,
                &sig.declassify_array()?,
            )
            .map_err(|_| INVALID_SIGNATURE),

            (SignatureScheme::EcdsaSecp256r1Sha256, PublicVerificationKey::EcDsa(pk)) => {
                libcrux_ecdsa::p256::verify(
                    EcDsaDigestAlgorithm::Sha256,
                    &input.declassify(),
                    &libcrux_ecdsa::p256::Signature::from_bytes(sig.declassify_array()?),
                    &libcrux_ecdsa::p256::PublicKey::try_from(&pk.declassify_array()?)
                        .map_err(|_| CRYPTO_ERROR)?,
                )
                .map_err(|_| INVALID_SIGNATURE)
            }

            (
                SignatureScheme::RsaPssRsaSha256,
                PublicVerificationKey::Rsa(RsaVerificationKey {
                    modulus: n,
                    exponent: e,
                }),
            ) => {
                if !valid_rsa_exponent(e.declassify()) {
                    Err(UNSUPPORTED_ALGORITHM)
                } else {
                    supported_rsa_key_size(n)?;
                    let n_vec = n.declassify();
                    let pk =
                        VarLenPublicKey::try_from(&n_vec[1..]).map_err(|_| INCORRECT_ARRAY_LENGTH)?;

                    verify_varlen(
                        RsaDigestAlgorithm::Sha2_256,
                        &pk,
                        &input.declassify(),
                        32,
                        &sig.declassify(),
                    )
                    .map_err(|_| CRYPTO_ERROR)
                }
            }
            _ => Err(UNSUPPORTED_ALGORITHM),
        }
    }

    fn kem_keygen<R: BertieRand>(
        &self,
        alg: KemScheme,
        rng: &mut R,
    ) -> Result<(KemSk, KemPk), TLSError> {
        let res = libcrux_kem::key_gen(libcrux_kem_alg(alg)?, rng);
        match res {
            Ok((sk, pk)) => Ok((
                Bytes::from(sk.encode()),
                encoding_prefix(alg).concat(Bytes::from(pk.encode())),
            )),
            Err(_) => Err(CRYPTO_ERROR),
        }
    }

    fn kem_encap<R: BertieRand>(
        &self,
        alg: KemScheme,
        pk: &Bytes,
        rng: &mut R,
    ) -> Result<(Bytes, Bytes), TLSError> {
        let pk = into_raw(alg, pk.clone());
        let pk = PublicKey::decode(libcrux_kem_alg(alg)?, &pk.declassify()).unwrap();
        let res = pk.encapsulate(rng);
        match res {
            Ok((shared_secret, ct)) => {
                let ct = encoding_prefix(alg).concat(Bytes::from(ct.encode()));
                let shared_secret = to_shared_secret(alg, Bytes::from(shared_secret.encode()));
                Ok((shared_secret, ct))
            }
            Err(_) => Err(CRYPTO_ERROR),
        }
    }

    fn kem_decap(&self, alg: KemScheme, ct: &Bytes, sk: &Bytes) -> Result<Bytes, TLSError> {
        let librux_algorithm = libcrux_kem_alg(alg)?;
        let sk = PrivateKey::decode(librux_algorithm, &sk.declassify()).unwrap();
        let ct = into_raw(alg, ct.clone()).declassify();
        let ct = Ct::decode(librux_algorithm, &ct).unwrap();
        let res = ct.decapsulate(&sk);
        match res {
            Ok(shared_secret) => {
                let shared_secret: Bytes = shared_secret.encode().into();
                let shared_secret = to_shared_secret(alg, shared_secret);
                Ok(shared_secret)
            }
            Err(_) => Err(CRYPTO_ERROR),
        }
    }
}
