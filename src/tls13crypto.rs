
#[cfg(feature = "libcrux")]
use libcrux::*;
#[cfg(not(feature = "libcrux"))]
use hacspec_cryptolib::*;
use crate::*;


pub type Random = Bytes; //was [U8;32]
pub type Entropy = Bytes;
pub type SignatureKey = Bytes;
pub type PSK = Bytes;
pub type Key = Bytes;
pub type MacKey = Bytes;
pub type KemPk = Bytes;
pub type KemSk = Bytes;
pub type HMAC = Bytes;
pub type Digest = Bytes;
pub type AeadKey = Bytes;
pub type AeadIV = Bytes;
pub type AeadKeyIV = (Bytes,Bytes);

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum HashAlgorithm {
    SHA256,
    SHA384,
    SHA512
}

pub fn to_libcrux_hash_alg(alg:&HashAlgorithm) -> Result<digest::Algorithm,TLSError> {
    match alg {
        HashAlgorithm::SHA256 => Ok(digest::Algorithm::Sha256),
        HashAlgorithm::SHA384 => Ok(digest::Algorithm::Sha384),
        HashAlgorithm::SHA512 => Ok(digest::Algorithm::Sha512),
    }
}

pub fn hash(alg:&HashAlgorithm,data:&Bytes) -> Result<Bytes,TLSError> {
    Ok(digest::hash(to_libcrux_hash_alg(alg)?,&data.declassify()).into())
}

pub fn hash_len(alg:&HashAlgorithm) -> usize {
    match alg {
        HashAlgorithm::SHA256 => digest::digest_size(digest::Algorithm::Sha256),
        HashAlgorithm::SHA384 => digest::digest_size(digest::Algorithm::Sha384),
        HashAlgorithm::SHA512 => digest::digest_size(digest::Algorithm::Sha512),
    }
}

pub fn to_libcrux_hmac_alg(alg:&HashAlgorithm) -> Result<hmac::Algorithm,TLSError> {
    match alg {
        HashAlgorithm::SHA256 => Ok(hmac::Algorithm::Sha256),
        HashAlgorithm::SHA384 => Ok(hmac::Algorithm::Sha384),
        HashAlgorithm::SHA512 => Ok(hmac::Algorithm::Sha512),
    }
}
pub fn hmac_tag_len(alg:&HashAlgorithm) -> usize {
    hash_len(alg)
}

pub fn hmac_tag(alg:&HashAlgorithm,mk:&MacKey,input:&Bytes) -> Result<HMAC,TLSError> {
    Ok(hmac::hmac(to_libcrux_hmac_alg(alg)?, &mk.declassify(), &input.declassify(),None).into())
}

pub fn hmac_verify(alg:&HashAlgorithm,mk:&MacKey,input:&Bytes, tag:&Bytes) -> Result<(),TLSError> {
   if eq(&hmac_tag(alg,mk,input)?,tag) {Ok(())}
   else {tlserr(CRYPTO_ERROR)}
}

pub fn zero_key(alg:&HashAlgorithm) -> Bytes {
    Bytes::zeroes(hash_len(alg))
}

pub fn to_libcrux_hkdf_alg(alg:&HashAlgorithm) -> Result<hkdf::Algorithm,TLSError> {
    match alg {
        HashAlgorithm::SHA256 => Ok(hkdf::Algorithm::Sha256),
        HashAlgorithm::SHA384 => Ok(hkdf::Algorithm::Sha384),
        HashAlgorithm::SHA512 => Ok(hkdf::Algorithm::Sha512),
    }
}

// TODO: as always, check the order of the arguments: salt, ikm or ikm, salt?
pub fn hkdf_extract(alg:&HashAlgorithm,salt:&Bytes,ikm:&Bytes) -> Result<Bytes,TLSError> {
    Ok(hkdf::extract(to_libcrux_hkdf_alg(alg)?, &salt.declassify(), &ikm.declassify()).into())
}

pub fn hkdf_expand(alg:&HashAlgorithm,prk:&Bytes,info:&Bytes,len:usize) -> Result<Bytes,TLSError> {
    Ok(hkdf::expand(to_libcrux_hkdf_alg(alg)?, &prk.declassify(), &info.declassify(), len).map_err(|e| CRYPTO_ERROR)?.into())
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum AeadAlgorithm {
    Chacha20Poly1305,
    Aes128Gcm,
    Aes256Gcm
}

pub fn to_libcrux_aead_alg(alg:&AeadAlgorithm) -> Result<aead::Algorithm,TLSError> {
    match alg {
        AeadAlgorithm::Chacha20Poly1305 => {Ok(aead::Algorithm::Chacha20Poly1305)},
        AeadAlgorithm::Aes128Gcm => {Ok(aead::Algorithm::Aes128Gcm)},
        AeadAlgorithm::Aes256Gcm => {Ok(aead::Algorithm::Aes256Gcm)},
    }
}
pub fn ae_key_len(alg:&AeadAlgorithm) -> usize {
    match alg {
        AeadAlgorithm::Chacha20Poly1305 => {32},
        AeadAlgorithm::Aes128Gcm => {16},
        AeadAlgorithm::Aes256Gcm => {32},
    }
}

pub fn ae_key_wrap(alg:&AeadAlgorithm, k:&AeadKey) -> Result<aead::Key,TLSError> {
    match alg {
        AeadAlgorithm::Chacha20Poly1305 => {Ok(aead::Key::Chacha20Poly1305(aead::Chacha20Key(k.declassify().try_into().map_err(|_|CRYPTO_ERROR)?)))},
        AeadAlgorithm::Aes128Gcm => {Ok(aead::Key::Aes128(aead::Aes128Key(k.declassify().try_into().map_err(|_|CRYPTO_ERROR)?)))},
        AeadAlgorithm::Aes256Gcm => {Ok(aead::Key::Aes256(aead::Aes256Key(k.declassify().try_into().map_err(|_|CRYPTO_ERROR)?)))},
    }
}

pub fn ae_iv_len(alg:&AeadAlgorithm) -> usize {
    match alg {
        AeadAlgorithm::Chacha20Poly1305 => {12},
        AeadAlgorithm::Aes128Gcm => {12},
        AeadAlgorithm::Aes256Gcm => {12},
    }
}

pub fn aead_encrypt(alg:&AeadAlgorithm,k:&AeadKey,iv:&AeadIV,plain:&Bytes,aad:&Bytes) -> Result<Bytes,TLSError> {
    let (tag,cip) = aead::encrypt_detached(&ae_key_wrap(alg,k)?, plain.declassify(), aead::Iv(iv.declassify().try_into().map_err(|_|CRYPTO_ERROR)?), aad.declassify()).map_err(|_| CRYPTO_ERROR)?;
    let cipby:Bytes = cip.into();
    let tagby:Bytes = tag.as_ref().into();
    Ok(cipby.concat(&tagby))
}

pub fn aead_decrypt(alg:&AeadAlgorithm,k:&AeadKey,iv:&AeadIV,cip:&Bytes,aad:&Bytes) -> Result<Bytes,TLSError> {
    let tag = cip.slice(cip.len()-16,16);
    let cip = cip.slice(0,cip.len() - 16);
    let tag : [u8;16] = tag.declassify().try_into().map_err(|_| CRYPTO_ERROR)?;
    let plain = aead::decrypt_detached(&ae_key_wrap(alg,k)?, cip.declassify(), aead::Iv(iv.declassify().try_into().map_err(|_|CRYPTO_ERROR)?), aad.declassify(), &aead::Tag::from(tag)).map_err(|_| CRYPTO_ERROR)?;
    Ok(plain.into())
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum SignatureScheme {
    RsaPssRsaSha256,
    EcdsaSecp256r1Sha256,
    ED25519
}

pub fn to_libcrux_sig_alg(a:SignatureScheme) -> Result<signature::Algorithm,TLSError> {
    match a {
        SignatureScheme::RsaPssRsaSha256 => tlserr(UNSUPPORTED_ALGORITHM),
        SignatureScheme::ED25519 => Ok(signature::Algorithm::Ed25519),
        SignatureScheme::EcdsaSecp256r1Sha256 => Ok(signature::Algorithm::EcDsaP256(signature::DigestAlgorithm::Sha256)),
    }
}

pub fn sign(alg:&SignatureScheme,sk:&Bytes,input:&Bytes,ent:Bytes) -> Result<Bytes,TLSError> {
    
    tlserr(UNSUPPORTED_ALGORITHM) //TODO
}

pub fn verify(alg:&SignatureScheme,pk:&PublicVerificationKey,input:&Bytes,sig:&Bytes) -> Result<(),TLSError> {
    tlserr(UNSUPPORTED_ALGORITHM) //TODO
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum KemScheme {
    X25519,
    Secp256r1,
    X448,
    Secp384r1,
    Secp521r1
}

pub fn kem_priv_len(alg:&KemScheme) -> usize {
    match alg {
        KemScheme::X25519 => {32},
        KemScheme::Secp256r1 => {32},
        _ => {64} //Check
    }
}

pub fn to_libcrux_kem_alg(alg:&KemScheme) -> Result<kem::Algorithm,TLSError> {
    match alg {
        KemScheme::X25519 => Ok(kem::Algorithm::X25519),
        KemScheme::Secp256r1 => Ok(kem::Algorithm::Secp256r1),
        _ => tlserr(UNSUPPORTED_ALGORITHM)
    }
}
pub fn kem_keygen(alg:&KemScheme,ent:Bytes) -> Result<(KemSk,KemPk),TLSError> {
    let sk = ent.clone();
    let pk = kem::secret_to_public(to_libcrux_kem_alg(alg)?,&sk.declassify()).map_err(|_| CRYPTO_ERROR)?.into();
    Ok((sk,pk))
}

pub fn kem_encap(alg:&KemScheme,pk:&Bytes, ent:Bytes) -> Result<(Bytes,Bytes),TLSError> {
    tlserr(UNSUPPORTED_ALGORITHM) //TODO
}

pub fn kem_decap(alg:&KemScheme,ct:&Bytes, sk:&Bytes) -> Result<Bytes,TLSError> {
    Ok(kem::decapsulate(to_libcrux_kem_alg(alg)?,&ct.declassify(),&sk.declassify()).map_err(|_| CRYPTO_ERROR)?.into())
}

// Algorithmns(ha, ae, sa, gn, psk_mode, zero_rtt)
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Algorithms(
    pub HashAlgorithm,
    pub AeadAlgorithm,
    pub SignatureScheme,
    pub KemScheme,
    pub bool,
    pub bool,
);

pub fn hash_alg(algs: &Algorithms) -> HashAlgorithm {
    algs.0
}
pub fn aead_alg(algs: &Algorithms) -> AeadAlgorithm {
    algs.1
}
pub fn sig_alg(algs: &Algorithms) -> SignatureScheme {
    algs.2
}
pub fn kem_alg(algs: &Algorithms) -> KemScheme {
    algs.3
}
pub fn psk_mode(algs: &Algorithms) -> bool {
    algs.4
}
pub fn zero_rtt(algs: &Algorithms) -> bool {
    algs.5
}
