use rand::{CryptoRng, RngCore};

use crate::{
    tls13cert::{cert_public_key, rsa_public_key, verification_key_from_cert},
    tls13crypto::{
        hkdf_expand, hkdf_extract, hmac_tag, hmac_verify, kem_decap, kem_encap, kem_keygen, sign,
        sign_rsa, verify, zero_key, AeadAlgorithm, AeadKey, AeadKeyIV, Algorithms, Digest,
        HashAlgorithm, KemSk, Key, MacKey, Psk, Random, SignatureScheme,
    },
    tls13formats::{handshake_data::HandshakeData, *},
    tls13record::*,
    tls13utils::*,
};

/// Get the hash of an empty byte slice.
fn hash_empty(algorithm: &HashAlgorithm) -> Result<Digest, TLSError> {
    algorithm.hash(&Bytes::new())
}

/* TLS 1.3 Key Schedule: See RFC 8446 Section 7 */

/// HKDF expand with a `label`.
fn hkdf_expand_label(
    hash_algorithm: &HashAlgorithm,
    key: &Key,
    label: Bytes,
    context: &Bytes,
    len: usize,
) -> Result<Key, TLSError> {
    if len >= 65536 {
        Err(PAYLOAD_TOO_LONG)
    } else {
        let lenb = u16_as_be_bytes(U16(len as u16));
        let tls13_label = Bytes::from_slice(&LABEL_TLS13).concat(label);
        let info = encode_length_u8(tls13_label.as_raw())?
            .concat(encode_length_u8(context.as_raw())?)
            .prefix(&lenb);
        hkdf_expand(hash_algorithm, key, &info, len)
    }
}

pub fn derive_secret(
    hash_algorithm: &HashAlgorithm,
    key: &Key,
    label: Bytes,
    transcript_hash: &Digest,
) -> Result<Key, TLSError> {
    hkdf_expand_label(
        hash_algorithm,
        key,
        label,
        transcript_hash,
        hash_algorithm.hash_len(),
    )
}

pub fn derive_binder_key(ha: &HashAlgorithm, k: &Key) -> Result<MacKey, TLSError> {
    let early_secret = hkdf_extract(ha, k, &zero_key(ha))?;
    derive_secret(
        ha,
        &early_secret,
        bytes(&LABEL_RES_BINDER),
        &hash_empty(ha)?,
    )
}

/// Derive an AEAD key and iv.
pub(crate) fn derive_aead_key_iv(
    hash_algorithm: &HashAlgorithm,
    aead_algorithm: &AeadAlgorithm,
    key: &Key,
) -> Result<AeadKeyIV, TLSError> {
    let sender_write_key = hkdf_expand_label(
        hash_algorithm,
        key,
        bytes(&LABEL_KEY),
        &Bytes::new(),
        aead_algorithm.key_len(),
    )?;
    let sender_write_iv = hkdf_expand_label(
        hash_algorithm,
        key,
        bytes(&LABEL_IV),
        &Bytes::new(),
        aead_algorithm.iv_len(),
    )?;
    Ok(AeadKeyIV::new(
        AeadKey::new(sender_write_key, *aead_algorithm),
        sender_write_iv,
    ))
}

/// Derive 0-RTT AEAD keys.
pub(crate) fn derive_0rtt_keys(
    hash_algorithm: &HashAlgorithm,
    aead_algoorithm: &AeadAlgorithm,
    key: &Key,
    tx: &Digest,
) -> Result<(AeadKeyIV, Key), TLSError> {
    let early_secret = hkdf_extract(hash_algorithm, key, &zero_key(hash_algorithm))?;
    let client_early_traffic_secret =
        derive_secret(hash_algorithm, &early_secret, bytes(&LABEL_C_E_TRAFFIC), tx)?;
    let early_exporter_master_secret = derive_secret(
        hash_algorithm,
        &early_secret,
        bytes(&LABEL_E_EXP_MASTER),
        tx,
    )?;
    let sender_write_key_iv = derive_aead_key_iv(
        hash_algorithm,
        aead_algoorithm,
        &client_early_traffic_secret,
    )?;
    Ok((sender_write_key_iv, early_exporter_master_secret))
}

pub fn derive_finished_key(ha: &HashAlgorithm, k: &Key) -> Result<MacKey, TLSError> {
    hkdf_expand_label(
        ha,
        k,
        bytes(&LABEL_FINISHED),
        &Bytes::new(),
        ha.hmac_tag_len(),
    )
}

/// Derive the handshake keys and master secret.
pub(crate) fn derive_hk_ms(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    shared_secret: &Key,
    psko: &Option<Psk>,
    transcript_hash: &Digest,
) -> Result<(AeadKeyIV, AeadKeyIV, MacKey, MacKey, Key), TLSError> {
    let psk = if let Some(k) = psko {
        k.clone()
    } else {
        zero_key(ha)
    };
    let early_secret = hkdf_extract(ha, &psk, &zero_key(ha))?;
    let digest_emp = hash_empty(ha)?;
    let derived_secret = derive_secret(ha, &early_secret, bytes(&LABEL_DERIVED), &digest_emp)?;
    let handshake_secret = hkdf_extract(ha, shared_secret, &derived_secret)?;
    let client_handshake_traffic_secret = derive_secret(
        ha,
        &handshake_secret,
        bytes(&LABEL_C_HS_TRAFFIC),
        transcript_hash,
    )?;
    let server_handshake_traffic_secret = derive_secret(
        ha,
        &handshake_secret,
        bytes(&LABEL_S_HS_TRAFFIC),
        transcript_hash,
    )?;
    let client_finished_key = derive_finished_key(ha, &client_handshake_traffic_secret)?;
    let server_finished_key = derive_finished_key(ha, &server_handshake_traffic_secret)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_handshake_traffic_secret)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_handshake_traffic_secret)?;
    let master_secret_ = derive_secret(ha, &handshake_secret, bytes(&LABEL_DERIVED), &digest_emp)?;
    let master_secret = hkdf_extract(ha, &zero_key(ha), &master_secret_)?;
    Ok((
        client_write_key_iv,
        server_write_key_iv,
        client_finished_key,
        server_finished_key,
        master_secret,
    ))
}

/// Derive the application keys and master secret.
pub(crate) fn derive_app_keys(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    master_secret: &Key,
    tx: &Digest,
) -> Result<(AeadKeyIV, AeadKeyIV, Key), TLSError> {
    let client_application_traffic_secret_0 =
        derive_secret(ha, master_secret, bytes(&LABEL_C_AP_TRAFFIC), tx)?;
    let server_application_traffic_secret_0 =
        derive_secret(ha, master_secret, bytes(&LABEL_S_AP_TRAFFIC), tx)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_application_traffic_secret_0)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_application_traffic_secret_0)?;
    let exporter_master_secret = derive_secret(ha, master_secret, bytes(&LABEL_EXP_MASTER), tx)?;
    Ok((
        client_write_key_iv,
        server_write_key_iv,
        exporter_master_secret,
    ))
}

pub(crate) fn derive_rms(
    ha: &HashAlgorithm,
    master_secret: &Key,
    tx: &Digest,
) -> Result<Key, TLSError> {
    derive_secret(ha, master_secret, bytes(&LABEL_RES_MASTER), tx)
}
