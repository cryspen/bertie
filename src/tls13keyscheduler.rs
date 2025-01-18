pub(crate) mod key_schedule;

use crate::{
    tls13crypto::{
        hkdf_expand, hkdf_extract, hmac_tag, AeadAlgorithm, AeadKey, AeadKeyIV, Algorithms, Digest,
        HashAlgorithm, Key, MacKey, Psk,
    },
    tls13formats::*,
    tls13utils::*,
};
use key_schedule::{hkdf_expand_label, no_psk, xpd, xtr, zero_ikm, zero_salt, TagKey};

/// Get the hash of an empty byte slice.
fn hash_empty(algorithm: &HashAlgorithm) -> Result<Digest, TLSError> {
    algorithm.hash(&Bytes::new())
}

pub fn derive_binder_key(ha: &HashAlgorithm, k: &TagKey) -> Result<MacKey, TLSError> {
    let early_secret = xtr(ha, k, &zero_salt(ha))?;
    Ok(xpd(
        ha,
        &early_secret,
        bytes(&LABEL_RES_BINDER),
        &hash_empty(ha)?,
    )?
    .val)
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

pub(crate) fn next_keys_c_2(
    hash_algorithm: &HashAlgorithm,
    aead_algorithm: &AeadAlgorithm,
    key: &TagKey,
    tx: &Digest,
) -> Result<(TagKey, TagKey, TagKey), TLSError> {
    let early_secret = xtr(hash_algorithm, &key, &zero_salt(hash_algorithm))?;
    let digest_emp = hash_empty(hash_algorithm)?;
    let derived_secret = xpd(
        hash_algorithm,
        &early_secret,
        bytes(&LABEL_DERIVED),
        &digest_emp,
    )?;
    let client_early_traffic_secret =
        xpd(hash_algorithm, &early_secret, bytes(&LABEL_C_E_TRAFFIC), tx)?;
    let early_exporter_master_secret = xpd(
        hash_algorithm,
        &early_secret,
        bytes(&LABEL_E_EXP_MASTER),
        tx,
    )?;
    Ok((
        early_exporter_master_secret,
        client_early_traffic_secret,
        derived_secret,
    ))
}

/// Derive 0-RTT AEAD keys.
pub(crate) fn derive_0rtt_keys(
    hash_algorithm: &HashAlgorithm,
    aead_algorithm: &AeadAlgorithm,
    key: &TagKey,
    tx: &Digest,
) -> Result<(AeadKeyIV, TagKey), TLSError> {
    let (early_exporter_master_secret, client_early_traffic_secret, derived_secret) =
        next_keys_c_2(hash_algorithm, aead_algorithm, key, tx)?;
    let sender_write_key_iv = derive_aead_key_iv(
        hash_algorithm,
        aead_algorithm,
        &client_early_traffic_secret.val,
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
    shared_secret: &TagKey,
    psko: &Option<TagKey>,
    transcript_hash: &Digest,
) -> Result<(AeadKeyIV, AeadKeyIV, MacKey, MacKey, TagKey), TLSError> {
    let psk = if let Some(k) = psko {
        &k.clone()
    } else {
        &no_psk(ha)
    };
    let early_secret = xtr(ha, psk, &zero_salt(ha))?;
    let digest_emp = hash_empty(ha)?;
    let derived_secret = xpd(ha, &early_secret, bytes(&LABEL_DERIVED), &digest_emp)?;
    let handshake_secret = xtr(ha, shared_secret, &derived_secret)?;
    let client_handshake_traffic_secret = xpd(
        ha,
        &handshake_secret,
        bytes(&LABEL_C_HS_TRAFFIC),
        transcript_hash,
    )?;
    let server_handshake_traffic_secret = xpd(
        ha,
        &handshake_secret,
        bytes(&LABEL_S_HS_TRAFFIC),
        transcript_hash,
    )?;
    let client_finished_key = derive_finished_key(ha, &client_handshake_traffic_secret.val)?;
    let server_finished_key = derive_finished_key(ha, &server_handshake_traffic_secret.val)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_handshake_traffic_secret.val)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_handshake_traffic_secret.val)?;
    let master_secret_ = xpd(ha, &handshake_secret, bytes(&LABEL_DERIVED), &digest_emp)?;
    let master_secret = xtr(ha, &zero_ikm(ha), &master_secret_)?;
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
    master_secret: &TagKey,
    tx: &Digest,
) -> Result<(AeadKeyIV, AeadKeyIV, TagKey), TLSError> {
    let client_application_traffic_secret_0 =
        xpd(ha, master_secret, bytes(&LABEL_C_AP_TRAFFIC), tx)?;
    let server_application_traffic_secret_0 =
        xpd(ha, master_secret, bytes(&LABEL_S_AP_TRAFFIC), tx)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_application_traffic_secret_0.val)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_application_traffic_secret_0.val)?;
    let exporter_master_secret = xpd(ha, master_secret, bytes(&LABEL_EXP_MASTER), tx)?;
    Ok((
        client_write_key_iv,
        server_write_key_iv,
        exporter_master_secret,
    ))
}

pub(crate) fn derive_rms(
    ha: &HashAlgorithm,
    master_secret: &TagKey,
    tx: &Digest,
) -> Result<TagKey, TLSError> {
    xpd(ha, master_secret, bytes(&LABEL_RES_MASTER), tx)
}
