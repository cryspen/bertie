pub(crate) mod key_schedule;

use crate::{
    tls13crypto::{AeadAlgorithm, AeadKey, AeadKeyIV, Digest, HashAlgorithm, Key, MacKey},
    tls13formats::*,
    tls13utils::*,
};
use key_schedule::*;

/// Get the hash of an empty byte slice.
fn hash_empty(algorithm: &HashAlgorithm) -> Result<Digest, TLSError> {
    algorithm.hash(&Bytes::new())
}

pub fn derive_binder_key(
    ha: &HashAlgorithm,
    handle: &Handle,
    ks: &mut TLSkeyscheduler,
) -> Result<Handle, TLSError> {
    // panic!(); // TODO: function never called in tests??
    let zero_salt_handle = zero_salt(ks, ha);
    let early_secret_handle = XTR(ks, 0, TLSnames::ES, &handle, &zero_salt_handle)?;

    let h = XPD(
        ks,
        TLSnames::Bind,
        0,
        &early_secret_handle,
        true, // res or ext? or is a bit needed to determine this?
        &hash_empty(ha)?,
    )?;
    Ok(h)
}

/// Derive an AEAD key and iv.
pub(crate) fn derive_aead_key_iv(
    hash_algorithm: &HashAlgorithm,
    aead_algorithm: &AeadAlgorithm,
    handle: &Handle,
    ks: &mut TLSkeyscheduler,
) -> Result<AeadKeyIV, TLSError> {
    let key = tagkey_from_handle(ks, &handle).ok_or(INCORRECT_STATE)?;
    let sender_write_key = hkdf_expand_label(
        hash_algorithm,
        &key.val,
        bytes(&LABEL_KEY),
        &Bytes::new(),
        aead_algorithm.key_len(),
    )?;
    let sender_write_iv = hkdf_expand_label(
        hash_algorithm,
        &key.val,
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
    handle: &Handle,
    tx: &Digest,
    ks: &mut TLSkeyscheduler,
) -> Result<(Handle, Handle, Handle), TLSError> {
    let zero_salt_handle = zero_salt(ks, hash_algorithm);
    let early_secret_handle = XTR(ks, 0, TLSnames::ES, &handle, &zero_salt_handle)?;
    let digest_emp = hash_empty(hash_algorithm)?;
    let derived_secret_handle = XPD(
        ks,
        TLSnames::ESalt,
        0,
        &early_secret_handle,
        true,
        &digest_emp,
    )?;

    let client_early_traffic_secret_handle =
        XPD(ks, TLSnames::CET, 0, &early_secret_handle, true, tx)?;

    let early_exporter_master_secret_handle =
        XPD(ks, TLSnames::EEM, 0, &early_secret_handle, true, tx)?;

    Ok((
        early_exporter_master_secret_handle,
        client_early_traffic_secret_handle,
        derived_secret_handle,
    ))
}

/// Derive 0-RTT AEAD keys.
pub(crate) fn derive_0rtt_keys(
    hash_algorithm: &HashAlgorithm,
    aead_algorithm: &AeadAlgorithm,
    handle: &Handle,
    tx: &Digest,
    ks: &mut TLSkeyscheduler,
) -> Result<(AeadKeyIV, Handle), TLSError> {
    let (early_exporter_master_secret, client_early_traffic_secret, derived_secret) =
        next_keys_c_2(hash_algorithm, handle, tx, ks)?;
    let sender_write_key_iv = derive_aead_key_iv(
        hash_algorithm,
        aead_algorithm,
        &client_early_traffic_secret,
        ks,
    )?;
    Ok((sender_write_key_iv, early_exporter_master_secret))
}

pub fn derive_finished_key(
    ha: &HashAlgorithm,
    handle: &Handle,
    ks: &mut TLSkeyscheduler,
) -> Result<MacKey, TLSError> {
    let k = tagkey_from_handle(ks, &handle).ok_or(INCORRECT_STATE)?;
    hkdf_expand_label(
        ha,
        &k.val,
        bytes(&LABEL_FINISHED),
        &Bytes::new(),
        ha.hmac_tag_len(),
    )
}

/// Derive the handshake keys and master secret.
pub(crate) fn derive_hk_handles(
    ha: &HashAlgorithm,
    shared_secret_handle: &Handle,
    psko: &Option<Handle>,
    transcript_hash: &Digest,
    ks: &mut TLSkeyscheduler,
) -> Result<(Handle, Handle, Handle), TLSError> {
    let psk_handle = if let Some(k) = psko {
        &k.clone()
    } else {
        &no_psk(ks, ha)
    };
    let zero_salt_handle = zero_salt(ks, ha);
    let early_secret_handle = XTR(ks, 0, TLSnames::ES, &psk_handle, &zero_salt_handle)?;
    let digest_emp = hash_empty(ha)?;
    let derived_secret_handle = XPD(
        ks,
        TLSnames::ESalt,
        0,
        &early_secret_handle,
        true,
        &digest_emp,
    )?;

    let handshake_secret_handle = XTR(
        ks,
        0,
        TLSnames::HS,
        shared_secret_handle,
        &derived_secret_handle,
    )?;
    let client_handshake_traffic_secret_handle = XPD(
        ks,
        TLSnames::CHT,
        0,
        &handshake_secret_handle,
        true,
        transcript_hash,
    )?;
    let server_handshake_traffic_secret_handle = XPD(
        ks,
        TLSnames::SHT,
        0,
        &handshake_secret_handle,
        true,
        transcript_hash,
    )?;
    let master_secret_handle_ = XPD(
        ks,
        TLSnames::HSalt,
        0,
        &handshake_secret_handle,
        true,
        &digest_emp,
    )?;

    let zero_ikm_handle = zero_ikm(ks, ha);
    let master_secret_handle = XTR(
        ks,
        0,
        TLSnames::AS,
        &zero_ikm_handle,
        &master_secret_handle_,
    )?;
    Ok((
        client_handshake_traffic_secret_handle,
        server_handshake_traffic_secret_handle,
        master_secret_handle,
    ))
}

pub(crate) fn derive_hk_ms(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    client_handshake_traffic_secret_handle: &Handle,
    server_handshake_traffic_secret_handle: &Handle,
    ks: &mut TLSkeyscheduler,
) -> Result<(AeadKeyIV, AeadKeyIV, MacKey, MacKey), TLSError> {
    let client_finished_key = derive_finished_key(ha, &client_handshake_traffic_secret_handle, ks)?;
    let server_finished_key = derive_finished_key(ha, &server_handshake_traffic_secret_handle, ks)?;
    let client_write_key_iv =
        derive_aead_key_iv(ha, ae, &client_handshake_traffic_secret_handle, ks)?;
    let server_write_key_iv =
        derive_aead_key_iv(ha, ae, &server_handshake_traffic_secret_handle, ks)?;

    Ok((
        client_write_key_iv,
        server_write_key_iv,
        client_finished_key,
        server_finished_key,
    ))
}

/// Derive the application keys and master secret.
pub(crate) fn derive_app_handles(
    ha: &HashAlgorithm,
    master_secret: &Handle,
    tx: &Digest,
    ks: &mut TLSkeyscheduler,
) -> Result<(Handle, Handle, Handle), TLSError> {
    let client_application_traffic_secret_0_handle =
        XPD(ks, TLSnames::CAT, 0, master_secret, true, &tx)?;
    let server_application_traffic_secret_0_handle =
        XPD(ks, TLSnames::SAT, 0, master_secret, true, &tx)?;

    let exporter_master_secret_handle = XPD(ks, TLSnames::EAM, 0, master_secret, true, &tx)?;

    Ok((
        client_application_traffic_secret_0_handle,
        server_application_traffic_secret_0_handle,
        exporter_master_secret_handle,
    ))
}

pub(crate) fn derive_app_keys(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    client_application_traffic_secret_0_handle: &Handle,
    server_application_traffic_secret_0_handle: &Handle,
    ks: &mut TLSkeyscheduler,
) -> Result<(AeadKeyIV, AeadKeyIV), TLSError> {
    let client_write_key_iv =
        derive_aead_key_iv(ha, ae, &client_application_traffic_secret_0_handle, ks)?;
    let server_write_key_iv =
        derive_aead_key_iv(ha, ae, &server_application_traffic_secret_0_handle, ks)?;

    Ok((client_write_key_iv, server_write_key_iv))
}

pub(crate) fn derive_rms(
    ha: &HashAlgorithm,
    master_secret: &Handle,
    tx: &Digest,
    ks: &mut TLSkeyscheduler,
) -> Result<Handle, TLSError> {
    XPD(ks, TLSnames::RM, 0, &master_secret, true, &tx)
}

// pub(crate) fn nextKeys(key: &TagKey, extra: Bytes, digest: &Digest, aead_algorithm: &AeadAlgorithm,) -> Vec<TagKey> {
//     // 0-RTT (k_cet)
//     derive_0rtt_keys(

//     // handshake messages (k_cht, k_sht)

//     // 1-RTT data (k_cat, k_sat)

//     // eksporter secrets (k_eem, k_eam)
// }
