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
    key: &TagKey,
    ks: &mut TLSkeyscheduler,
) -> Result<MacKey, TLSError> {
    // panic!(); // TODO: function never called in tests??
    let key_handle = Handle {
        name: key.tag,
        alg: key.alg,
        level: 0,
    };
    set_by_handle(ks, &key_handle, key.val.clone());

    let zero_salt_handle = Handle {
        name: TLSnames::ZeroSalt,
        alg: ha.clone(),
        level: 0,
    };
    set_by_handle(ks, &zero_salt_handle, zero_salt(ha).val);

    let early_secret_handle = XTR(ks, 0, TLSnames::ES, &key_handle, &zero_salt_handle)?;
    let early_secret = tagkey_from_handle(ks, &early_secret_handle);

    let h = XPD(
        ks,
        TLSnames::Bind,
        0,
        &early_secret_handle,
        true, // res or ext? or is a bit needed to determine this?
        &hash_empty(ha)?,
    )?;
    Ok(ks.get(TLSnames::Bind, 0, (h.name, h.alg, h.level)))
}

/// Derive an AEAD key and iv.
pub(crate) fn derive_aead_key_iv(
    hash_algorithm: &HashAlgorithm,
    aead_algorithm: &AeadAlgorithm,
    key: &TagKey,
) -> Result<AeadKeyIV, TLSError> {
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
    key: &TagKey,
    tx: &Digest,
    ks: &mut TLSkeyscheduler,
) -> Result<(TagKey, TagKey, TagKey), TLSError> {
    let key_handle = Handle {
        name: key.tag,
        alg: key.alg,
        level: 0,
    };
    set_by_handle(ks, &key_handle, key.val.clone());

    let zero_salt_handle = Handle {
        name: TLSnames::ZeroSalt,
        alg: hash_algorithm.clone(),
        level: 0,
    };
    set_by_handle(ks, &zero_salt_handle, zero_salt(hash_algorithm).val);

    let early_secret_handle = XTR(ks, 0, TLSnames::ES, &key_handle, &zero_salt_handle)?;
    let early_secret = tagkey_from_handle(ks, &early_secret_handle);

    let digest_emp = hash_empty(hash_algorithm)?;

    let derived_secret_handle = XPD(
        ks,
        TLSnames::ESalt,
        0,
        &early_secret_handle,
        true,
        &digest_emp,
    )?;
    let derived_secret = tagkey_from_handle(ks, &derived_secret_handle);

    let client_early_traffic_secret_handle =
        XPD(ks, TLSnames::CET, 0, &early_secret_handle, true, tx)?;
    let client_early_traffic_secret = tagkey_from_handle(ks, &client_early_traffic_secret_handle);

    let early_exporter_master_secret_handle =
        XPD(ks, TLSnames::EEM, 0, &early_secret_handle, true, tx)?;
    let early_exporter_master_secret = tagkey_from_handle(ks, &early_exporter_master_secret_handle);

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
    ks: &mut TLSkeyscheduler,
) -> Result<(AeadKeyIV, TagKey), TLSError> {
    let (early_exporter_master_secret, client_early_traffic_secret, derived_secret) =
        next_keys_c_2(hash_algorithm, key, tx, ks)?;
    let sender_write_key_iv =
        derive_aead_key_iv(hash_algorithm, aead_algorithm, &client_early_traffic_secret)?;
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
    ks: &mut TLSkeyscheduler,
) -> Result<(AeadKeyIV, AeadKeyIV, MacKey, MacKey, TagKey), TLSError> {
    let psk = if let Some(k) = psko {
        &k.clone()
    } else {
        &no_psk(ha)
    };

    let psk_handle = Handle {
        name: psk.tag,
        alg: psk.alg,
        level: 0,
    };
    set_by_handle(ks, &psk_handle, psk.val.clone());

    let zero_salt_handle = Handle {
        name: TLSnames::ZeroSalt,
        alg: ha.clone(),
        level: 0,
    };
    set_by_handle(ks, &zero_salt_handle, zero_salt(ha).val);

    let early_secret_handle = XTR(ks, 0, TLSnames::ES, &psk_handle, &zero_salt_handle)?;
    let early_secret = tagkey_from_handle(ks, &early_secret_handle);

    let digest_emp = hash_empty(ha)?;

    let derived_secret_handle = XPD(
        ks,
        TLSnames::ESalt,
        0,
        &early_secret_handle,
        true,
        &digest_emp,
    )?;
    let derived_secret = tagkey_from_handle(ks, &derived_secret_handle);

    // KEM
    let shared_secret_handle = Handle {
        name: shared_secret.tag,
        alg: shared_secret.alg,
        level: 0,
    };
    set_by_handle(ks, &shared_secret_handle, shared_secret.val.clone());

    let handshake_secret_handle = XTR(
        ks,
        0,
        TLSnames::HS,
        &shared_secret_handle,
        &derived_secret_handle,
    )?;
    let handshake_secret = tagkey_from_handle(ks, &early_secret_handle);

    let client_handshake_traffic_secret_handle = XPD(
        ks,
        TLSnames::CHT,
        0,
        &handshake_secret_handle,
        true,
        transcript_hash,
    )?;
    let client_handshake_traffic_secret =
        tagkey_from_handle(ks, &client_handshake_traffic_secret_handle);

    let server_handshake_traffic_secret_handle = XPD(
        ks,
        TLSnames::SHT,
        0,
        &handshake_secret_handle,
        true,
        transcript_hash,
    )?;
    let server_handshake_traffic_secret =
        tagkey_from_handle(ks, &server_handshake_traffic_secret_handle);

    let client_finished_key = derive_finished_key(ha, &client_handshake_traffic_secret.val)?;
    let server_finished_key = derive_finished_key(ha, &server_handshake_traffic_secret.val)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_handshake_traffic_secret)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_handshake_traffic_secret)?;

    let master_secret_handle_ = XPD(
        ks,
        TLSnames::HSalt,
        0,
        &handshake_secret_handle,
        true,
        &digest_emp,
    )?;
    let master_secret_ = tagkey_from_handle(ks, &master_secret_handle_);

    let zero_ikm_handle = Handle {
        name: TLSnames::ZeroIKM,
        alg: ha.clone(),
        level: 0,
    };
    set_by_handle(ks, &zero_ikm_handle, zero_ikm(ha).val);

    let master_secret_handle = XTR(
        ks,
        0,
        TLSnames::AS,
        &zero_ikm_handle,
        &master_secret_handle_,
    )?;
    let master_secret = tagkey_from_handle(ks, &master_secret_handle);

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
    ks: &mut TLSkeyscheduler,
) -> Result<(AeadKeyIV, AeadKeyIV, TagKey), TLSError> {
    let as_handle = Handle {
        name: master_secret.tag,
        alg: master_secret.alg,
        level: 0,
    };

    let client_application_traffic_secret_0_handle =
        XPD(ks, TLSnames::CAT, 0, &as_handle, true, &tx)?;
    let client_application_traffic_secret_0 =
        tagkey_from_handle(ks, &client_application_traffic_secret_0_handle);

    // let client_application_traffic_secret_0 = xpd(master_secret, bytes(&LABEL_C_AP_TRAFFIC), tx)?;

    let server_application_traffic_secret_0_handle =
        XPD(ks, TLSnames::SAT, 0, &as_handle, true, &tx)?;
    let server_application_traffic_secret_0 =
        tagkey_from_handle(ks, &server_application_traffic_secret_0_handle);

    // let server_application_traffic_secret_0 = xpd(master_secret, bytes(&LABEL_S_AP_TRAFFIC), tx)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_application_traffic_secret_0)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_application_traffic_secret_0)?;

    let exporter_master_secret_handle = XPD(ks, TLSnames::EAM, 0, &as_handle, true, &tx)?;
    let exporter_master_secret = tagkey_from_handle(ks, &exporter_master_secret_handle);

    // let exporter_master_secret = xpd(master_secret, bytes(&LABEL_EXP_MASTER), tx)?;
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
    ks: &mut TLSkeyscheduler,
) -> Result<TagKey, TLSError> {
    let as_handle = Handle {
        name: master_secret.tag,
        alg: master_secret.alg,
        level: 0,
    };

    let exporter_master_secret_handle = XPD(ks, TLSnames::RM, 0, &as_handle, true, &tx)?;
    Ok(tagkey_from_handle(ks, &exporter_master_secret_handle))
}

// pub(crate) fn nextKeys(key: &TagKey, extra: Bytes, digest: &Digest, aead_algorithm: &AeadAlgorithm,) -> Vec<TagKey> {
//     // 0-RTT (k_cet)
//     derive_0rtt_keys(

//     // handshake messages (k_cht, k_sht)

//     // 1-RTT data (k_cat, k_sat)

//     // eksporter secrets (k_eem, k_eam)
// }
