pub(crate) mod key_schedule;

use crate::{
    tls13crypto::{hash, AeadAlgorithm, AeadKey, AeadKeyIV, Digest, HashAlgorithm, MacKey},
    tls13formats::*,
    tls13utils::*,
};
use key_schedule::{TLSnames::*, *};

/// Get the hash of an empty byte slice.
#[cfg_attr(feature = "hax-pv", hax_lib::pv_constructor)]
fn hash_empty(algorithm: &HashAlgorithm) -> Result<Digest, TLSError> {
    hash(algorithm, &Bytes::new())
}

#[cfg_attr(feature = "hax-pv", hax_lib::pv_constructor)]
pub fn derive_binder_key(
    ha: &HashAlgorithm,
    handle: &Handle,
    ks: &mut TLSkeyscheduler,
) -> Result<Handle, TLSError> {
    let zero_salt_handle = zero_salt(ks, ha);
    let early_secret = XTR(ks, 0, ES, handle, &zero_salt_handle)?;
    XPD(ks, Bind, 0, &early_secret, true, &hash_empty(ha)?) // res or ext? or is a bit needed to determine this?
}

/// Derive an AEAD key and iv.
#[allow(clippy::assign_op_pattern)]
#[cfg_attr(
    feature = "hax-pv",
    hax_lib::proverif::before(
        "fun extern__derive_aead_key_iv(
    $:{HashAlgorithm},
    $:{AeadAlgorithm},
    $:{Handle},
    $:{TLSkeyscheduler}
         )
     : $:{AeadKeyIV}."
    )
)]
#[cfg_attr(
    feature = "hax-pv",
    hax_lib::proverif::replace_body(
        "(extern__derive_aead_key_iv(
            hash_algorithm,
            aead_algorithm,
            handle,
            ks
          )
       )"
    )
)]
pub(crate) fn derive_aead_key_iv(
    hash_algorithm: &HashAlgorithm,
    aead_algorithm: &AeadAlgorithm,
    handle: &Handle,
    ks: &mut TLSkeyscheduler,
) -> Result<AeadKeyIV, TLSError> {
    let key = tagkey_from_handle(ks, handle)?.val;
    let sender_write_key = hkdf_expand_label(
        hash_algorithm,
        &key,
        bytes(&LABEL_KEY),
        &Bytes::new(),
        aead_algorithm.key_len(),
    )?;
    let sender_write_iv = hkdf_expand_label(
        hash_algorithm,
        &key,
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
    let early_secret = XTR(ks, 0, ES, handle, &zero_salt_handle)?;
    let digest_emp = hash_empty(hash_algorithm)?;
    let derived_secret = XPD(ks, ESalt, 0, &early_secret, true, &digest_emp)?;
    let client_early_traffic_secret = XPD(ks, CET, 0, &early_secret, true, tx)?;
    let early_exporter_master_secret = XPD(ks, EEM, 0, &early_secret, true, tx)?;

    Ok((
        early_exporter_master_secret,
        client_early_traffic_secret,
        derived_secret,
    ))
}

/// Derive 0-RTT AEAD keys.
#[cfg_attr(feature = "hax-pv", hax_lib::pv_constructor)]
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

#[cfg_attr(
    feature = "hax-pv",
    hax_lib::proverif::before(
        "fun extern__derive_finished_key(
                $:{HashAlgorithm},
                $:{Handle},
                $:{TLSkeyscheduler}
         )
     : $:{MacKey}."
    )
)]
#[cfg_attr(
    feature = "hax-pv",
    hax_lib::proverif::replace_body(
        "(extern__derive_finished_key(
              ha,
              handle,
              ks
          )
       )"
    )
)]
pub fn derive_finished_key(
    ha: &HashAlgorithm,
    handle: &Handle,
    ks: &mut TLSkeyscheduler,
) -> Result<MacKey, TLSError> {
    let k = tagkey_from_handle(ks, handle)?;
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
    shared_secret: &Handle,
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
    let early_secret = XTR(ks, 0, ES, psk_handle, &zero_salt_handle)?;
    let digest_emp = hash_empty(ha)?;
    let derived_secret = XPD(ks, ESalt, 0, &early_secret, true, &digest_emp)?;

    let handshake_secret = XTR(ks, 0, HS, shared_secret, &derived_secret)?;
    let client_handshake_traffic_secret =
        XPD(ks, CHT, 0, &handshake_secret, true, transcript_hash)?;
    let server_handshake_traffic_secret =
        XPD(ks, SHT, 0, &handshake_secret, true, transcript_hash)?;
    let master_secret_ = XPD(ks, HSalt, 0, &handshake_secret, true, &digest_emp)?;

    let zero_ikm_handle = zero_ikm(ks, ha);
    let master_secret = XTR(ks, 0, AS, &zero_ikm_handle, &master_secret_)?;
    Ok((
        client_handshake_traffic_secret,
        server_handshake_traffic_secret,
        master_secret,
    ))
}

pub(crate) fn derive_hk_ms(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    client_handshake_traffic_secret: &Handle,
    server_handshake_traffic_secret: &Handle,
    ks: &mut TLSkeyscheduler,
) -> Result<(AeadKeyIV, AeadKeyIV, MacKey, MacKey), TLSError> {
    let client_finished_key = derive_finished_key(ha, client_handshake_traffic_secret, ks)?;
    let server_finished_key = derive_finished_key(ha, server_handshake_traffic_secret, ks)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, client_handshake_traffic_secret, ks)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, server_handshake_traffic_secret, ks)?;

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
    let client_application_traffic_secret_0 = XPD(ks, CAT, 0, master_secret, true, tx)?;
    let server_application_traffic_secret_0 = XPD(ks, SAT, 0, master_secret, true, tx)?;
    let exporter_master_secret = XPD(ks, EAM, 0, master_secret, true, tx)?;

    Ok((
        client_application_traffic_secret_0,
        server_application_traffic_secret_0,
        exporter_master_secret,
    ))
}

pub(crate) fn derive_app_keys(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    client_application_traffic_secret_0: &Handle,
    server_application_traffic_secret_0: &Handle,
    ks: &mut TLSkeyscheduler,
) -> Result<(AeadKeyIV, AeadKeyIV), TLSError> {
    let client_write_key_iv = derive_aead_key_iv(ha, ae, client_application_traffic_secret_0, ks)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, server_application_traffic_secret_0, ks)?;

    Ok((client_write_key_iv, server_write_key_iv))
}

pub(crate) fn derive_rms(
    ha: &HashAlgorithm,
    master_secret: &Handle,
    tx: &Digest,
    ks: &mut TLSkeyscheduler,
) -> Result<Handle, TLSError> {
    XPD(ks, RM, 0, master_secret, true, tx)
}
