use crate::{
    tls13crypto::{
        hkdf_expand, hkdf_extract, hmac_tag, zero_key, AeadAlgorithm, AeadKey, AeadKeyIV,
        Algorithms, Digest, HashAlgorithm, Key, MacKey, Psk,
    },
    tls13formats::*,
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

pub fn derive_binder_key(ha: &HashAlgorithm, k: &Key) -> Result<MacKey, TLSError> {
    let (K_ES, early_secret) = xtr(PSK, ZeroSalt, ha, k, &zero_key(ha))?;
    Ok(xpd(
        K_ES,
        ha,
        &early_secret,
        bytes(&LABEL_RES_BINDER),
        &hash_empty(ha)?,
    )?
    .1)
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
    let (K_ES, early_secret) = xtr(
        PSK,
        ZeroSalt,
        hash_algorithm,
        key,
        &zero_key(hash_algorithm),
    )?;
    let (K_CET, client_early_traffic_secret) = xpd(
        K_ES,
        hash_algorithm,
        &early_secret,
        bytes(&LABEL_C_E_TRAFFIC),
        tx,
    )?;
    let (K_EEM, early_exporter_master_secret) = xpd(
        K_ES,
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
    let (K_ES, early_secret) = xtr(PSK, ZeroSalt, ha, &psk, &zero_key(ha))?;
    let digest_emp = hash_empty(ha)?;
    let (K_ESalt, derived_secret) =
        xpd(K_ES, ha, &early_secret, bytes(&LABEL_DERIVED), &digest_emp)?;
    let (K_HS, handshake_secret) = xtr(K_ESalt, DH, ha, shared_secret, &derived_secret)?;
    let (K_CHT, client_handshake_traffic_secret) = xpd(
        K_HS,
        ha,
        &handshake_secret,
        bytes(&LABEL_C_HS_TRAFFIC),
        transcript_hash,
    )?;
    let (K_SHT, server_handshake_traffic_secret) = xpd(
        K_HS,
        ha,
        &handshake_secret,
        bytes(&LABEL_S_HS_TRAFFIC),
        transcript_hash,
    )?;
    let client_finished_key = derive_finished_key(ha, &client_handshake_traffic_secret)?;
    let server_finished_key = derive_finished_key(ha, &server_handshake_traffic_secret)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_handshake_traffic_secret)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_handshake_traffic_secret)?;
    let (K_HSalt, master_secret_) = xpd(
        K_HS,
        ha,
        &handshake_secret,
        bytes(&LABEL_DERIVED),
        &digest_emp,
    )?;
    let (K_AS, master_secret) = xtr(K_HSalt, ZeroIKM, ha, &zero_key(ha), &master_secret_)?;
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
    let (_, client_application_traffic_secret_0) =
        xpd(AS, ha, master_secret, bytes(&LABEL_C_AP_TRAFFIC), tx)?;
    let (_, server_application_traffic_secret_0) =
        xpd(AS, ha, master_secret, bytes(&LABEL_S_AP_TRAFFIC), tx)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_application_traffic_secret_0)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_application_traffic_secret_0)?;
    let (_, exporter_master_secret) = xpd(AS, ha, master_secret, bytes(&LABEL_EXP_MASTER), tx)?;
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
    let (_, key) = xpd(AS, ha, master_secret, bytes(&LABEL_RES_MASTER), tx)?;
    Ok(key)
}

/////////////////////////////////////////////////

trait KeySchedule<N> {
    fn labels(a: N, b: bool) -> [u8; 12]; // Bit string of size 96 (8*12)
    fn prnt_n(a: N) -> (Option<N>, Option<N>);
}

struct TLSkeyscheduler {}

#[derive(Copy, Clone)]
enum TLSnames {
    ES,
    EEM,
    CET,
    Bind,
    Binder,
    HS,
    SHT,
    CHT,
    HSalt,
    AS,
    RM,
    CAT,
    SAT,
    EAM,
    PSK,

    ZeroSalt, // 0
    ESalt,
    DH,
    ZeroIKM, // 0^len(alg)
}
use TLSnames::*;

impl KeySchedule<TLSnames> for TLSkeyscheduler {
    fn prnt_n(a: TLSnames) -> (Option<TLSnames>, Option<TLSnames>) {
        match a {
            ES => (Some(ZeroSalt), Some(PSK)),
            EEM | CET | Bind => (Some(ES), None),
            Binder => (Some(Bind), None),
            HS => (Some(ESalt), Some(DH)),
            SHT | CHT | HSalt => (Some(HS), None),
            AS => (Some(HSalt), Some(ZeroIKM)),
            RM | CAT | SAT | EAM => (Some(AS), None),
            PSK => (Some(RM), None),
            ZeroSalt | DH | ZeroIKM => (None, None),
            ESalt => (todo!(), None),
        }
    }

    fn labels(a: TLSnames, b: bool) -> [u8; 12] {
        match a {
            // EEM => LABEL_E_EXP_MASTER,
            // CET => LABEL_C_E_TRAFFIC,
            // Binder => LABEL_RES_BINDER,
            SHT => LABEL_S_HS_TRAFFIC,
            CHT => LABEL_C_HS_TRAFFIC,
            CAT => LABEL_C_AP_TRAFFIC,
            SAT => LABEL_S_AP_TRAFFIC,
            _ => [0; 96 / 8],
        }
    }
}

enum Label {
    RES_BINDER__,
    EXT_BINDER__,
    C_E_TRAFFIC_,
    E_EXP_MASTER,
    EXP_MASTER__,
    RES_MASTER__,
    C_HS_TRAFFIC,
    S_HS_TRAFFIC,
    DERIVED_____,
    C_AP_TRAFFIC,
    S_AP_TRAFFIC,
    RESUMPTION__,
}
use Label::*;

fn convert_label(label: Bytes) -> Option<Label> {
    match &label.declassify()[..] {
        [101, 120, 116, 032, 098, 105, 110, 100, 101, 114] => Some(EXT_BINDER__),
        [114, 101, 115, 032, 098, 105, 110, 100, 101, 114] => Some(RES_BINDER__),
        [099, 032, 101, 032, 116, 114, 097, 102, 102, 105, 099] => Some(C_E_TRAFFIC_),
        [101, 032, 101, 120, 112, 032, 109, 097, 115, 116, 101, 114] => Some(E_EXP_MASTER),
        [099, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099] => Some(C_AP_TRAFFIC),
        [115, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099] => Some(S_AP_TRAFFIC),
        [101, 120, 112, 032, 109, 097, 115, 116, 101, 114] => Some(EXP_MASTER__),
        [114, 101, 115, 032, 109, 097, 115, 116, 101, 114] => Some(RES_MASTER__),
        [100, 101, 114, 105, 118, 101, 100] => Some(DERIVED_____),
        [099, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099] => Some(C_HS_TRAFFIC),
        [115, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099] => Some(S_HS_TRAFFIC),
        [82, 69, 83, 85, 77, 80, 84, 73, 79, 78] => Some(RESUMPTION__),
        _ => None,
    }
}

type TagKey = (TLSnames, Key);

pub(crate) fn xtr(
    k_a: TLSnames,
    k_b: TLSnames,
    alg: &HashAlgorithm,
    ikm: &Bytes,
    salt: &Bytes,
) -> Result<TagKey, TLSError> {
    let k_n = match (k_a, k_b) {
        (PSK, ZeroSalt) => ES,
        (ESalt, DH) => HS,
        (HSalt, ZeroIKM) => AS,
        _ => Err(INCORRECT_STATE)?,
    };

    Ok((k_n, hkdf_extract(alg, ikm, salt)?))
}

fn xpd(
    k: TLSnames,
    hash_algorithm: &HashAlgorithm,
    key: &Key,
    label: Bytes,
    transcript_hash: &Digest,
) -> Result<TagKey, TLSError> {
    let n: TLSnames = match (k, convert_label(label.clone())) {
        (ES, Some(EXT_BINDER__ | RES_BINDER__)) => Bind,
        (Bind, None) => Binder,
        (ES, Some(C_E_TRAFFIC_)) => CET,
        (ES, Some(E_EXP_MASTER)) => EEM,
        (ES, Some(DERIVED_____)) => ESalt,

        (HS, Some(C_HS_TRAFFIC)) => CHT,
        (HS, Some(S_HS_TRAFFIC)) => SHT,
        (HS, Some(DERIVED_____)) => HSalt,

        (AS, Some(C_AP_TRAFFIC)) => CAT,
        (AS, Some(S_AP_TRAFFIC)) => SAT,
        (AS, Some(EXP_MASTER__)) => EAM,
        (AS, Some(RES_MASTER__)) => RM,

        (RM, Some(RESUMPTION__)) => PSK,

        _ => Err(INCORRECT_STATE)?,
    };

    Ok((
        n,
        hkdf_expand_label(
            hash_algorithm,
            key,
            label,
            transcript_hash,
            hash_algorithm.hash_len(),
        )?,
    ))
}
