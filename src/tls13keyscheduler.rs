use crate::{
    tls13crypto::{
        hkdf_expand, hkdf_extract, hmac_tag, AeadAlgorithm, AeadKey, AeadKeyIV, Algorithms, Digest,
        HashAlgorithm, Key, MacKey, Psk,
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

/////////////////////////////////////////////////

trait KeySchedule<N> {
    fn labels(a: N, b: bool) -> Result<Bytes, TLSError>; // Bit string of size 96 (8*12)
    fn prnt_n(a: N) -> (Option<N>, Option<N>);
}

pub(crate) struct TLSkeyscheduler {}

#[derive(Copy, Clone, PartialEq)]
pub(crate) enum TLSnames {
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

    fn labels(a: TLSnames, b: bool) -> Result<Bytes, TLSError> {
        // [u8; 12]
        Ok(match a {
            // EEM => LABEL_E_EXP_MASTER,
            // CET => LABEL_C_E_TRAFFIC,
            // Binder => LABEL_RES_BINDER,
            SHT => LABEL_S_HS_TRAFFIC,
            CHT => LABEL_C_HS_TRAFFIC,
            CAT => LABEL_C_AP_TRAFFIC,
            SAT => LABEL_S_AP_TRAFFIC,
            _ => Err(INCORRECT_STATE)?,
        }
        .into())
    }
}

pub(crate) enum Label {
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
    let l = &label.declassify()[..];
    if l == [101, 120, 116, 032, 098, 105, 110, 100, 101, 114] {
        Some(EXT_BINDER__)
    } else if l == [114, 101, 115, 032, 098, 105, 110, 100, 101, 114] {
        Some(RES_BINDER__)
    } else if l == [099, 032, 101, 032, 116, 114, 097, 102, 102, 105, 099] {
        Some(C_E_TRAFFIC_)
    } else if l == [101, 032, 101, 120, 112, 032, 109, 097, 115, 116, 101, 114] {
        Some(E_EXP_MASTER)
    } else if l == [099, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099] {
        Some(C_AP_TRAFFIC)
    } else if l == [115, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099] {
        Some(S_AP_TRAFFIC)
    } else if l == [101, 120, 112, 032, 109, 097, 115, 116, 101, 114] {
        Some(EXP_MASTER__)
    } else if l == [114, 101, 115, 032, 109, 097, 115, 116, 101, 114] {
        Some(RES_MASTER__)
    } else if l == [100, 101, 114, 105, 118, 101, 100] {
        Some(DERIVED_____)
    } else if l == [099, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099] {
        Some(C_HS_TRAFFIC)
    } else if l == [115, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099] {
        Some(S_HS_TRAFFIC)
    } else {
        // if l == [82, 69, 83, 85, 77, 80, 84, 73, 79, 78] =>
        Some(RESUMPTION__)
    }

    // Matching slice unsupported..
    // match &label.declassify()[..] {
    //     [101, 120, 116, 032, 098, 105, 110, 100, 101, 114] => Some(EXT_BINDER__),
    //     [114, 101, 115, 032, 098, 105, 110, 100, 101, 114] => Some(RES_BINDER__),
    //     [099, 032, 101, 032, 116, 114, 097, 102, 102, 105, 099] => Some(C_E_TRAFFIC_),
    //     [101, 032, 101, 120, 112, 032, 109, 097, 115, 116, 101, 114] => Some(E_EXP_MASTER),
    //     [099, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099] => Some(C_AP_TRAFFIC),
    //     [115, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099] => Some(S_AP_TRAFFIC),
    //     [101, 120, 112, 032, 109, 097, 115, 116, 101, 114] => Some(EXP_MASTER__),
    //     [114, 101, 115, 032, 109, 097, 115, 116, 101, 114] => Some(RES_MASTER__),
    //     [100, 101, 114, 105, 118, 101, 100] => Some(DERIVED_____),
    //     [099, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099] => Some(C_HS_TRAFFIC),
    //     [115, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099] => Some(S_HS_TRAFFIC),
    //     [82, 69, 83, 85, 77, 80, 84, 73, 79, 78] => Some(RESUMPTION__),
    //     _ => None,
    // }
}

#[derive(Clone)]
pub(crate) struct TagKey {
    pub(crate) tag: TLSnames,
    pub(crate) val: Key,
}

pub(crate) fn xtr(alg: &HashAlgorithm, ikm: &TagKey, salt: &TagKey) -> Result<TagKey, TLSError> {
    let k_n = match (ikm.tag, salt.tag) {
        (PSK, ZeroSalt) => ES,
        // (ESalt, DH) => HS,
        (DH, ESalt) => HS, // TODO: Should use ^ instead
        // (HSalt, ZeroIKM) => AS,
        (ZeroIKM, HSalt) => AS, // TODO: should use ^ instead
        _ => Err(INCORRECT_STATE)?,
    };

    Ok(TagKey {
        tag: k_n,
        val: hkdf_extract(alg, &ikm.val, &salt.val)?,
    })
}

fn xpd(
    hash_algorithm: &HashAlgorithm,
    key: &TagKey,
    label: Bytes,
    transcript_hash: &Digest,
) -> Result<TagKey, TLSError> {
    let n: TLSnames = match (key.tag, convert_label(label.clone())) {
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

    Ok(TagKey {
        tag: n,
        val: hkdf_expand_label(
            hash_algorithm,
            &key.val,
            label,
            transcript_hash,
            hash_algorithm.hash_len(),
        )?,
    })
}

struct Handle {
    name: TLSnames,
    key: Key,
    alg: HashAlgorithm,
    level: u8,
}

fn xpd_angle(
    name: TLSnames,
    label: Bytes,
    parrent_handle: &Handle,
    args: &Bytes,
) -> Result<Handle, TLSError> {
    let k = xpd(
        &parrent_handle.alg,
        &TagKey {
            tag: parrent_handle.name,
            val: parrent_handle.key.clone(),
        },
        label,
        args,
    )?;
    Ok(Handle {
        name: k.tag,
        key: k.val,
        alg: parrent_handle.alg,
        level: parrent_handle.level,
    })
}

// fn XPD<T, KS : KeySchedule<TLSnames>>(n : TLSnames,l: u8,h1: &Handle,r : bool,args: &Bytes) -> Result<(), TLSError>{
//     let (n1, _) = KS::prnt_n(n);
//     let label = KS::labels(n, r)?;
//     let h = xpd_angle(n,label, h1, args)?;
//     let (k1,hon) = GET(n1,l,h1);

//     let mut l = l;
//     let k : TagKey;

//     if n == PSK {
//         l = l+1;
//         k = xpd(k1, label, args);
//     } else {
//         d = HASH(args);
//         k = xpd(k1, label, d);
//     }
//     let h = SET(n,l,h,hon,k);

//     return h
// }

// fn next_keys(keys: Vec<&TagKey>, data: Vec<Bytes>) -> Vec<&TagKey> {
//     match keys.iter().map(|x| x.tag).collect::<Vec<_>>()[..] {
//         [PSK] => vec![],
//         [ES] => vec![],
//         _ => todo!(),
//     }
// }

/////////
// Description from papaer
/////////

/// Get an empty key of the correct size.
pub(crate) fn zero_salt(alg: &HashAlgorithm) -> TagKey {
    TagKey {
        tag: ZeroSalt,
        val: Bytes::zeroes(alg.hash_len()),
    }
}

/// Get an empty key of the correct size.
pub(crate) fn no_psk(alg: &HashAlgorithm) -> TagKey {
    TagKey {
        tag: PSK,
        val: Bytes::zeroes(alg.hash_len()),
    }
}

/// Get an empty key of the correct size.
pub(crate) fn zero_ikm(alg: &HashAlgorithm) -> TagKey {
    TagKey {
        tag: ZeroIKM,
        val: Bytes::zeroes(alg.hash_len()),
    }
}

////
// Key package
////

// fn UNQ(n,h,hon,k) {

// }

// struct KPackage {
//     n : TLSnames,
//     l : u8,
//     K : std::collections::HashMap<[u8; 12], (TagKey, bool)>
// }

// impl KPackage {
//     // fn SET(self, h : &Handle, hon : bool, k_star : TagKey){
//     //     assert!(h.name == self.n);
//     //     assert!(h.level == self.l);
//     //     assert!(k_star.alg == h.alg);
//     //     if self.K[h].is_some() {
//     //         return h;
//     //     }
//     //     let mut k = k_star.untag();
//     //     assert!(h.alg.len() == k.size());
//     //     if b {
//     //         if hon {
//     //             k = random_sample(h.alg.len())
//     //         }
//     //     }
//     //     UNQ(n,h,hon,k);
//     //     self.K[h] = (k, hon);
//     //     return h;
//     // }

//     fn GET(self, n : TLSnames, l: u8, h : &Handle){
//         assert!(self.K.contains_key(h));
//         let (k_star, hon) = self.K[h];
//         let k = tag(h, k_star);
//         return (k, hon)
//     }
// }
