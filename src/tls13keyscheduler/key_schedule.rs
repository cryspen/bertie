use crate::{
    tls13crypto::{hkdf_expand, hkdf_extract, hmac_tag, Digest, HashAlgorithm, Key},
    tls13formats::*,
    tls13utils::*,
};
use std::collections::HashMap;
use std::vec;

/* TLS 1.3 Key Schedule: See RFC 8446 Section 7 */

/// HKDF expand with a `label`.
#[cfg_attr(feature = "hax-pv", hax_lib::pv_constructor)]
pub(crate) fn hkdf_expand_label(
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

/// Get an empty key of the correct size.
pub(crate) fn zero_salt(ks: &mut TLSkeyscheduler, alg: &HashAlgorithm) -> Handle {
    let handle = Handle {
        name: ZeroSalt,
        alg: alg.clone(),
        level: 0,
    };
    set_by_handle(
        ks,
        &handle,
        Bytes::zeroes(1), // alg.hash_len()
    ); // 1 bit-length, multiple introduce redundancy ?
    handle
}

/// Get an empty key of the correct size.
pub(crate) fn no_psk(ks: &mut TLSkeyscheduler, alg: &HashAlgorithm) -> Handle // TagKey
{
    let handle = Handle {
        name: PSK,
        alg: alg.clone(),
        level: 0,
    };
    set_by_handle(ks, &handle, Bytes::zeroes(alg.hash_len()));
    handle
}

/// Get an empty key of the correct size.
pub(crate) fn zero_ikm(ks: &mut TLSkeyscheduler, alg: &HashAlgorithm) -> Handle {
    let handle = Handle {
        name: ZeroIKM,
        alg: alg.clone(),
        level: 0,
    };
    set_by_handle(ks, &handle, Bytes::zeroes(alg.hash_len()));
    handle
}

pub trait KeySchedule<N> {
    fn labels(a: N, b: bool) -> Result<Bytes, TLSError>; // Bit string of size 96 (8*12)
    fn prnt_n(a: N) -> (Option<N>, Option<N>);

    // key mapping
    fn get(&self, name: N, level: u8, h: (N, HashAlgorithm, u8)) -> Option<Key>;
    fn set(&mut self, name: N, level: u8, h: (N, HashAlgorithm, u8), k: Key);

    fn hash(d: &Bytes) -> Bytes;
}

pub struct TLSkeyscheduler {
    pub keys: HashMap<(TLSnames, HashAlgorithm, u8), Key>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
#[allow(clippy::upper_case_acronyms)]
pub enum TLSnames {
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
    KEM,
    ZeroIKM, // 0^len(alg)
}
use TLSnames::*;

impl KeySchedule<TLSnames> for TLSkeyscheduler {
    fn prnt_n(a: TLSnames) -> (Option<TLSnames>, Option<TLSnames>) {
        match a {
            ES => (Some(ZeroSalt), Some(PSK)),
            EEM | CET | Bind => (Some(ES), None),
            Binder => (Some(Bind), None),
            HS => (Some(ESalt), Some(KEM)),
            SHT | CHT | HSalt => (Some(HS), None),
            AS => (Some(HSalt), Some(ZeroIKM)),
            RM | CAT | SAT | EAM => (Some(AS), None),
            PSK => (Some(RM), None),
            ZeroSalt | KEM | ZeroIKM => (None, None),
            ESalt => (Some(ES), None), // (todo!(), None),
        }
    }

    fn labels(a: TLSnames, b: bool) -> Result<Bytes, TLSError> {
        // [u8; 12]
        Ok(label_to_bytes(match a {
            Bind => {
                if b {
                    RES_BINDER__
                } else {
                    EXT_BINDER__
                }
            }
            RM => RES_MASTER__,
            ESalt | HSalt => DERIVED_____,
            EEM | EAM => E_EXP_MASTER,
            CET => C_E_TRAFFIC_,
            Binder => ____________,
            SHT => S_HS_TRAFFIC,
            CHT => C_HS_TRAFFIC,
            CAT => C_AP_TRAFFIC,
            SAT => S_AP_TRAFFIC,
            _ => Err(INCORRECT_STATE)?,
        }))
    }

    fn get(&self, name: TLSnames, level: u8, h: (TLSnames, HashAlgorithm, u8)) -> Option<Key> {
        self.keys.get(&h).cloned()
    }

    fn set(&mut self, name: TLSnames, level: u8, h: (TLSnames, HashAlgorithm, u8), k: Key) {
        self.keys.insert(h, k);
    }

    // TODO:
    fn hash(d: &Bytes) -> Bytes {
        d.clone()
    }
}

#[derive(Debug, PartialEq, Eq)]
#[allow(non_camel_case_types)]
#[allow(clippy::just_underscores_and_digits)]
pub(crate) enum Label {
    ____________,
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
    } else if l == [82, 69, 83, 85, 77, 80, 84, 73, 79, 78] {
        Some(RESUMPTION__)
    } else if l.is_empty() {
        Some(____________)
    } else {
        None
    }
}

#[allow(clippy::just_underscores_and_digits)]
#[cfg_attr(feature = "hax-pv", hax_lib::pv_constructor)]
fn label_to_bytes(label: Label) -> Bytes {
    match label {
        EXT_BINDER__ => vec![101, 120, 116, 032, 098, 105, 110, 100, 101, 114].into(),
        RES_BINDER__ => vec![114, 101, 115, 032, 098, 105, 110, 100, 101, 114].into(),
        C_E_TRAFFIC_ => vec![099, 032, 101, 032, 116, 114, 097, 102, 102, 105, 099].into(),
        E_EXP_MASTER => vec![101, 032, 101, 120, 112, 032, 109, 097, 115, 116, 101, 114].into(),
        C_AP_TRAFFIC => vec![099, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099].into(),
        S_AP_TRAFFIC => vec![115, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099].into(),
        EXP_MASTER__ => vec![101, 120, 112, 032, 109, 097, 115, 116, 101, 114].into(),
        RES_MASTER__ => vec![114, 101, 115, 032, 109, 097, 115, 116, 101, 114].into(),
        DERIVED_____ => vec![100, 101, 114, 105, 118, 101, 100].into(),
        C_HS_TRAFFIC => vec![099, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099].into(),
        S_HS_TRAFFIC => vec![115, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099].into(),
        RESUMPTION__ => vec![82, 69, 83, 85, 77, 80, 84, 73, 79, 78].into(),
        ____________ => vec::Vec::<u8>::new().into(),
    }
}

#[derive(Clone)]
pub struct TagKey {
    pub alg: HashAlgorithm,
    pub tag: TLSnames,
    pub val: Key,
}

pub(crate) fn xtr_alg(alg: &HashAlgorithm, k1: &Key, k2: &Key) -> Result<Bytes, TLSError> {
    hkdf_extract(alg, k1, k2)
}

pub(crate) fn xpd_alg(
    alg: &HashAlgorithm,
    k1: &Key,
    label: Bytes,
    d: &Digest,
) -> Result<Bytes, TLSError> {
    let kvt = convert_label(label.clone());
    if kvt == Some(____________) {
        hmac_tag(alg, k1, d)
    } else {
        hkdf_expand_label(alg, k1, label, d, alg.hash_len())
    }
}

pub(crate) fn xtr(k1: &TagKey, k2: &TagKey) -> Result<TagKey, TLSError> {
    let val = xtr_alg(&k1.alg, &k1.val, &k2.val)?;

    Ok(TagKey {
        alg: k1.alg,
        tag: k1.tag,
        val,
    })
}

pub(crate) fn xpd(k1: &TagKey, label: Bytes, d: &Digest) -> Result<TagKey, TLSError> {
    let alg = k1.clone().alg;
    let v = k1.clone().val;
    let val = xpd_alg(&alg, &v, label, d)?;

    Ok(TagKey {
        tag: k1.tag,
        alg,
        val,
    })
}

#[derive(Clone, Debug)]
pub struct Handle {
    pub name: TLSnames,
    pub alg: HashAlgorithm,
    pub level: u8,
}

pub(crate) fn xpd_angle(
    name: TLSnames,
    label: Bytes,
    parrent_handle: &Handle,
    args: &Bytes,
) -> Result<Handle, TLSError> {
    Ok(Handle {
        name,
        alg: parrent_handle.alg,
        level: parrent_handle.level,
    })
}

#[cfg_attr(feature = "hax-pv", hax_lib::pv_constructor)]
pub fn tagkey_from_handle(ks: &TLSkeyscheduler, handle: &Handle) -> Result<TagKey, TLSError> {
    Ok(TagKey {
        alg: handle.alg,
        tag: handle.name,
        val: get_by_handle(ks, handle)?,
    })
}

#[cfg_attr(feature = "hax-pv", hax_lib::pv_constructor)]
pub fn set_by_handle(ks: &mut TLSkeyscheduler, handle: &Handle, key: Key) {
    ks.set(
        handle.name,
        handle.level,
        (handle.name, handle.alg, handle.level),
        key,
    );
}

#[cfg_attr(feature = "hax-pv", hax_lib::pv_constructor)]
pub fn get_by_handle(ks: &TLSkeyscheduler, handle: &Handle) -> Result<Key, TLSError> {
    ks.get(
        handle.name,
        handle.level,
        (handle.name, handle.alg, handle.level),
    ).ok_or(INCORRECT_STATE)
}

#[allow(non_snake_case)]
#[allow(clippy::assign_op_pattern)]
#[cfg_attr(
    feature = "hax-pv",
    hax_lib::proverif::before(
        "fun extern__XPD(
                $:{TLSnames},
                nat,
                $:{Handle},
                bool,
                $:{Bytes}
         )
     : $:{Handle}."
    )
)]
#[cfg_attr(
    feature = "hax-pv",
    hax_lib::proverif::replace_body(
        "(extern__XPD(
              n,
              l,
              h1,
              r,
              args
          )
       )"
    )
)]
pub fn XPD(
    ks: &mut TLSkeyscheduler,
    n: TLSnames,
    mut l: u8,
    h1: &Handle,
    r: bool,
    args: &Bytes,
) -> Result<Handle, TLSError> {
    let (n1, _) = TLSkeyscheduler::prnt_n(n);
    let label = TLSkeyscheduler::labels(n, r)?;

    let h = xpd_angle(n, label.clone(), h1, args)?;
    let n1_unwrap = n1.ok_or(INCORRECT_STATE)?;
    let k1 = ks
        .get(n1_unwrap, l, (h1.name, h1.alg, h1.level))
        .ok_or(INCORRECT_STATE)?;

    let k: TagKey = if n == PSK {
        l = l + 1;
        xpd(
            &TagKey {
                alg: h1.alg,
                tag: h1.name,
                val: k1,
            },
            label,
            args,
        )?
    } else {
        let d = TLSkeyscheduler::hash(args);
        xpd(
            &TagKey {
                alg: h1.alg,
                tag: h1.name,
                val: k1,
            },
            label,
            &d,
        )?
    };
    ks.set(n, l, (h.name, h.alg, h.level), k.val);

    Ok(h)
}

pub(crate) fn xtr_angle(name: TLSnames, left: Handle, right: Handle) -> Result<Handle, TLSError> {
    Ok(Handle {
        alg: left.alg,
        name,
        level: left.level,
    })
}

#[allow(non_snake_case)]
#[cfg_attr(
    feature = "hax-pv",
    hax_lib::proverif::before(
        "fun extern__XTR(
                nat,
                $:{TLSnames},
                $:{Handle},
                $:{Handle}
         )
     : $:{Handle}."
    )
)]
#[cfg_attr(
    feature = "hax-pv",
    hax_lib::proverif::replace_body(
        "(extern__XTR(
              level,
              name,
              h1,
              h2
          )
       )"
    )
)]
#[hax_lib::fstar::verification_status(lax)]
pub(crate) fn XTR(
    ks: &mut TLSkeyscheduler,
    level: u8,
    name: TLSnames,
    h1: &Handle,
    h2: &Handle,
) -> Result<Handle, TLSError> {
    let (n1, n2) = TLSkeyscheduler::prnt_n(name);
    let h = xtr_angle(name, h1.clone(), h2.clone())?;
    let n1_unwrap = n1.ok_or(INCORRECT_STATE)?;
    let n2_unwrap = n2.ok_or(INCORRECT_STATE)?;
    let k1 = ks
        .get(n1_unwrap, level, (h1.name, h1.alg, h1.level))
        .ok_or(INCORRECT_STATE)?;
    let k2 = ks
        .get(n2_unwrap, level, (h2.name, h2.alg, h2.level))
        .ok_or(INCORRECT_STATE)?;
    let k = xtr(
        &TagKey {
            alg: h1.alg,
            tag: h1.name,
            val: k1,
        },
        &TagKey {
            alg: h2.alg,
            tag: h2.name,
            val: k2,
        },
    )?;
    ks.set(name, level, (h.name, h.alg, h.level), k.val);
    Ok(h)
}
