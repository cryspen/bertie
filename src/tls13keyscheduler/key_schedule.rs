use crate::{
    tls13crypto::{hkdf_expand, hkdf_extract, hmac_tag, Digest, HashAlgorithm, Key},
    tls13formats::*,
    tls13utils::*,
};
use std::collections::HashMap;
use std::vec;

/* TLS 1.3 Key Schedule: See RFC 8446 Section 7 */

/// HKDF expand with a `label`.
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
#[cfg_attr(feature = "hax-pv", hax_lib::pv_constructor)]
pub(crate) fn zero_salt(ks: &mut TLSkeyscheduler, alg: &HashAlgorithm) -> Handle {
    let handle = Handle {
        alg: alg.clone(),
        name: ZeroSalt,
        level: 0,
    };
    let _ = set_by_handle(
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
        alg: alg.clone(),
        name: PSK,
        level: 0,
    };
    let _ = set_by_handle(ks, &handle, Bytes::zeroes(alg.hash_len()));
    handle
}

/// Get an empty key of the correct size.
pub(crate) fn zero_ikm(ks: &mut TLSkeyscheduler, alg: &HashAlgorithm) -> Handle {
    let handle = Handle {
        alg: alg.clone(),
        name: ZeroIKM,
        level: 0,
    };
    let _ = set_by_handle(ks, &handle, Bytes::zeroes(alg.hash_len()));
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
        self.keys.get(&h).map(|x| x.clone())
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
    } else if l == [] {
        Some(____________)
    } else {
        None
    }
}

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
    // hmac_tag(alg, k1, k2)
}

pub(crate) fn xpd_alg(
    alg: &HashAlgorithm,
    k1: &Key,
    label: Bytes,
    d: &Digest,
) -> Result<Bytes, TLSError> {
    let kvt = convert_label(label.clone());
    if kvt == Some(____________)
    // || kvt == None
    {
        hmac_tag(alg, k1, d)
    } else {
        hkdf_expand_label(alg, k1, label, d, alg.hash_len())
    }
}

pub(crate) fn xtr(k1: &TagKey, k2: &TagKey) -> Result<TagKey, TLSError> {
    // let k_n = match (k1.tag, k2.tag) {
    //     (PSK, ZeroSalt) => ES,
    //     (KEM, ESalt) => HS,
    //     (ZeroIKM, HSalt) => AS,
    //     _ => Err(INCORRECT_STATE)?,
    // };

    let val = xtr_alg(&k1.alg, &k1.val, &k2.val)?;

    Ok(TagKey {
        alg: k1.alg.clone(),
        tag: k1.tag.clone(),
        val,
    })
}

pub(crate) fn xpd(k1: &TagKey, label: Bytes, d: &Digest) -> Result<TagKey, TLSError> {
    let TagKey { alg, tag, val: k1 } = k1.clone();
    let val = xpd_alg(&alg, &k1, label, d)?;

    Ok(TagKey { tag, alg, val })
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
    // let n: TLSnames = match (parrent_handle.name, convert_label(label.clone())) {
    //     (ES, Some(EXT_BINDER__ | RES_BINDER__)) => Bind,
    //     (Bind, None) => Binder,
    //     (ES, Some(C_E_TRAFFIC_)) => CET,
    //     (ES, Some(E_EXP_MASTER)) => EEM,
    //     (ES, Some(DERIVED_____)) => ESalt,

    //     (HS, Some(C_HS_TRAFFIC)) => CHT,
    //     (HS, Some(S_HS_TRAFFIC)) => SHT,
    //     (HS, Some(DERIVED_____)) => HSalt,

    //     (AS, Some(C_AP_TRAFFIC)) => CAT,
    //     (AS, Some(S_AP_TRAFFIC)) => SAT,
    //     (AS, Some(EXP_MASTER__)) => EAM,
    //     (AS, Some(RES_MASTER__)) => RM,

    //     (RM, Some(RESUMPTION__)) => PSK,

    //     _ => Err(INCORRECT_STATE)?,
    // };

    Ok(Handle {
        name,
        // key: k.val,
        alg: parrent_handle.alg,
        level: parrent_handle.level,
    })
}

#[cfg_attr(feature = "hax-pv", hax_lib::pv_constructor)]
pub fn tagkey_from_handle(ks: &TLSkeyscheduler, handle: &Handle) -> Result<TagKey, TLSError> {
    Ok(TagKey {
        alg: handle.alg,
        tag: handle.name,
        val: get_by_handle(ks, handle).ok_or(INCORRECT_STATE)?,
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

// XXX: Make this a destructor for above
pub fn get_by_handle(ks: &TLSkeyscheduler, handle: &Handle) -> Option<Key> {
    ks.get(
        handle.name,
        handle.level,
        (handle.name, handle.alg, handle.level),
    )
}

#[allow(non_snake_case)]
#[cfg_attr(feature = "hax-pv", hax_lib::pv_constructor)]
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
    // let h =
    let _ = ks.set(n, l, (h.name, h.alg, h.level), k.val);
    // set(&mut self, name: N, level: u8, h: (N, HashAlgorithm, u8), hon: bool, k: (N, Key));

    Ok(h)
}

pub(crate) fn xtr_angle(name: TLSnames, left: Handle, right: Handle) -> Result<Handle, TLSError> {
    // let k_n = match (left.name, right.name) {
    //     (PSK, ZeroSalt) => ES,
    //     // (ESalt, DH) => HS,
    //     (DH, ESalt) => HS, // TODO: Should use ^ instead
    //     // (HSalt, ZeroIKM) => AS,
    //     (ZeroIKM, HSalt) => AS, // TODO: should use ^ instead
    //     _ => Err(INCORRECT_STATE)?,
    // };

    Ok(Handle {
        alg: left.alg,
        name,
        level: left.level,
    })
}

#[cfg_attr(feature = "hax-pv", hax_lib::pv_constructor)]
#[hax_lib::fstar::verification_status(lax)]
pub(crate) fn XTR(
    ks: &mut TLSkeyscheduler,
    level: u8,
    name: TLSnames,
    h1: &Handle,
    h2: &Handle,
) -> Result<Handle, TLSError> {
    let (n1, n2) = TLSkeyscheduler::prnt_n(name);
    // if h1.is_some() && h2.is_some() {
    //     assert_eq!(h1.unwrap().alg, h2.unwrap().alg)
    // }
    let h = xtr_angle(name, h1.clone(), h2.clone())?;
    let n1_unwrap = n1.ok_or(INCORRECT_STATE)?;
    let n2_unwrap = n2.ok_or(INCORRECT_STATE)?;
    let k1 = ks
        .get(n1_unwrap, level.clone(), (h1.name, h1.alg, h1.level))
        .ok_or(INCORRECT_STATE)?;
    let k2 = ks
        .get(n2_unwrap, level.clone(), (h2.name, h2.alg, h2.level))
        .ok_or(INCORRECT_STATE)?;
    let k = xtr(
        &TagKey {
            alg: h1.alg.clone(),
            tag: h1.name,
            val: k1,
        },
        &TagKey {
            alg: h2.alg.clone(),
            tag: h2.name,
            val: k2,
        },
    )?;
    // let hon = hon1 || hon2;
    // if b && hon2 {

    // }
    ks.set(name, level, (h.name, h.alg, h.level), k.val);
    Ok(h)
}

// fn nextKeys(
//     alg: &HashAlgorithm,
//     label: Option<Bytes>,
//     digest: &Digest,
//     key: &TagKey,
//     other_key: Option<&TagKey>,
//     resumption_bit: bool,
// ) -> Result<TagKey, TLSError> {
//     match (key.tag, label.clone().map_or(None, |x| convert_label(x)), other_key.map(|x| x.tag)) {
//         (PSK, None, Some(ZeroSalt)) => xtr(alg, key, other_key.unwrap()), // -> ES
//         (ES, Some(EXT_BINDER__ | RES_BINDER__), None) => xpd(
//             alg,
//             key,
//             label.unwrap(),
//             &Into::<Digest>::into(Vec::<u8>::new()),
//         ),
//         (Bind, Some(____________), None) => xpd(
//             alg,
//             key,
//             label.unwrap(),
//             &Into::<Digest>::into(Vec::<u8>::new()),
//         ),
//         (ES, Some(C_E_TRAFFIC_ | E_EXP_MASTER), None) => xpd(alg, key, label.unwrap(), digest),
//         (ES, Some(C_E_TRAFFIC_ | E_EXP_MASTER), None) => xpd(alg, key, label.unwrap(), digest),
//         _ => panic!(),
//     }
// }

// fn next_keys(keys: Vec<&TagKey>, data: Vec<Bytes>) -> Vec<&TagKey> {
//     match keys.iter().map(|x| x.tag).collect::<Vec<_>>()[..] {
//         [PSK] => vec![],
//         [ES] => vec![],
//         _ => todo!(),
//     }
// }

/////////
// Description from paper
/////////

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

// pub(crate) fn nextKeys(key: &TagKey, extra: Bytes, digest: &Digest, aead_algorithm: &AeadAlgorithm,) -> Vec<TagKey> {
//     // 0-RTT (k_cet)
//     derive_0rtt_keys(

//     // handshake messages (k_cht, k_sht)

//     // 1-RTT data (k_cat, k_sat)

//     // eksporter secrets (k_eem, k_eam)
// }
