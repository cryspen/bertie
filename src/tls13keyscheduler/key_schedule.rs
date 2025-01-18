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
