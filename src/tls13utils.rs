//use core::num::dec2flt::parse;

use crate::*;

// Local error codes
pub type TLSError = u8;
pub const UNSUPPORTED_ALGORITHM: TLSError = 1u8;
pub const CRYPTO_ERROR: TLSError = 2u8;
pub const INSUFFICIENT_ENTROPY: TLSError = 3u8;
pub const INCORRECT_ARRAY_LENGTH: TLSError = 4u8;

pub const INCORRECT_STATE: TLSError = 128u8;
pub const ZERO_RTT_DISABLED: TLSError = 129u8;
pub const PAYLOAD_TOO_LONG: TLSError = 130u8;
pub const PSK_MODE_MISMATCH: TLSError = 131u8;
pub const NEGOTIATION_MISMATCH: TLSError = 132u8;
pub const PARSE_FAILED: TLSError = 133u8;
pub const INSUFFICIENT_DATA: TLSError = 134u8;
pub const UNSUPPORTED: TLSError = 135u8;
pub const INVALID_COMPRESSION_LIST: TLSError = 136u8;
pub const PROTOCOL_VERSION_ALERT: TLSError = 137u8;
pub const APPLICATION_DATA_INSTEAD_OF_HANDSHAKE: TLSError = 138u8;
pub const MISSING_KEY_SHARE: TLSError = 139u8;
pub const INVALID_SIGNATURE: TLSError = 140u8;
pub const GOT_HANDSHAKE_FAILURE_ALERT: TLSError = 141u8;

pub fn error_string(c: u8) -> String {
    format!("{}", c)
}

pub fn tlserr<T>(err: TLSError) -> Result<T, TLSError> {
    let bt = backtrace::Backtrace::new();
    println!("{:?}", bt);
    Err(err)
}

/*
pub fn check_eq_size(s1: TLSError, s2: usize) -> Result<()> {
    if s1 == s2 {Ok(())}
    else {Err(parse_failed())}
}*/

pub trait Declassify {
    type T;
    fn declassify(&self) -> Self::T;
}

#[cfg(feature = "secret_integers")]
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct U8(u8);
#[cfg(feature = "secret_integers")]
impl core::ops::BitXor for U8 {
    type Output = U8;
    fn bitxor(self, rhs: Self) -> Self::Output {
        U8(self.0 ^ rhs.0)
    }
}
#[cfg(feature = "secret_integers")]
impl From<u8> for U8 {
    fn from(x: u8) -> U8 {
        U8(x)
    }
}
#[cfg(feature = "secret_integers")]
impl Declassify for U8 {
    type T = u8;
    fn declassify(&self) -> u8 {
        self.0
    }
}

#[cfg(not(feature = "secret_integers"))]
type U8 = u8;
#[cfg(not(feature = "secret_integers"))]
pub fn U8(x: u8) -> U8 {
    x
}
#[cfg(not(feature = "secret_integers"))]
impl Declassify for U8 {
    type t = u8;
    fn declassify(&self) -> u8 {
        *self
    }
}

impl From<&u8> for U8 {
    fn from(x: &u8) -> U8 {
        U8(*x)
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct U16(u16);

impl From<u16> for U16 {
    fn from(x: u16) -> U16 {
        U16(x)
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct U32(u32);

impl From<u32> for U32 {
    fn from(x: u32) -> U32 {
        U32(x)
    }
}

impl core::ops::Add for U32 {
    type Output = U32;
    fn add(self, y: U32) -> U32 {
        U32(self.0 + y.0)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Bytes(Vec<U8>);

impl From<Vec<u8>> for Bytes {
    fn from(x: Vec<u8>) -> Bytes {
        Bytes(x.iter().map(|x| x.into()).collect())
    }
}

impl Declassify for Bytes {
    type T = Vec<u8>;
    fn declassify(&self) -> Vec<u8> {
        self.0.iter().map(|x| x.declassify()).collect()
    }
}

impl Bytes {
    pub fn declassify_array<const C: usize>(&self) -> Result<[u8; C], TLSError> {
        self.declassify()
            .try_into()
            .map_err(|_| INCORRECT_ARRAY_LENGTH)
    }
}

impl From<&[u8]> for Bytes {
    fn from(x: &[u8]) -> Bytes {
        x.to_vec().into()
    }
}

impl From<&[U8]> for Bytes {
    fn from(x: &[U8]) -> Bytes {
        Bytes(x.to_vec())
    }
}

impl<const C: usize> From<[u8; C]> for Bytes {
    fn from(x: [u8; C]) -> Bytes {
        x.to_vec().into()
    }
}

impl<const C: usize> From<&[u8; C]> for Bytes {
    fn from(x: &[u8; C]) -> Bytes {
        x.to_vec().into()
    }
}

impl U32 {
    pub fn from_be_bytes(x: &Bytes) -> Result<U32, TLSError> {
        Ok(U32(u32::from_be_bytes(x.declassify_array()?)))
    }
    pub fn to_be_bytes(&self) -> Bytes {
        (self.0.to_be_bytes().to_vec()).into()
    }
    pub fn declassify(&self) -> u32 {
        self.0
    }
}

impl U16 {
    pub fn from_be_bytes(x: &Bytes) -> Result<U16, TLSError> {
        Ok(U16(u16::from_be_bytes(x.declassify_array()?)))
    }
    pub fn to_be_bytes(&self) -> Bytes {
        (self.0.to_be_bytes().to_vec()).into()
    }
    pub fn declassify(&self) -> u16 {
        self.0
    }
}

pub fn bytes(x: &[u8]) -> Bytes {
    x.into()
}
pub fn bytes1(x: u8) -> Bytes {
    [x].into()
}
pub fn bytes2(x: u8, y: u8) -> Bytes {
    [x, y].into()
}

impl core::ops::Index<usize> for Bytes {
    type Output = U8;
    fn index(&self, x: usize) -> &U8 {
        &self.0[x]
    }
}

impl core::ops::IndexMut<usize> for Bytes {
    fn index_mut(&mut self, i: usize) -> &mut U8 {
        &mut self.0[i]
    }
}

impl core::ops::Index<core::ops::Range<usize>> for Bytes {
    type Output = [U8];
    fn index(&self, x: core::ops::Range<usize>) -> &[U8] {
        &self.0[x]
    }
}

impl core::ops::IndexMut<core::ops::Range<usize>> for Bytes {
    fn index_mut(&mut self, x: core::ops::Range<usize>) -> &mut [U8] {
        &mut self.0[x]
    }
}

impl Bytes {
    pub fn new() -> Bytes {
        Bytes(Vec::new())
    }
    pub fn zeroes(len: usize) -> Bytes {
        Bytes(vec![U8(0); len])
    }
    pub fn with_capacity(len: usize) -> Bytes {
        Bytes(Vec::with_capacity(len))
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn push(&mut self, x: U8) {
        self.0.push(x)
    }
    pub fn extend_from_slice(&mut self, x: &Bytes) {
        self.0.extend_from_slice(&x.0)
    }

    pub fn from_slice(s: &[u8]) -> Bytes {
        s.into()
    }
    pub fn from_hex(s: &str) -> Bytes {
        let s: String = s.split_whitespace().collect();
        if s.len() % 2 == 0 {
            Bytes(
                (0..s.len())
                    .step_by(2)
                    .map(|i| {
                        s.get(i..i + 2)
                            .and_then(|sub| (u8::from_str_radix(sub, 16).ok()).map(U8))
                    })
                    .collect::<Option<Vec<U8>>>()
                    .expect("Not a hex string1"),
            )
        } else {
            None.expect("Not a hex string2")
        }
    }

    pub fn to_hex(&self) -> String {
        let strs: Vec<String> = self
            .0
            .iter()
            .map(|b| format!("{:02x}", b.declassify()))
            .collect();
        strs.join("")
    }
    pub fn slice_range(&self, r: core::ops::Range<usize>) -> Bytes {
        self.0[r.start..r.end].into()
    }
    pub fn slice(&self, start: usize, len: usize) -> Bytes {
        self.0[start..start + len].into()
    }
    pub fn concat(&self, x: &Bytes) -> Bytes {
        let mut res = Vec::new();
        res.extend_from_slice(&self.0);
        res.extend_from_slice(&x.0);
        Bytes(res)
    }

    pub fn update_slice(&self, st: usize, src: &Bytes, beg: usize, len: usize) -> Bytes {
        let mut res = self.clone();
        for i in 0..len {
            res[st + i] = src[beg + i];
        }
        res
    }

    /* pub fn to_array<const sz:usize>(&self) -> Result<[U8; sz],TLSError> {
        if self.len() == sz {
            Ok(self.0.clone().try_into().unwrap())
        } else {Err(PARSE_FAILED)}
    }*/
}

pub fn check(b: bool) -> Result<(), TLSError> {
    if b {
        Ok(())
    } else {
        Err(parse_failed())
    }
}

pub fn eq1(b1: U8, b2: U8) -> bool {
    b1.declassify() == b2.declassify()
}
pub fn check_eq1(b1: U8, b2: U8) -> Result<(), TLSError> {
    if eq1(b1, b2) {
        Ok(())
    } else {
        Err(parse_failed())
    }
}

// TODO: This function should short-circuit once hax supports returns within loops
pub fn eq(b1: &Bytes, b2: &Bytes) -> bool {
    if b1.len() != b2.len() {
        false
    } else {
        let mut b: bool = true;
        for i in 0..b1.len() {
            if !eq1(b1[i], b2[i]) {
                b = false;
            };
        }
        return b;
    }
}

pub fn check_eq(b1: &Bytes, b2: &Bytes) -> Result<(), TLSError> {
    let b = eq(&b1, &b2);
    if b {
        Ok(())
    } else {
        Err(parse_failed())
    }
}

// TODO: This function should short-circuit once hax supports returns within loops
pub fn check_mem(b1: &Bytes, b2: &Bytes) -> Result<(), TLSError> {
    if b2.len() % b1.len() != 0 {
        Err(parse_failed())
    } else {
        let mut b = false;
        for i in 0..(b2.len() / b1.len()) {
            if eq(&b1, &b2.slice_range(i * b1.len()..(i + 1) * b1.len())) {
                b = true;
            }
        }
        return if b { Ok(()) } else { Err(parse_failed()) };
    }
}

pub fn lbytes1(b: &Bytes) -> Result<Bytes, TLSError> {
    let len = b.len();
    if len >= 256 {
        Err(PAYLOAD_TOO_LONG)
    } else {
        let mut lenb = Bytes::new();
        lenb.push((len as u8).into());
        lenb.extend_from_slice(&b);
        Ok(lenb)
    }
}

pub fn lbytes2(b: &Bytes) -> Result<Bytes, TLSError> {
    let len = b.len();
    if len >= 65536 {
        Err(PAYLOAD_TOO_LONG)
    } else {
        let len: Bytes = (U16(len as u16)).to_be_bytes();
        let mut lenb = Bytes::new();
        lenb.push(len[0]);
        lenb.push(len[1]);
        lenb.extend_from_slice(&b);
        Ok(lenb)
    }
}

pub fn lbytes3(b: &Bytes) -> Result<Bytes, TLSError> {
    let len = b.len();
    if len >= 16777216 {
        Err(PAYLOAD_TOO_LONG)
    } else {
        let len: Bytes = U32(len as u32).to_be_bytes();
        let mut lenb = Bytes::new();
        lenb.push(len[1]);
        lenb.push(len[2]);
        lenb.push(len[3]);
        lenb.extend_from_slice(&b);
        Ok(lenb)
    }
}

pub fn check_lbytes1(b: &Bytes) -> Result<usize, TLSError> {
    if b.len() < 1 {
        Err(parse_failed())
    } else {
        let l = b[0].declassify() as usize;
        if b.len() - 1 < l {
            Err(parse_failed())
        } else {
            Ok(l)
        }
    }
}

pub fn check_lbytes2(b: &Bytes) -> Result<usize, TLSError> {
    if b.len() < 2 {
        Err(parse_failed())
    } else {
        let l0 = b[0].declassify() as usize;
        let l1 = b[1].declassify() as usize;
        let l = l0 * 256 + l1;
        if b.len() - 2 < l as usize {
            Err(parse_failed())
        } else {
            Ok(l)
        }
    }
}

pub fn check_lbytes3(b: &Bytes) -> Result<usize, TLSError> {
    if b.len() < 3 {
        Err(parse_failed())
    } else {
        let l0 = b[0].declassify() as usize;
        let l1 = b[1].declassify() as usize;
        let l2 = b[2].declassify() as usize;
        let l = l0 * 65536 + l1 * 256 + l2;
        if b.len() - 3 < l {
            Err(parse_failed())
        } else {
            Ok(l)
        }
    }
}

pub fn check_lbytes1_full(b: &Bytes) -> Result<(), TLSError> {
    if check_lbytes1(b)? + 1 != b.len() {
        Err(parse_failed())
    } else {
        Ok(())
    }
}

pub fn check_lbytes2_full(b: &Bytes) -> Result<(), TLSError> {
    if check_lbytes2(b)? + 2 != b.len() {
        Err(parse_failed())
    } else {
        Ok(())
    }
}

pub fn check_lbytes3_full(b: &Bytes) -> Result<(), TLSError> {
    if check_lbytes3(b)? + 3 != b.len() {
        Err(parse_failed())
    } else {
        Ok(())
    }
}

// Handshake Data
pub struct HandshakeData(pub Bytes);

pub fn handshake_data(b: Bytes) -> HandshakeData {
    HandshakeData(b)
}
pub fn handshake_data_bytes(hd: &HandshakeData) -> Bytes {
    hd.0.clone()
}

pub fn handshake_data_len(p: &HandshakeData) -> usize {
    p.0.len()
}

pub fn handshake_concat(msg1: HandshakeData, msg2: &HandshakeData) -> HandshakeData {
    let HandshakeData(mut m1) = msg1;
    let HandshakeData(m2) = msg2;
    m1.0.extend_from_slice(&m2.0);
    HandshakeData(m1)
}

// Application Data
#[derive(PartialEq)]
pub struct AppData(Bytes);

pub fn app_data(b: Bytes) -> AppData {
    AppData(b)
}
pub fn app_data_bytes(a: AppData) -> Bytes {
    a.0
}

pub struct ServerDB(
    pub Bytes,
    pub Bytes,
    pub SignatureKey,
    pub Option<(Bytes, PSK)>,
);

pub fn lookup_db(
    algs: Algorithms,
    db: &ServerDB,
    sni: &Bytes,
    tkt: &Option<Bytes>,
) -> Result<(Bytes, SignatureKey, Option<PSK>), TLSError> {
    let ServerDB(server_name, cert, sk, psk_opt) = db;
    if eq(&sni, &Bytes::new()) || eq(&sni, &server_name) {
        match (psk_mode(&algs), tkt, psk_opt) {
            (true, Some(ctkt), Some((stkt, psk))) => {
                check_eq(ctkt, stkt)?;
                Ok((cert.clone(), sk.clone(), Some(psk.clone())))
            }
            (false, _, _) => Ok((cert.clone(), sk.clone(), None)),
            _ => Err(PSK_MODE_MISMATCH),
        }
    } else {
        Err(parse_failed())
    }
}

pub fn random_bytes(len: usize) -> Bytes {
    (0..len)
        .map(|_| rand::random::<u8>())
        .collect::<Vec<u8>>()
        .into()
}
