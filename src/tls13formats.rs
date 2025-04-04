//! A module that for the formatting code needed by TLS 1.3
#![allow(clippy::manual_range_contains)]

#[cfg(not(feature = "secret_integers"))]
use crate::tls13utils::Declassify;
use crate::{
    tls13crypto::{
        zero_key, Algorithms, Digest, HashAlgorithm, Hmac, KemPk, Random, SignatureScheme,
    },
    tls13utils::{
        bytes1, bytes2, bytes_concat, check, check_eq, check_eq_slice, check_eq_with_slice,
        check_length_encoding_u16, check_length_encoding_u16_slice, check_length_encoding_u24,
        check_length_encoding_u8, check_length_encoding_u8_slice, check_mem, encode_length_u16,
        encode_length_u24, encode_length_u8, eq_slice, length_u16_encoded,
        length_u16_encoded_slice, length_u24_encoded, length_u8_encoded, parse_failed, tlserr,
        u32_as_be_bytes, Bytes, TLSError, APPLICATION_DATA_INSTEAD_OF_HANDSHAKE, DECODE_ERROR,
        INVALID_COMPRESSION_LIST, INVALID_SIGNATURE, MISSING_KEY_SHARE, PROTOCOL_VERSION_ALERT,
        PSK_MODE_MISMATCH, U32, U8, UNSUPPORTED_ALGORITHM,
    },
};

pub(crate) mod handshake_data;
#[cfg(not(bench))]
use handshake_data::{HandshakeData, HandshakeType};
#[cfg(bench)]
pub use handshake_data::{HandshakeData, HandshakeType};

#[cfg(feature = "hax-pv")]
use hax_lib::{pv_constructor, proverif};

// Well Known Constants

pub const LABEL_IV: [u8; 2] = [105, 118];
pub const LABEL_KEY: [u8; 3] = [107, 101, 121];
pub const LABEL_TLS13: [u8; 6] = [116, 108, 115, 049, 051, 032];
pub const LABEL_DERIVED: [u8; 7] = [100, 101, 114, 105, 118, 101, 100];
pub const LABEL_FINISHED: [u8; 8] = [102, 105, 110, 105, 115, 104, 101, 100];
pub const LABEL_RES_BINDER: [u8; 10] = [114, 101, 115, 032, 098, 105, 110, 100, 101, 114];
// pub const LABEL_EXT_BINDER: [u8; 10] = [101, 120, 116, 032, 098, 105, 110, 100, 101, 114];
pub const LABEL_EXP_MASTER: [u8; 10] = [101, 120, 112, 032, 109, 097, 115, 116, 101, 114];
pub const LABEL_RES_MASTER: [u8; 10] = [114, 101, 115, 032, 109, 097, 115, 116, 101, 114];
pub const LABEL_C_E_TRAFFIC: [u8; 11] = [099, 032, 101, 032, 116, 114, 097, 102, 102, 105, 099];
pub const LABEL_E_EXP_MASTER: [u8; 12] =
    [101, 032, 101, 120, 112, 032, 109, 097, 115, 116, 101, 114];
pub const LABEL_C_HS_TRAFFIC: [u8; 12] =
    [099, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099];
pub const LABEL_S_HS_TRAFFIC: [u8; 12] =
    [115, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099];
pub const LABEL_C_AP_TRAFFIC: [u8; 12] =
    [099, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099];
pub const LABEL_S_AP_TRAFFIC: [u8; 12] =
    [115, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099];

pub const PREFIX_SERVER_SIGNATURE: [u8; 98] = [
    0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
    0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
    0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
    0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
    0x54, 0x4c, 0x53, 0x20, 0x31, 0x2e, 0x33, 0x2c, 0x20, 0x73, 0x65, 0x72, 0x76, 0x65, 0x72, 0x20,
    0x43, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x56, 0x65, 0x72, 0x69, 0x66,
    0x79, 0x00,
];

/// Build the server name out of the `name` bytes for the client hello.
fn build_server_name(name: &Bytes) -> Result<Bytes, TLSError> {
    const PREFIX1: &[U8; 2] = &[U8(0), U8(0)];
    const PREFIX2: &[U8; 1] = &[U8(0)];
    Ok(encode_length_u16(encode_length_u16(
        encode_length_u16(name.clone())?.prefix(PREFIX2),
    )?)?
    .prefix(PREFIX1))
}

/// Check the server name for the sni extension.
///
/// Returns the value for the server name indicator when successful, and a `[TLSError`]
/// otherwise.
fn check_server_name(extension: &[U8]) -> Result<Bytes, TLSError> {
    check_length_encoding_u16_slice(extension)?;
    check_eq_with_slice(&[U8(0)], extension, 2, 3)?;
    check_length_encoding_u16_slice(&extension[3..extension.len()])?;
    Ok(extension[5..extension.len()].into())
}

/// Build the supported versions bytes for the client hello.
fn supported_versions() -> Result<Bytes, TLSError> {
    Ok(Bytes::from([0, 0x2b]).concat(encode_length_u16(encode_length_u8(&[U8(3), U8(4)])?)?))
}

/// Check the TLS version in the provided `client_hello`.
fn check_supported_versions(client_hello: &[U8]) -> Result<(), TLSError> {
    check_length_encoding_u8_slice(client_hello)?;
    check_mem(&[U8(3), U8(4)], &client_hello[1..client_hello.len()])
}

fn server_supported_version(_algorithms: &Algorithms) -> Result<Bytes, TLSError> {
    const SUPPORTED_VERSION_PREFIX: &[U8; 2] = &[U8(0), U8(0x2b)];
    Ok(encode_length_u16(bytes2(3, 4))?.prefix(SUPPORTED_VERSION_PREFIX))
}

fn check_server_supported_version(_algs: &Algorithms, b: &[U8]) -> Result<(), TLSError> {
    check_eq_slice(&[U8(3), U8(4)], b)
}

fn supported_groups(algs: &Algorithms) -> Result<Bytes, TLSError> {
    const SUPPORTED_GROUPS_PREFIX: &[U8; 2] = &[U8(0), U8(0x0a)];
    Ok(
        encode_length_u16(encode_length_u16(algs.supported_group()?)?)?
            .prefix(SUPPORTED_GROUPS_PREFIX),
    )
}

fn check_supported_groups(algs: &Algorithms, ch: &[U8]) -> Result<(), TLSError> {
    check_length_encoding_u16_slice(ch)?;
    check_mem(algs.supported_group()?.as_raw(), &ch[2..ch.len()])
}

fn signature_algorithms(algs: &Algorithms) -> Result<Bytes, TLSError> {
    Ok(bytes2(0, 0x0d).concat(encode_length_u16(encode_length_u16(
        algs.signature_algorithm()?,
    )?)?))
}

fn check_signature_algorithms(algs: &Algorithms, ch: &[U8]) -> Result<(), TLSError> {
    check_length_encoding_u16_slice(ch)?;
    check_mem(algs.signature_algorithm()?.as_raw(), &ch[2..ch.len()])
}

fn psk_key_exchange_modes() -> Result<Bytes, TLSError> {
    const PSK_MODE_PREFIX: &[U8; 2] = &[U8(0), U8(0x2d)];
    Ok(encode_length_u16(encode_length_u8(&[U8(1)])?)?.prefix(PSK_MODE_PREFIX))
}

fn check_psk_key_exchange_modes(client_hello: &[U8]) -> Result<(), TLSError> {
    check_length_encoding_u8_slice(client_hello)?;
    check_eq_with_slice(&[U8(1)], client_hello, 1, 2)
}

fn key_shares(algs: &Algorithms, gx: KemPk) -> Result<Bytes, TLSError> {
    let ks = algs.supported_group()?.concat(encode_length_u16(gx)?);
    const PREFIX: &[U8; 2] = &[U8(0), U8(0x33)];
    Ok(encode_length_u16(encode_length_u16(ks)?)?.prefix(PREFIX))
}

fn find_key_share(g: &Bytes, ch: &[U8]) -> Result<Bytes, TLSError> {
    if ch.len() < 4 {
        tlserr(parse_failed())
    } else if eq_slice(g.as_raw(), &ch[0..2]) {
        let len = length_u16_encoded_slice(&ch[2..ch.len()])?;
        Ok(ch[4..4 + len].into())
    } else {
        let len = length_u16_encoded_slice(&ch[2..ch.len()])?;
        find_key_share(g, &ch[4 + len..ch.len()])
    }
}

fn check_key_shares(algs: &Algorithms, ch: &[U8]) -> Result<Bytes, TLSError> {
    check_length_encoding_u16_slice(ch)?;
    find_key_share(&algs.supported_group()?, &ch[2..ch.len()])
}

fn server_key_shares(algs: &Algorithms, gx: KemPk) -> Result<Bytes, TLSError> {
    let ks = algs.supported_group()?.concat(encode_length_u16(gx)?);
    Ok(bytes2(0, 0x33).concat(encode_length_u16(ks)?))
}

fn check_server_key_share(algs: &Algorithms, b: &[U8]) -> Result<Bytes, TLSError> {
    check_eq_with_slice(algs.supported_group()?.as_raw(), b, 0, 2)?;
    check_length_encoding_u16_slice(&b[2..b.len()])?;
    // XXX Performance: These conversions aren't necessary. A slice would suffice.
    Ok(Bytes::from(&b[4..b.len()]))
}

fn pre_shared_key(algs: &Algorithms, session_ticket: &Bytes) -> Result<(Bytes, usize), TLSError> {
    let identities = encode_length_u16(
        encode_length_u16(session_ticket.clone())?.concat_array(u32_as_be_bytes(U32(0xffffffff))),
    )?;
    let binders = encode_length_u16(encode_length_u8(zero_key(&algs.hash()).as_raw())?)?;
    let binders_len = binders.len();
    let ext = bytes2(0, 41).concat(encode_length_u16(identities.concat(binders))?);
    let ext_len = ext.len();
    Ok((ext, ext_len + binders_len + 199 - 16 - 82)) // binders_len+199-76+41))
}

// Return ticket (tkt) and binder
fn check_psk_shared_key(algs: &Algorithms, ch: &[U8]) -> Result<(Bytes, Bytes), TLSError> {
    let len_id = length_u16_encoded(ch)?;
    let len_tkt = length_u16_encoded(&ch[2..2 + len_id])?;
    if len_id == len_tkt + 6 {
        check_length_encoding_u16_slice(&ch[2 + len_id..ch.len()])?;
        check_length_encoding_u8_slice(&ch[4 + len_id..ch.len()])?;
        if ch.len() - 5 - len_id != algs.hash().hash_len() {
            tlserr(parse_failed())
        } else {
            // let len_other_u16 = length_u16_encoded(&ch[2 + len_id..ch.len()])?;
            // let len_other_u8 = length_u8_encoded(&ch[4 + len_id..4+len_id+len_other_u16])?;
            Ok((Bytes::from(&ch[4..4 + len_tkt]), Bytes::from([0; 0])))
        }
    } else {
        tlserr(parse_failed())
    }
}

fn server_pre_shared_key(_algs: &Algorithms) -> Result<Bytes, TLSError> {
    Ok(bytes2(0, 41).concat(encode_length_u16(bytes2(0, 0))?))
}

fn check_server_psk_shared_key(_algs: &Algorithms, b: &[U8]) -> Result<(), TLSError> {
    check_eq_slice(&[U8(0), U8(0)], b)
}

/// TLS Extensions
pub struct Extensions {
    sni: Option<Bytes>,
    key_share: Option<Bytes>,
    ticket: Option<Bytes>,
    binder: Option<Bytes>,
}

impl Extensions {
    /// Merge the two extensions.
    /// This will fail if both have set the same extension.
    fn merge(self, e2: Self) -> Result<Self, TLSError> {
        Ok(Extensions {
            sni: merge_opts(self.sni, e2.sni)?,
            key_share: merge_opts(self.key_share, e2.key_share)?,
            ticket: merge_opts(self.ticket, e2.ticket)?,
            binder: merge_opts(self.binder, e2.binder)?,
        })
    }
}

/// Merge two options as xor and return `Some(value)`, `None`, or an error if
/// both are `Some`.
fn merge_opts<T>(o1: Option<T>, o2: Option<T>) -> Result<Option<T>, TLSError> {
    match (o1, o2) {
        (None, Some(o)) => Ok(Some(o)),
        (Some(o), None) => Ok(Some(o)),
        (None, None) => Ok(None),
        _ => tlserr(parse_failed()),
    }
}

/// Check an extension for validity.
fn check_extension(algs: &Algorithms, bytes: &[U8]) -> Result<(usize, Extensions), TLSError> {
    if bytes.len() < 4 {
        Err(parse_failed())
    } else {
        let l0 = bytes[0].declassify() as usize;
        let l1 = bytes[1].declassify() as usize;
        let len = length_u16_encoded_slice(&bytes[2..bytes.len()])?;
        let out = Extensions {
            sni: None,
            key_share: None,
            ticket: None,
            binder: None,
        };

        match (l0 as u8, l1 as u8) {
            (0, 0) => Ok((
                4 + len,
                Extensions {
                    sni: Some(check_server_name(&bytes[4..4 + len])?),
                    key_share: None,
                    ticket: None,
                    binder: None,
                },
            )),
            (0, 0x2d) => {
                check_psk_key_exchange_modes(&bytes[4..4 + len])?;
                Ok((4 + len, out))
            }
            (0, 0x2b) => {
                check_supported_versions(&bytes[4..4 + len])?;
                Ok((4 + len, out))
            }
            (0, 0x0a) => {
                check_supported_groups(algs, &bytes[4..4 + len])?;
                Ok((4 + len, out))
            }
            (0, 0x0d) => {
                check_signature_algorithms(algs, &bytes[4..4 + len])?;
                Ok((4 + len, out))
            }
            (0, 0x33) => match check_key_shares(algs, &bytes[4..4 + len]) {
                Ok(gx) => Ok((
                    4 + len,
                    Extensions {
                        sni: None,
                        key_share: Some(gx),
                        ticket: None,
                        binder: None,
                    },
                )),
                Err(_) => tlserr(MISSING_KEY_SHARE),
            },
            (0, 0x29) => {
                // 41
                let (tkt, binder) = check_psk_shared_key(algs, &bytes[4..4 + len])?;
                Ok((
                    4 + len,
                    Extensions {
                        sni: None,
                        key_share: None,
                        ticket: Some(tkt),
                        binder: Some(binder),
                    },
                ))
            }
            _ => Ok((4 + len, out)),
        }
    }
}

fn check_server_extension(algs: &Algorithms, b: &[U8]) -> Result<(usize, Option<Bytes>), TLSError> {
    if b.len() < 4 {
        Err(parse_failed())
    } else {
        let l0 = b[0].declassify() as usize;
        let l1 = b[1].declassify() as usize;
        let len = length_u16_encoded(&b[2..b.len()])?;
        let mut out = None;
        match (l0 as u8, l1 as u8) {
            (0, 0x2b) => check_server_supported_version(algs, &b[4..4 + len])?,
            (0, 0x33) => {
                let gx = check_server_key_share(algs, &b[4..4 + len])?;
                out = Some(gx)
            }
            (0, 41) => check_server_psk_shared_key(algs, &b[4..4 + len])?,
            _ => (),
        }
        Ok((4 + len, out))
    }
}

#[inline(always)]
fn check_extensions_slice(algs: &Algorithms, b: &[U8]) -> Result<Extensions, TLSError> {
    let (len, out) = check_extension(algs, b)?;
    if len == b.len() {
        Ok(out)
    } else {
        let out_rest = check_extensions_slice(algs, &b[len..b.len()])?;
        out.merge(out_rest)
    }
}

fn check_extensions(algs: &Algorithms, b: &Bytes) -> Result<Extensions, TLSError> {
    let (len, out) = check_extension(algs, b.as_raw())?;
    if len == b.len() {
        Ok(out)
    } else {
        let out_rest = check_extensions_slice(algs, b.raw_slice(len..b.len()))?;
        out.merge(out_rest)
    }
}

fn check_server_extensions(algs: &Algorithms, b: &[U8]) -> Result<Option<Bytes>, TLSError> {
    let (len, out) = check_server_extension(algs, b)?;
    if len == b.len() {
        Ok(out)
    } else {
        let out_rest = check_server_extensions(algs, &b[len..b.len()])?;
        merge_opts(out, out_rest)
    }
}

// ```TLS
// struct {
//     AlertLevel level;
//     AlertDescription description;
// } Alert;
// ```

/// ```TLS
/// enum {
///     warning(1),
///     fatal(2),
///     (255)
/// } AlertLevel;
/// ```
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(u8)]
pub enum AlertLevel {
    Warning = 1,
    Fatal = 2,
}

impl TryFrom<u8> for AlertLevel {
    type Error = TLSError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            1 => Ok(AlertLevel::Warning),
            2 => Ok(AlertLevel::Fatal),
            _ => tlserr(parse_failed()),
        }
    }
}

/// ```TLS
/// enum {
///     close_notify(0),
///     unexpected_message(10),
///     bad_record_mac(20),
///     record_overflow(22),
///     handshake_failure(40),
///     bad_certificate(42),
///     unsupported_certificate(43),
///     certificate_revoked(44),
///     certificate_expired(45),
///     certificate_unknown(46),
///     illegal_parameter(47),
///     unknown_ca(48),
///     access_denied(49),
///     decode_error(50),
///     decrypt_error(51),
///     protocol_version(70),
///     insufficient_security(71),
///     internal_error(80),
///     inappropriate_fallback(86),
///     user_canceled(90),
///     missing_extension(109),
///     unsupported_extension(110),
///     unrecognized_name(112),
///     bad_certificate_status_response(113),
///     unknown_psk_identity(115),
///     certificate_required(116),
///     no_application_protocol(120),
///     (255)
/// } AlertDescription;
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(u8)]
pub enum AlertDescription {
    CloseNotify = 0,
    UnexpectedMessage = 10,
    BadRecordMac = 20,
    RecordOverflow = 22,
    HandshakeFailure = 40,
    BadCertificate = 42,
    UnsupportedCertificate = 43,
    CertificateRevoked = 44,
    CertificateExpired = 45,
    CertificateUnknown = 46,
    IllegalParameter = 47,
    UnknownCa = 48,
    AccessDenied = 49,
    DecodeError = 50,
    DecryptError = 51,
    ProtocolVersion = 70,
    InsufficientSecurity = 71,
    InternalError = 80,
    InappropriateFallback = 86,
    UserCanceled = 90,
    MissingExtension = 109,
    UnsupportedExtension = 110,
    UnrecognizedName = 112,
    BadCertificateStatusResponse = 113,
    UnknownPskIdentity = 115,
    CertificateRequired = 116,
    NoApplicationProtocol = 120,
}

impl AlertDescription {}

impl TryFrom<u8> for AlertDescription {
    type Error = TLSError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(AlertDescription::CloseNotify),
            10 => Ok(AlertDescription::UnexpectedMessage),
            20 => Ok(AlertDescription::BadRecordMac),
            22 => Ok(AlertDescription::RecordOverflow),
            40 => Ok(AlertDescription::HandshakeFailure),
            42 => Ok(AlertDescription::BadCertificate),
            43 => Ok(AlertDescription::UnsupportedCertificate),
            44 => Ok(AlertDescription::CertificateRevoked),
            45 => Ok(AlertDescription::CertificateExpired),
            46 => Ok(AlertDescription::CertificateUnknown),
            47 => Ok(AlertDescription::IllegalParameter),
            48 => Ok(AlertDescription::UnknownCa),
            49 => Ok(AlertDescription::AccessDenied),
            50 => Ok(AlertDescription::DecodeError),
            51 => Ok(AlertDescription::DecryptError),
            70 => Ok(AlertDescription::ProtocolVersion),
            71 => Ok(AlertDescription::InsufficientSecurity),
            80 => Ok(AlertDescription::InternalError),
            86 => Ok(AlertDescription::InappropriateFallback),
            90 => Ok(AlertDescription::UserCanceled),
            109 => Ok(AlertDescription::MissingExtension),
            110 => Ok(AlertDescription::UnsupportedExtension),
            112 => Ok(AlertDescription::UnrecognizedName),
            113 => Ok(AlertDescription::BadCertificateStatusResponse),
            115 => Ok(AlertDescription::UnknownPskIdentity),
            116 => Ok(AlertDescription::CertificateRequired),
            120 => Ok(AlertDescription::NoApplicationProtocol),
            _ => tlserr(parse_failed()),
        }
    }
}

#[cfg(bench)]
pub fn bench_client_hello(
    algorithms: &Algorithms,
    client_random: Random,
    kem_pk: &KemPk,
    server_name: &Bytes,
    session_ticket: &Option<Bytes>,
) -> Result<(HandshakeData, usize), TLSError> {
    client_hello(
        algorithms,
        client_random,
        kem_pk,
        server_name,
        session_ticket,
    )
}

fn get_psk_extensions(
    algorithms: &Algorithms,
    session_ticket: &Bytes,
    mut extensions: Bytes,
) -> Result<(usize, Bytes), TLSError> {
    let pskm = psk_key_exchange_modes()?;
    let (psk, len) = pre_shared_key(algorithms, session_ticket)?;
    extensions = extensions.concat(pskm).concat(psk);
    Ok((len, extensions))
}

/// Build a ClientHello message.
#[cfg_attr(feature = "hax-pv", proverif::before(
"fun extern__client_hello_c(
      $:{Bytes}, (* client_randomness *)
      $:{Bytes}, (* session_id *)
      $:{Bytes}, (*server name /sni*)
      $:{Bytes}, (*kem_pk / gx*)
      Option, (*tkto*)
      Option, (*bindero*)
      nat) (*trunc_len*)
      : $:{HandshakeData} [data]."))]
#[cfg_attr(feature = "hax-pv", proverif::replace_body(
    "(extern__client_hello_c(
         client_random,
         $:{Bytes}_default(),
         server_name,
         kem_pk,
         session_ticket,
         None(),
         0),
     0)"
))]
pub(crate) fn client_hello(
    algorithms: &Algorithms,
    client_random: Random,
    kem_pk: &KemPk,
    server_name: &Bytes,
    session_ticket: &Option<Bytes>,
) -> Result<(HandshakeData, usize), TLSError> {
    let version = bytes2(3, 3);
    let compression_methods = bytes2(1, 0);
    // const version: &[U8; 2] = &[U8(3), U8(3)];
    // const compression_methods: &[U8; 2] = &[U8(1), U8(0)];
    let legacy_session_id = encode_length_u8(&[U8(0); 32])?;
    let cipher_suites = encode_length_u16(algorithms.ciphersuite()?)?;
    let server_name = build_server_name(server_name)?;
    let supported_versions = supported_versions()?;
    let supported_groups = supported_groups(algorithms)?;
    let signature_algorithms = signature_algorithms(algorithms)?;
    let key_shares = key_shares(algorithms, kem_pk.clone())?;

    let extensions = bytes_concat!(
        server_name,
        supported_versions,
        supported_groups,
        signature_algorithms,
        key_shares
    );
    let (trunc_len, extensions) = (match (algorithms.psk_mode(), session_ticket) {
        (true, Some(session_ticket)) => get_psk_extensions(algorithms, session_ticket, extensions),
        (false, None) => Ok((0, extensions)),
        _ => tlserr(PSK_MODE_MISMATCH),
    })?;

    let encoded_extensions = encode_length_u16(extensions)?;
    let handshake_bytes = bytes_concat!(
        version,
        client_random,
        legacy_session_id,
        cipher_suites,
        compression_methods,
        encoded_extensions
    );
    let client_hello = HandshakeData::from_bytes(HandshakeType::ClientHello, &handshake_bytes)?;
    Ok((client_hello, trunc_len))
}


#[cfg_attr(feature = "hax-pv", proverif::replace_body("
       let extern__client_hello_c(client_randomness,
                                  session_id,
                                  server_name,
                                  kem_pk,
                                  tkto,
                                  old_binder,
                                  old_trunc_len)
        = client_hello in
          extern__client_hello_c(client_randomness,
                                  session_id,
                                  server_name,
                                  kem_pk,
                                  tkto,
                                  binder,
                                  0)"

    ))]
pub(crate) fn set_client_hello_binder(
    ciphersuite: &Algorithms,
    binder: &Option<Hmac>,
    client_hello: HandshakeData,
    trunc_len: Option<usize>,
) -> Result<HandshakeData, TLSError> {
    let HandshakeData(ch) = client_hello;
    let chlen = &ch.len();
    let hlen = ciphersuite.hash().hash_len();
    match (binder, trunc_len) {
        (Some(m), Some(trunc_len)) => {
            if chlen - hlen == trunc_len {
                Ok(HandshakeData(ch.update_slice(trunc_len, m, 0, hlen)))
            } else {
                tlserr(parse_failed())
            }
        }
        (None, None) => Ok(HandshakeData(ch)),
        (_, _) => tlserr(parse_failed()),
    }
}

fn invalid_compression_list() -> Result<(), TLSError> {
    Result::<(), TLSError>::Err(INVALID_COMPRESSION_LIST)
}

#[cfg(bench)]
pub fn bench_parse_client_hello(
    ciphersuite: &Algorithms,
    client_hello: &HandshakeData,
) -> Result<
    (
        Random,
        Bytes,
        Bytes,
        Bytes,
        Option<Bytes>,
        Option<Bytes>,
        usize,
    ),
    TLSError,
> {
    parse_client_hello(ciphersuite, client_hello)
}

/// Parse the provided `client_hello` with the given `ciphersuite`.
// XXX: Can `Option` not be hardwired like this?
#[allow(clippy::type_complexity)]
#[cfg_attr(feature = "hax-pv", proverif::replace("
fun ${parse_client_hello}(
  $:{Algorithms},
  $:{HandshakeData})
: bitstring
reduc forall
      algs:$:{Algorithms},
      client_random: $:{Bytes},
      server_name: $:{Bytes},
      kem_pk: $:{Bytes},
      session_ticket: Option,
      binder: Option;
    ${parse_client_hello}(
        algs,
        extern__client_hello_c(client_random,
                            $:{Bytes}_default_value,
                            server_name,
                            kem_pk,
                            session_ticket,
                            binder,
                            0))
           = (client_random,
                            $:{Bytes}_default_value,
                            server_name,
                            kem_pk,
                            session_ticket,
                            binder,
                            0)."
    ))]
pub(super) fn parse_client_hello(
    ciphersuite: &Algorithms,
    client_hello: &HandshakeData,
) -> Result<
    (
        Random,
        Bytes,
        Bytes,
        Bytes,
        Option<Bytes>,
        Option<Bytes>,
        usize,
    ),
    TLSError,
> {
    let HandshakeData(ch) = client_hello.as_handshake_message(HandshakeType::ClientHello)?;
    let ver = bytes2(3, 3);
    let comp = bytes2(1, 0);
    let mut next = 0;
    check_eq_with_slice(ver.as_raw(), ch.as_raw(), next, next + 2)?;
    next += 2;
    check(ch.len() >= next + 32)?;
    let crand = ch.slice_range(next..next + 32);
    next += 32;
    let sidlen = length_u8_encoded(&ch[next..ch.len()])?;
    let sid = ch.slice_range(next + 1..next + 1 + sidlen);
    next = next + 1 + sidlen;
    let cslen = ciphersuite.check(ch.raw_slice(next..ch.len()))?;
    next += cslen;
    match check_eq_with_slice(comp.as_raw(), ch.as_raw(), next, next + 2) {
        Ok(_) => Ok(()),
        Err(_) => invalid_compression_list(),
    }?;
    next += 2;
    check_length_encoding_u16(&ch.slice_range(next..ch.len()))?;
    next += 2;
    let exts = check_extensions(ciphersuite, &ch.slice_range(next..ch.len()))?;
    let trunc_len = ch.len() - ciphersuite.hash().hash_len() - 3; // ??
    match (ciphersuite.psk_mode(), exts) {
        (
            _,
            Extensions {
                sni: _,
                key_share: None,
                ticket: _,
                binder: _,
            },
        ) => Err(MISSING_KEY_SHARE),
        (
            true,
            Extensions {
                sni: Some(sn),
                key_share: Some(gx),
                ticket: Some(tkt),
                binder: Some(binder),
            },
        ) => Ok((crand, sid, sn, gx, Some(tkt), Some(binder), trunc_len)),
        (
            true,
            Extensions {
                sni: None,
                key_share: Some(gx),
                ticket: Some(tkt),
                binder: Some(binder),
            },
        ) => Ok((
            crand,
            sid,
            Bytes::new(),
            gx,
            Some(tkt),
            Some(binder),
            trunc_len,
        )),
        (
            false,
            Extensions {
                sni: Some(sn),
                key_share: Some(gx),
                ticket: None,
                binder: None,
            },
        ) => Ok((crand, sid, sn, gx, None, None, 0)),
        (
            false,
            Extensions {
                sni: None,
                key_share: Some(gx),
                ticket: None,
                binder: None,
            },
        ) => Ok((crand, sid, Bytes::new(), gx, None, None, 0)),
        _ => Err(parse_failed()),
    }
}

/// Build the server hello message.
#[cfg_attr(feature = "hax-pv", pv_constructor)]
pub(crate) fn server_hello(
    algs: &Algorithms,
    sr: Random,
    sid: &Bytes,
    gy: &KemPk,
) -> Result<HandshakeData, TLSError> {
    let ver = bytes2(3, 3);
    let sid = encode_length_u8(sid.as_raw())?;
    let cip = algs.ciphersuite()?;
    let comp = bytes1(0);
    let ks = server_key_shares(algs, gy.clone())?;
    let sv = server_supported_version(algs)?;
    let mut exts = ks.concat(sv);
    if algs.psk_mode() {
        exts = exts.concat(server_pre_shared_key(algs)?);
    }
    let encoded_extensions = encode_length_u16(exts)?;
    let sh = HandshakeData::from_bytes(
        HandshakeType::ServerHello,
        &bytes_concat!(ver, sr, sid, cip, comp, encoded_extensions),
    )?;
    Ok(sh)
}

fn unsupported_cipher_alert() -> Result<(), TLSError> {
    Err(UNSUPPORTED_ALGORITHM)
}

fn invalid_compression_method_alert() -> Result<(), TLSError> {
    Err(DECODE_ERROR)
}

#[cfg(bench)]
pub fn bench_parse_server_hello(
    algs: &Algorithms,
    server_hello: &HandshakeData,
) -> Result<(Random, KemPk), TLSError> {
    parse_server_hello(algs, server_hello)
}

#[cfg_attr(feature = "hax-pv", proverif::replace(
    "reduc forall
   algs: $:{Algorithms},
   server_random: $:{Bytes},
   sid: $:{Bytes},
   gy: $:{Bytes};

   ${parse_server_hello}(
     algs,
     ${server_hello}(algs, server_random, sid, gy)
) = (server_random, gy)."
    ))]
pub(crate) fn parse_server_hello(
    algs: &Algorithms,
    server_hello: &HandshakeData,
) -> Result<(Random, KemPk), TLSError> {
    let HandshakeData(server_hello) =
        server_hello.as_handshake_message(HandshakeType::ServerHello)?;
    let ver = bytes2(3, 3);
    let cip = algs.ciphersuite()?;
    let comp = bytes1(0);
    let mut next = 0;
    (match check_eq_with_slice(ver.as_raw(), server_hello.as_raw(), next, next + 2) {
        Ok(_) => Ok(()),
        Err(_) => protocol_version_alert(),
    })?;
    next += 2;
    check(server_hello.len() >= next + 32)?;
    let srand = server_hello.slice_range(next..next + 32);
    next += 32;
    let sidlen = length_u8_encoded(&server_hello[next..server_hello.len()])?;
    next = next + 1 + sidlen;
    (match check_eq_with_slice(cip.as_raw(), server_hello.as_raw(), next, next + 2) {
        Ok(_) => Ok(()),
        Err(_) => unsupported_cipher_alert(),
    })?;
    next += 2;
    (match check_eq_with_slice(comp.as_raw(), server_hello.as_raw(), next, next + 1) {
        Ok(_) => Ok(()),
        Err(_) => invalid_compression_method_alert(),
    })?;
    next += 1;
    check_length_encoding_u16(&server_hello.slice_range(next..server_hello.len()))?;
    next += 2;
    let gy = check_server_extensions(algs, &server_hello[next..server_hello.len()])?;
    if let Some(gy) = gy {
        Ok((srand, gy))
    } else {
        Err(MISSING_KEY_SHARE)
    }
}

#[cfg_attr(feature = "hax-pv", pv_constructor)]
pub(crate) fn encrypted_extensions(_algs: &Algorithms) -> Result<HandshakeData, TLSError> {
    let handshake_type = bytes1(HandshakeType::EncryptedExtensions as u8);
    Ok(HandshakeData(handshake_type.concat(encode_length_u24(
        &encode_length_u16(Bytes::new())?,
    )?)))
}

#[cfg_attr(feature = "hax-pv", proverif::replace("
reduc forall algs: $:{Algorithms};

      ${parse_encrypted_extensions}(
        algs,
        ${encrypted_extensions}(algs)
      ) = ()."
    ))]
pub(crate) fn parse_encrypted_extensions(
    _algs: &Algorithms,
    encrypted_extensions: &HandshakeData,
) -> Result<(), TLSError> {
    let HandshakeData(encrypted_extension_bytes) = encrypted_extensions;
    let expected_handshake_type = bytes1(HandshakeType::EncryptedExtensions as u8);
    check_eq_with_slice(
        expected_handshake_type.as_raw(),
        encrypted_extension_bytes.as_raw(),
        0,
        1,
    )?;
    check_length_encoding_u24(
        encrypted_extension_bytes.raw_slice(1..encrypted_extension_bytes.len()),
    )
}
#[cfg_attr(feature = "hax-pv", pv_constructor)]
pub(crate) fn server_certificate(
    _algs: &Algorithms,
    cert: &Bytes,
) -> Result<HandshakeData, TLSError> {
    let creq = encode_length_u8(&[])?;
    let crt = encode_length_u24(cert)?;
    let ext = encode_length_u16(Bytes::new())?;
    let crts = encode_length_u24(&crt.concat(ext))?;
    HandshakeData::from_bytes(HandshakeType::Certificate, &creq.concat(crts))
}

#[cfg(bench)]
pub fn bench_parse_server_certificate(certificate: &HandshakeData) -> Result<Bytes, TLSError> {
    parse_server_certificate(certificate)
}

#[cfg_attr(feature = "hax-pv", proverif::replace("
reduc forall
algs: $:{Algorithms},
cert: $:{Bytes};

  ${parse_server_certificate}(
     ${server_certificate}(algs, cert)
  ) = cert."
    ))]
pub(crate) fn parse_server_certificate(certificate: &HandshakeData) -> Result<Bytes, TLSError> {
    let HandshakeData(sc) = certificate.as_handshake_message(HandshakeType::Certificate)?;
    let mut next = 0;
    let creqlen = length_u8_encoded(&sc[0..sc.len()])?;
    next = next + 1 + creqlen;
    check_length_encoding_u24(sc.raw_slice(next..sc.len()))?;
    next += 3;
    let crtlen = length_u24_encoded(sc.raw_slice(next..sc.len()))?;
    next += 3;
    let crt = sc.slice_range(next..next + crtlen);
    next += crtlen;
    let _extlen = length_u16_encoded(&sc[next..sc.len()])?;
    Ok(crt)
}

fn ecdsa_signature(sv: &Bytes) -> Result<Bytes, TLSError> {
    if sv.len() != 64 {
        Err(parse_failed())
    } else {
        let b0 = bytes1(0x0);
        let b1 = bytes1(0x30);
        let b2 = bytes1(0x02);
        let mut r: Bytes = sv.slice(0, 32);
        let mut s: Bytes = sv.slice(32, 32);
        if r[0].declassify() >= 128 {
            r = b0.clone().concat(r);
        }
        if s[0].declassify() >= 128 {
            s = b0.concat(s);
        }
        Ok(b1.concat(encode_length_u8(
            b2.clone()
                .concat(encode_length_u8(r.as_raw())?)
                .concat(b2)
                .concat(encode_length_u8(s.as_raw())?)
                .as_raw(),
        )?))
    }
}

fn check_r_len(rlen: usize) -> Result<(), TLSError> {
    if rlen < 32 || rlen > 33 {
        Err(INVALID_SIGNATURE)
    } else {
        Ok(())
    }
}

fn parse_ecdsa_signature(sig: Bytes) -> Result<Bytes, TLSError> {
    if sig.len() < 4 {
        Err(parse_failed())
    } else {
        check_eq(&bytes1(0x30), &sig.slice_range(0..1))?;
        check_length_encoding_u8(&sig.slice_range(1..sig.len()))?;
        check_eq(&bytes1(0x02), &sig.slice_range(2..3))?;
        let rlen = length_u8_encoded(&sig[3..sig.len()])?;
        check_r_len(rlen)?;
        let r = sig.slice(4 + rlen - 32, 32);
        if sig.len() < 6 + rlen + 32 {
            Err(INVALID_SIGNATURE)
        } else {
            check_eq(&bytes1(0x02), &sig.slice_range(4 + rlen..5 + rlen))?;
            check_length_encoding_u8(&sig.slice_range(5 + rlen..sig.len()))?;
            let s = sig.slice(sig.len() - 32, 32);
            Ok(r.concat(s))
        }
    }
}
#[cfg_attr(feature = "hax-pv", pv_constructor)]
pub(crate) fn certificate_verify(algs: &Algorithms, cv: &Bytes) -> Result<HandshakeData, TLSError> {
    let sv = (match algs.signature {
        SignatureScheme::RsaPssRsaSha256 => Ok(cv.clone()),
        SignatureScheme::EcdsaSecp256r1Sha256 => {
            if cv.len() != 64 {
                Err(parse_failed())
            } else {
                ecdsa_signature(cv)
            }
        }
        SignatureScheme::ED25519 => Err(UNSUPPORTED_ALGORITHM),
    })?;

    let sig = algs.signature_algorithm()?.concat(encode_length_u16(sv)?);
    HandshakeData::from_bytes(HandshakeType::CertificateVerify, &sig)
}

#[cfg_attr(feature = "hax-pv", proverif::replace("
reduc forall
algs: $:{Algorithms},
cert: $:{Bytes};

      ${parse_certificate_verify}(
        algs,${certificate_verify}(algs, cert)
      ) = cert."
    ))]
pub(crate) fn parse_certificate_verify(
    algs: &Algorithms,
    certificate_verify: &HandshakeData,
) -> Result<Bytes, TLSError> {
    let HandshakeData(cv) =
        certificate_verify.as_handshake_message(HandshakeType::CertificateVerify)?;
    let sa = algs.signature();
    check_eq_with_slice(algs.signature_algorithm()?.as_raw(), cv.as_raw(), 0, 2)?;
    check_length_encoding_u16(&cv.slice_range(2..cv.len()))?;
    match sa {
        SignatureScheme::EcdsaSecp256r1Sha256 => parse_ecdsa_signature(cv.slice_range(4..cv.len())),
        SignatureScheme::RsaPssRsaSha256 => Ok(cv.slice_range(4..cv.len())),
        SignatureScheme::ED25519 => {
            if cv.len() - 4 == 64 {
                Ok(cv.slice_range(4..cv.len()))
            } else {
                Err(INVALID_SIGNATURE)
            }
        }
    }
}

#[cfg_attr(feature = "hax-pv", pv_constructor)]
pub(crate) fn finished(vd: &Bytes) -> Result<HandshakeData, TLSError> {
    HandshakeData::from_bytes(HandshakeType::Finished, vd)
}


#[cfg_attr(feature = "hax-pv", proverif::replace("
reduc forall
  vd: $:{Bytes};

   ${parse_finished}(
     ${finished}(vd)
) = vd.
    "))]
pub(crate) fn parse_finished(finished: &HandshakeData) -> Result<Bytes, TLSError> {
    let HandshakeData(fin) = finished.as_handshake_message(HandshakeType::Finished)?;
    Ok(fin)
}

// XXX: Unused -> remove?

// fn session_ticket(_algs: &Algorithms, tkt: &Bytes) -> Result<HandshakeData, TLSError> {
//     let lifetime = U32::from(172800).as_be_bytes();
//     let age = U32::from(9999).as_be_bytes();
//     let nonce = encode_length_u8(&bytes1(1))?;
//     let stkt = encode_length_u16(tkt)?;
//     let grease_ext = bytes2(0x5a, 0x5a).concat(&encode_length_u16(&Bytes::new())?);
//     let ext = encode_length_u16(&grease_ext)?;
//     handshake_message(
//         HandshakeType::NewSessionTicket,
//         &lifetime
//             .concat(&age)
//             .concat(&nonce)
//             .concat(&stkt)
//             .concat(&ext),
//     )
// }

// fn parse_session_ticket(_algs: &Algorithms, tkt: &HandshakeData) -> Result<(U32, Bytes), TLSError> {
//     let HandshakeData(tkt) = as_handshake_message(HandshakeType::NewSessionTicket, tkt)?;
//     let lifetime = U32::from_be_bytes(&tkt.slice_range(0..4))?;
//     let age = U32::from_be_bytes(&tkt.slice_range(4..8))?;
//     let nonce_len = length_u8_encoded(&tkt.slice_range(8..tkt.len()))?;
//     let stkt_len = length_u16_encoded(&tkt.slice_range(9 + nonce_len..tkt.len()))?;
//     let stkt = tkt.slice_range(11 + nonce_len..11 + nonce_len + stkt_len);
//     check_length_encoding_u16(&tkt.slice_range(11 + nonce_len + stkt_len..tkt.len()))?;
//     Ok((lifetime + age, stkt))
// }

/* Record Layer Serialization and Parsing */
/// ```TLS
/// enum {
///     invalid(0),
///     change_cipher_spec(20),
///     alert(21),
///     handshake(22),
///     application_data(23),
///     (255)
/// } ContentType;
/// ```
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(u8)]
pub enum ContentType {
    Invalid = 0,
    ChangeCipherSpec = 20,
    Alert = 21,
    Handshake = 22,
    ApplicationData = 23,
}

impl ContentType {
    /// Get the [`ContentType`] from the `u8` representation.
    pub fn try_from_u8(t: u8) -> Result<Self, TLSError> {
        match t {
            20 => Ok(ContentType::ChangeCipherSpec),
            21 => Ok(ContentType::Alert),
            22 => Ok(ContentType::Handshake),
            23 => Ok(ContentType::ApplicationData),
            _ => Err(parse_failed()),
        }
    }
}

pub(crate) fn handshake_record(p: HandshakeData) -> Result<Bytes, TLSError> {
    let ty = bytes1(ContentType::Handshake as u8);
    let ver = bytes2(3, 3);
    Ok(ty.concat(ver).concat(encode_length_u16(p.0)?))
}

fn protocol_version_alert() -> Result<(), TLSError> {
    Result::<(), TLSError>::Err(PROTOCOL_VERSION_ALERT)
}

fn application_data_instead_of_handshake() -> Result<(), TLSError> {
    Result::<(), TLSError>::Err(APPLICATION_DATA_INSTEAD_OF_HANDSHAKE)
}

pub(crate) fn check_handshake_record(p: &Bytes) -> Result<(HandshakeData, usize), TLSError> {
    if p.len() < 5 {
        Err(parse_failed())
    } else {
        let ty = bytes1(ContentType::Handshake as u8);
        let ver = bytes2(3, 3);
        match check_eq(&ty, &p.slice_range(0..1)) {
            Ok(_) => (),
            Err(_) => application_data_instead_of_handshake()?,
        };
        match check_eq(&ver, &p.slice_range(1..3)) {
            Ok(_) => (),
            Err(_) => protocol_version_alert()?,
        };
        let len = length_u16_encoded(&p[3..p.len()])?;
        Ok((HandshakeData(p.slice_range(5..5 + len)), 5 + len))
    }
}

pub(crate) fn get_handshake_record(p: &Bytes) -> Result<HandshakeData, TLSError> {
    let (hd, len) = check_handshake_record(p)?;
    if len == p.len() {
        Ok(hd)
    } else {
        Err(parse_failed())
    }
}

/// Incremental Transcript Construction
/// For simplicity, we store the full transcript, but an internal Digest state would suffice.
pub(crate) struct Transcript {
    hash_algorithm: HashAlgorithm,
    transcript: HandshakeData,
}

impl Transcript {
    pub(crate) fn new(hash_algorithm: HashAlgorithm) -> Self {
        Self {
            hash_algorithm,
            transcript: HandshakeData(Bytes::new()),
        }
    }

    /// Add the [`HandshakeData`] `msg` to this transcript.
    // XXX: ${Struct} does not work to get the name of the struct
    // constructor. Either the backend should output different
    // constructor names for record types (i.e. accessble via
    // $:{Struct}), or the interpolation should be changed.
    #[cfg_attr(feature = "hax-pv", proverif::replace_body(
        "let bertie__tls13formats__Transcript(  (* XXX: hand-insert *)
            hash_algorithm: $:{HashAlgorithm},
            old_handshake_data: $:{HandshakeData}
        ) = self in
    bertie__tls13formats__Transcript(  (* XXX: hand-insert *)
        hash_algorithm,
        ${HandshakeData}(
            ${handshake_data::to_bytes_inner}(
                ${HandshakeData::concat}(
                    ${self.transcript},
                    msg
                )
            )
        )
    )"
    ))]
    pub(crate) fn add(mut self, msg: &HandshakeData) -> Self {
        self.transcript = self.transcript.concat(msg);
        self
    }

    /// Get the hash of this transcript
    pub(crate) fn transcript_hash(&self) -> Result<Digest, TLSError> {
        let th = self.hash_algorithm.hash(&self.transcript.0)?;
        Ok(th)
    }

    /// Get the hash of this transcript without the client hello
    #[cfg_attr(feature = "hax-pv", pv_constructor)]
    pub(crate) fn transcript_hash_without_client_hello(
        &self,
        client_hello: &HandshakeData,
        trunc_len: usize,
    ) -> Result<Digest, TLSError> {
        // let Transcript(ha, HandshakeData(tx)) = tx;
        let HandshakeData(ch) = client_hello;
        self.hash_algorithm.hash(
            &self
                .transcript
                .0
                .clone()
                .concat(client_hello.0.slice_range(0..trunc_len)),
        )
    }
}
