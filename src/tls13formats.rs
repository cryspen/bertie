//! A module that for the formatting code needed by TLS 1.3
#![allow(clippy::manual_range_contains)]

use crate::{
    tls13crypto::{
        zero_key, Algorithms, Digest, HashAlgorithm, Hmac, KemPk, Random, SignatureScheme,
    },
    tls13utils::{
        bytes1, bytes2, check_eq, check_lbyte, check_lbyte_full, check_lbytes2, check_lbytes2_full,
        check_lbytes3, check_lbytes3_full, check_mem, encode_lbyte, encode_lbytes2, encode_lbytes3,
        eq, eq1, parse_failed, tlserr, Bytes,
        HandshakeData, TLSError, APPLICATION_DATA_INSTEAD_OF_HANDSHAKE, DECODE_ERROR,
        INVALID_COMPRESSION_LIST, INVALID_SIGNATURE, MISSING_KEY_SHARE, PROTOCOL_VERSION_ALERT,
        PSK_MODE_MISMATCH, U32, U8, UNSUPPORTED_ALGORITHM,
    },
};

// Well Known Constants

pub const LABEL_IV: [u8; 2] = [105, 118];
pub const LABEL_KEY: [u8; 3] = [107, 101, 121];
pub const LABEL_TLS13: [u8; 6] = [116, 108, 115, 049, 051, 032];
pub const LABEL_DERIVED: [u8; 7] = [100, 101, 114, 105, 118, 101, 100];
pub const LABEL_FINISHED: [u8; 8] = [102, 105, 110, 105, 115, 104, 101, 100];
pub const LABEL_RES_BINDER: [u8; 10] = [114, 101, 115, 032, 098, 105, 110, 100, 101, 114];
pub const LABEL_EXT_BINDER: [u8; 10] = [101, 120, 116, 032, 098, 105, 110, 100, 101, 114];
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
    Ok(Bytes::from([0, 0]).concat(&encode_lbytes2(&encode_lbytes2(
        &Bytes::from([0]).concat(&encode_lbytes2(name)?),
    )?)?))
}

/// Check the server name for the sni extension.
///
/// Returns the value for the server name indicator when successful, and a `[TLSError`]
/// otherwise.
fn check_server_name(extension: &Bytes) -> Result<Bytes, TLSError> {
    check_lbytes2_full(extension)?;
    check_eq(&bytes1(0), &extension.slice_range(2..3))?;
    check_lbytes2_full(&extension.slice_range(3..extension.len()))?;
    Ok(extension.slice_range(5..extension.len()))
}

/// Build the supported versions bytes for the client hello.
fn supported_versions() -> Result<Bytes, TLSError> {
    Ok(Bytes::from([0, 0x2b]).concat(&encode_lbytes2(&encode_lbyte(&Bytes::from([3, 4]))?)?))
}

/// Check the TLS version in the provided `client_hello`.
fn check_supported_versions(client_hello: &Bytes) -> Result<(), TLSError> {
    check_lbyte_full(client_hello)?;
    check_mem(
        &[3, 4].into(),
        &client_hello.slice_range(1..client_hello.len()),
    )
}

fn server_supported_version(_algorithms: &Algorithms) -> Result<Bytes, TLSError> {
    Ok(bytes2(0, 0x2b).concat(&encode_lbytes2(&bytes2(3, 4))?))
}

fn check_server_supported_version(_algs: &Algorithms, b: &Bytes) -> Result<(), TLSError> {
    check_eq(&bytes2(3, 4), b)
}

fn supported_groups(algs: &Algorithms) -> Result<Bytes, TLSError> {
    Ok(bytes2(0, 0x0a).concat(&encode_lbytes2(&encode_lbytes2(&algs.supported_group()?)?)?))
}

fn check_supported_groups(algs: &Algorithms, ch: &Bytes) -> Result<(), TLSError> {
    check_lbytes2_full(ch)?;
    check_mem(&algs.supported_group()?, &ch.slice_range(2..ch.len()))
}

fn signature_algorithms(algs: &Algorithms) -> Result<Bytes, TLSError> {
    Ok(bytes2(0, 0x0d).concat(&encode_lbytes2(&encode_lbytes2(
        &algs.signature_algorithm()?,
    )?)?))
}

fn check_signature_algorithms(algs: &Algorithms, ch: &Bytes) -> Result<(), TLSError> {
    check_lbytes2_full(ch)?;
    check_mem(&algs.signature_algorithm()?, &ch.slice_range(2..ch.len()))
}

pub fn psk_key_exchange_modes() -> Result<Bytes, TLSError> {
    Ok(bytes2(0, 0x2d).concat(&encode_lbytes2(&encode_lbyte(&bytes1(1))?)?))
}

pub fn check_psk_key_exchange_modes(client_hello: &Bytes) -> Result<(), TLSError> {
    check_lbyte_full(client_hello)?;
    check_eq(&bytes1(1), &client_hello.slice_range(1..2))
}

pub fn key_shares(algs: &Algorithms, gx: &KemPk) -> Result<Bytes, TLSError> {
    let ks = algs.supported_group()?.concat(&encode_lbytes2(gx)?);
    Ok(bytes2(0, 0x33).concat(&encode_lbytes2(&encode_lbytes2(&ks)?)?))
}

pub fn find_key_share(g: &Bytes, ch: &Bytes) -> Result<Bytes, TLSError> {
    if ch.len() < 4 {
        tlserr(parse_failed())
    } else if eq(g, &ch.slice_range(0..2)) {
        let len = check_lbytes2(&ch.slice_range(2..ch.len()))?;
        Ok(ch.slice_range(4..4 + len))
    } else {
        let len = check_lbytes2(&ch.slice_range(2..ch.len()))?;
        find_key_share(g, &ch.slice_range(4 + len..ch.len()))
    }
}

pub fn check_key_shares(algs: &Algorithms, ch: &Bytes) -> Result<Bytes, TLSError> {
    check_lbytes2_full(ch)?;
    find_key_share(&algs.supported_group()?, &ch.slice_range(2..ch.len()))
}

pub fn server_key_shares(algs: &Algorithms, gx: &KemPk) -> Result<Bytes, TLSError> {
    let ks = algs.supported_group()?.concat(&encode_lbytes2(gx)?);
    Ok(bytes2(0, 0x33).concat(&encode_lbytes2(&ks)?))
}

pub fn check_server_key_share(algs: &Algorithms, b: &Bytes) -> Result<Bytes, TLSError> {
    check_eq(&algs.supported_group()?, &b.slice_range(0..2))?;
    check_lbytes2_full(&b.slice_range(2..b.len()))?;
    Ok(b.slice_range(4..b.len()))
}

pub fn pre_shared_key(
    algs: &Algorithms,
    session_ticket: &Bytes,
) -> Result<(Bytes, usize), TLSError> {
    let identities = encode_lbytes2(
        &encode_lbytes2(session_ticket)?.concat(&U32::from(0xffffffff).as_be_bytes()),
    )?;
    let binders = encode_lbytes2(&encode_lbyte(&zero_key(&algs.hash()))?)?;
    let ext = bytes2(0, 41).concat(&encode_lbytes2(&identities.concat(&binders))?);
    Ok((ext, binders.len()))
}

pub fn check_psk_shared_key(_algs: &Algorithms, ch: &Bytes) -> Result<(), TLSError> {
    let len_id = check_lbytes2(ch)?;
    let len_tkt = check_lbytes2(&ch.slice_range(2..2 + len_id))?;
    if len_id == len_tkt + 6 {
        check_lbytes2_full(&ch.slice_range(2 + len_id..ch.len()))?;
        check_lbyte_full(&ch.slice_range(4 + len_id..ch.len()))?;
        if ch.len() - 6 - len_id != 32 {
            tlserr(parse_failed())
        } else {
            Ok(())
        }
    } else {
        tlserr(parse_failed())
    }
}

pub fn server_pre_shared_key(_algs: &Algorithms) -> Result<Bytes, TLSError> {
    Ok(bytes2(0, 41).concat(&encode_lbytes2(&bytes2(0, 0))?))
}

pub fn check_server_psk_shared_key(_algs: &Algorithms, b: &Bytes) -> Result<(), TLSError> {
    check_eq(&bytes2(0, 0), b)
}

/// TLS Extensions
pub struct Extensions {
    pub sni: Option<Bytes>,
    pub key_share: Option<Bytes>,
    pub ticket: Option<Bytes>,
    pub binder: Option<Bytes>,
}

/// Merge two options as xor and return `Some(value)`, `None`, or an error if
/// both are `Some`.
pub fn merge_opts<T>(o1: Option<T>, o2: Option<T>) -> Result<Option<T>, TLSError> {
    match (o1, o2) {
        (None, Some(o)) => Ok(Some(o)),
        (Some(o), None) => Ok(Some(o)),
        (None, None) => Ok(None),
        _ => tlserr(parse_failed()),
    }
}

/// Merge the two extensions.
/// This will fail if both have set the same extension.
pub fn merge_extensions(e1: Extensions, e2: Extensions) -> Result<Extensions, TLSError> {
    Ok(Extensions {
        sni: merge_opts(e1.sni, e2.sni)?,
        key_share: merge_opts(e1.key_share, e2.key_share)?,
        ticket: merge_opts(e1.ticket, e2.ticket)?,
        binder: merge_opts(e1.binder, e2.binder)?,
    })
}

/// Check an extension for validity.
fn check_extension(algs: &Algorithms, bytes: &Bytes) -> Result<(usize, Extensions), TLSError> {
    let l0 = bytes[0].declassify() as usize;
    let l1 = bytes[1].declassify() as usize;
    let len = check_lbytes2(&bytes.slice_range(2..bytes.len()))?;
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
                sni: Some(check_server_name(&bytes.slice_range(4..4 + len))?),
                key_share: None,
                ticket: None,
                binder: None,
            },
        )),
        (0, 0x2d) => {
            check_psk_key_exchange_modes(&bytes.slice_range(4..4 + len))?;
            Ok((4 + len, out))
        }
        (0, 0x2b) => {
            check_supported_versions(&bytes.slice_range(4..4 + len))?;
            Ok((4 + len, out))
        }
        (0, 0x0a) => {
            check_supported_groups(algs, &bytes.slice_range(4..4 + len))?;
            Ok((4 + len, out))
        }
        (0, 0x0d) => {
            check_signature_algorithms(algs, &bytes.slice_range(4..4 + len))?;
            Ok((4 + len, out))
        }
        (0, 0x33) => match check_key_shares(algs, &bytes.slice_range(4..4 + len)) {
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
        (0, 41) => {
            check_psk_shared_key(algs, &bytes.slice_range(4..4 + len))?;
            Ok((4 + len, out))
        }
        _ => Ok((4 + len, out)),
    }
}

pub fn check_server_extension(
    algs: &Algorithms,
    b: &Bytes,
) -> Result<(usize, Option<Bytes>), TLSError> {
    let l0 = b[0].declassify() as usize;
    let l1 = b[1].declassify() as usize;
    let len = check_lbytes2(&b.slice_range(2..b.len()))?;
    let mut out = None;
    match (l0 as u8, l1 as u8) {
        (0, 0x2b) => check_server_supported_version(algs, &b.slice_range(4..4 + len))?,
        (0, 0x33) => {
            let gx = check_server_key_share(algs, &b.slice_range(4..4 + len))?;
            out = Some(gx)
        }
        (0, 41) => check_server_psk_shared_key(algs, &b.slice_range(4..4 + len))?,
        _ => (),
    }
    Ok((4 + len, out))
}

fn check_extensions(algs: &Algorithms, b: &Bytes) -> Result<Extensions, TLSError> {
    let (len, out) = check_extension(algs, b)?;
    //println!("checked 1 extension");
    if len == b.len() {
        Ok(out)
    } else {
        let out_rest = check_extensions(algs, &b.slice_range(len..b.len()))?;
        merge_extensions(out, out_rest)
    }
}

pub fn check_server_extensions(algs: &Algorithms, b: &Bytes) -> Result<Option<Bytes>, TLSError> {
    let (len, out) = check_server_extension(algs, b)?;
    if len == b.len() {
        Ok(out)
    } else {
        let out_rest = check_server_extensions(algs, &b.slice_range(len..b.len()))?;
        merge_opts(out, out_rest)
    }
}

/// ```TLS
/// enum {
///     client_hello(1),
///     server_hello(2),
///     new_session_ticket(4),
///     end_of_early_data(5),
///     encrypted_extensions(8),
///     certificate(11),
///     certificate_request(13),
///     certificate_verify(15),
///     finished(20),
///     key_update(24),
///     message_hash(254),
///     (255)
/// } HandshakeType;
/// ```
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(u8)]
pub enum HandshakeType {
    ClientHello = 1,
    ServerHello = 2,
    NewSessionTicket = 4,
    EndOfEarlyData = 5,
    EncryptedExtensions = 8,
    Certificate = 11,
    CertificateRequest = 13,
    CertificateVerify = 15,
    Finished = 20,
    KeyUpdate = 24,
    MessageHash = 254,
}

pub fn get_hs_type(t: u8) -> Result<HandshakeType, TLSError> {
    match t {
        1 => Ok(HandshakeType::ClientHello),
        2 => Ok(HandshakeType::ServerHello),
        4 => Ok(HandshakeType::NewSessionTicket),
        5 => Ok(HandshakeType::EndOfEarlyData),
        8 => Ok(HandshakeType::EncryptedExtensions),
        11 => Ok(HandshakeType::Certificate),
        13 => Ok(HandshakeType::CertificateRequest),
        15 => Ok(HandshakeType::CertificateVerify),
        20 => Ok(HandshakeType::Finished),
        24 => Ok(HandshakeType::KeyUpdate),
        254 => Ok(HandshakeType::MessageHash),
        _ => tlserr(parse_failed()),
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
pub enum AlertLevel {
    Warning,
    Fatal,
}

pub fn alert_level(t: AlertLevel) -> u8 {
    match t {
        AlertLevel::Warning => 1,
        AlertLevel::Fatal => 2,
    }
}

pub fn get_alert_level(t: u8) -> Result<AlertLevel, TLSError> {
    match t {
        1 => Ok(AlertLevel::Warning),
        2 => Ok(AlertLevel::Fatal),
        _ => tlserr(parse_failed()),
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
pub enum AlertDescription {
    CloseNotify,
    UnexpectedMessage,
    BadRecordMac,
    RecordOverflow,
    HandshakeFailure,
    BadCertificate,
    UnsupportedCertificate,
    CertificateRevoked,
    CertificateExpired,
    CertificateUnknown,
    IllegalParameter,
    UnknownCa,
    AccessDenied,
    DecodeError,
    DecryptError,
    ProtocolVersion,
    InsufficientSecurity,
    InternalError,
    InappropriateFallback,
    UserCanceled,
    MissingExtension,
    UnsupportedExtension,
    UnrecognizedName,
    BadCertificateStatusResponse,
    UnknownPskIdentity,
    CertificateRequired,
    NoApplicationProtocol,
}

pub fn alert_description(t: AlertDescription) -> u8 {
    match t {
        AlertDescription::CloseNotify => 0,
        AlertDescription::UnexpectedMessage => 10,
        AlertDescription::BadRecordMac => 20,
        AlertDescription::RecordOverflow => 22,
        AlertDescription::HandshakeFailure => 40,
        AlertDescription::BadCertificate => 42,
        AlertDescription::UnsupportedCertificate => 43,
        AlertDescription::CertificateRevoked => 44,
        AlertDescription::CertificateExpired => 45,
        AlertDescription::CertificateUnknown => 46,
        AlertDescription::IllegalParameter => 47,
        AlertDescription::UnknownCa => 48,
        AlertDescription::AccessDenied => 49,
        AlertDescription::DecodeError => 50,
        AlertDescription::DecryptError => 51,
        AlertDescription::ProtocolVersion => 70,
        AlertDescription::InsufficientSecurity => 71,
        AlertDescription::InternalError => 80,
        AlertDescription::InappropriateFallback => 86,
        AlertDescription::UserCanceled => 90,
        AlertDescription::MissingExtension => 109,
        AlertDescription::UnsupportedExtension => 110,
        AlertDescription::UnrecognizedName => 112,
        AlertDescription::BadCertificateStatusResponse => 113,
        AlertDescription::UnknownPskIdentity => 115,
        AlertDescription::CertificateRequired => 116,
        AlertDescription::NoApplicationProtocol => 120,
    }
}

pub fn get_alert_description(t: u8) -> Result<AlertDescription, TLSError> {
    match t {
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

// Tagged Handshake Data

pub fn handshake_message(
    handshake_type: HandshakeType,
    handshake_bytes: &Bytes,
) -> Result<HandshakeData, TLSError> {
    Ok(HandshakeData::from(
        bytes1(handshake_type as u8).concat(&encode_lbytes3(handshake_bytes)?),
    ))
}

/// Attempt to parse a handshake message from the beginning of the payload.
///
/// If successful, returns the parsed message and the unparsed rest of the
/// payload. Returns a [TLSError] if the payload is too short to contain a
/// handshake message or if the payload is shorter than the expected length
/// encoded in its first three bytes.
pub fn get_next_handshake_message(
    payload: &HandshakeData,
) -> Result<(HandshakeData, HandshakeData), TLSError> {
    if ({
        let p: &HandshakeData = &payload;
        p.len()
    }) < 4 {
        tlserr(parse_failed())
    } else {
        let len = check_lbytes3(&payload.0.slice_range(1..payload.0.len()))?;
        let message = payload.0.slice_range(0..4 + len);
        let rest = payload.0.slice_range(4 + len..payload.0.len());
        Ok((HandshakeData(message), HandshakeData(rest)))
    }
}

/// Attempt to parse exactly one handshake message from `payload`.
///
/// If successful, returns the parsed handshake message. Returns a [TLSError] if
/// no message can be parsed from the payload or if the payload is not fully
/// consumed by parsing one message.
pub fn get_handshake_message(payload: &HandshakeData) -> Result<HandshakeData, TLSError> {
    let (message, payload_rest) = get_next_handshake_message(payload)?;
    if ({
        let p = &payload_rest;
        p.len()
    }) != 0 {
        tlserr(parse_failed())
    } else {
        Ok(message)
    }
}

/// Attempt to parse exactly one handshake message of the `expected_type` from
/// `payload`.
///
/// If successful, returns the parsed handshake message. Returns a [TLSError] if
/// parsing is unsuccessful or the type of the parsed message disagrees with the
/// expected type.
pub fn get_handshake_message_ty(
    expected_type: HandshakeType,
    payload: &HandshakeData,
) -> Result<HandshakeData, TLSError> {
    let HandshakeData(tagged_message_bytes) = get_handshake_message(payload)?;
    let expected_bytes = bytes1(expected_type as u8);
    check_eq(&expected_bytes, &tagged_message_bytes.slice_range(0..1))?;
    Ok(HandshakeData(
        tagged_message_bytes.slice_range(4..tagged_message_bytes.len()),
    ))
}

/// Attempt to parse exactly two handshake messages from `payload`.
///
/// If successful, returns the parsed handshake messages. Returns a [TLSError]
/// if parsing of either message fails or if the payload is not fully consumed
/// by parsing two messages.
pub fn get_handshake_messages2(
    payload: &HandshakeData,
) -> Result<(HandshakeData, HandshakeData), TLSError> {
    let (message1, payload_rest) = get_next_handshake_message(payload)?;
    let (message2, payload_rest) = get_next_handshake_message(&payload_rest)?;
    if ({
        let p = &payload_rest;
        p.len()
    }) != 0 {
        tlserr(parse_failed())
    } else {
        Ok((message1, message2))
    }
}

/// Attempt to parse exactly four handshake messages from `payload`.
///
/// If successful, returns the parsed handshake messages. Returns a [TLSError]
/// if parsing of any message fails or if the payload is not fully consumed
/// by parsing four messages.
pub fn get_handshake_messages4(
    payload: &HandshakeData,
) -> Result<(HandshakeData, HandshakeData, HandshakeData, HandshakeData), TLSError> {
    let (message1, payload_rest) = get_next_handshake_message(payload)?;
    let (message2, payload_rest) = get_next_handshake_message(&payload_rest)?;
    let (message3, payload_rest) = get_next_handshake_message(&payload_rest)?;
    let (message4, payload_rest) = get_next_handshake_message(&payload_rest)?;
    if ({
        let p = &payload_rest;
        p.len()
    }) != 0 {
        tlserr(parse_failed())
    } else {
        Ok((message1, message2, message3, message4))
    }
}

/// Beginning at offset `start`, attempt to find a message of type `handshake_type` in `payload`.
///
/// Returns `true`` if `payload` contains a message of the given type, `false` otherwise.
pub fn find_handshake_message(
    handshake_type: HandshakeType,
    payload: &HandshakeData,
    start: usize,
) -> bool {
    if ({
        let p: &HandshakeData = &payload;
        p.len()
    }) < start + 4 {
        false
    } else {
        match check_lbytes3(&payload.0.slice_range(start + 1..payload.0.len())) {
            Err(_) => false,
            Ok(len) => {
                if eq1(payload.0[start], U8::from(handshake_type as u8)) {
                    true
                } else {
                    find_handshake_message(handshake_type, payload, start + 4 + len)
                }
            }
        }
    }
}

/// Build a ClientHello message.
pub(crate) fn client_hello(
    algorithms: &Algorithms,
    client_random: &Random,
    kem_pk: &KemPk,
    server_name: &Bytes,
    session_ticket: &Option<Bytes>,
) -> Result<(HandshakeData, usize), TLSError> {
    let version = bytes2(3, 3);
    let legacy_session_id = encode_lbyte(&Bytes::zeroes(32))?;
    let cipher_suites = encode_lbytes2(&algorithms.ciphersuite()?)?;
    let compression_methods = bytes2(1, 0);
    let server_name = build_server_name(server_name)?;
    let supported_versions = supported_versions()?;
    let supported_groups = supported_groups(algorithms)?;
    let signature_algorithms = signature_algorithms(algorithms)?;
    let key_shares = key_shares(algorithms, kem_pk)?;
    let mut extensions = server_name
        .concat(&supported_versions)
        .concat(&supported_groups)
        .concat(&signature_algorithms)
        .concat(&key_shares);
    let mut trunc_len = 0;
    match (algorithms.psk_mode(), session_ticket) {
        (true, Some(session_ticket)) => {
            let pskm = psk_key_exchange_modes()?;
            let (psk, len) = pre_shared_key(algorithms, session_ticket)?;
            extensions = extensions.concat(&pskm).concat(&psk);
            trunc_len = len;
        }
        (false, None) => {}
        _ => tlserr(PSK_MODE_MISMATCH)?,
    }

    let client_hello = handshake_message(
        HandshakeType::ClientHello,
        &version
            .concat(client_random)
            .concat(&legacy_session_id)
            .concat(&cipher_suites)
            .concat(&compression_methods)
            .concat(&encode_lbytes2(&extensions)?),
    )?;
    Ok((client_hello, trunc_len))
}

pub fn set_client_hello_binder(
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

/// Parse the provided `client_hello` with the given `ciphersuite`.
#[allow(clippy::type_complexity)]
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
    let HandshakeData(ch) = get_handshake_message_ty(HandshakeType::ClientHello, client_hello)?;
    let ver = bytes2(3, 3);
    let comp = bytes2(1, 0);
    let mut next = 0;
    check_eq(&ver, &ch.slice_range(next..next + 2))?;
    next = next + 2;
    let crand = ch.slice_range(next..next + 32);
    next = next + 32;
    let sidlen = check_lbyte(&ch.slice_range(next..ch.len()))?;
    let sid = ch.slice_range(next + 1..next + 1 + sidlen);
    next = next + 1 + sidlen;
    let cslen = ciphersuite.check(&ch.slice_range(next..ch.len()))?;
    next = next + cslen;
    match check_eq(&comp, &ch.slice_range(next..next + 2)) {
        Ok(_) => (),
        Err(_) => invalid_compression_list()?,
    };
    next = next + 2;
    check_lbytes2_full(&ch.slice_range(next..ch.len()))?;
    next = next + 2;
    let exts = check_extensions(ciphersuite, &ch.slice_range(next..ch.len()))?;
    //println!("check_extensions");
    let trunc_len = ch.len() - ciphersuite.hash().hash_len() - 3;
    match (ciphersuite.psk_mode(), exts) {
        (
            _,
            Extensions {
                sni: _,
                key_share: None,
                ticket: _,
                binder: _,
            },
        ) => tlserr(MISSING_KEY_SHARE),
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
        _ => tlserr(parse_failed()),
    }
}

/// Build the server hello message.
pub(crate) fn server_hello(
    algs: &Algorithms,
    sr: &Random,
    sid: &Bytes,
    gy: &KemPk,
) -> Result<HandshakeData, TLSError> {
    let ver = bytes2(3, 3);
    let sid = encode_lbyte(sid)?;
    let cip = algs.ciphersuite()?;
    let comp = bytes1(0);
    let ks = server_key_shares(algs, gy)?;
    let sv = server_supported_version(algs)?;
    let mut exts = ks.concat(&sv);
    match algs.psk_mode() {
        true => exts = exts.concat(&server_pre_shared_key(algs)?),
        false => {}
    }
    let sh = handshake_message(
        HandshakeType::ServerHello,
        &ver.concat(sr)
            .concat(&sid)
            .concat(&cip)
            .concat(&comp)
            .concat(&encode_lbytes2(&exts)?),
    )?;
    Ok(sh)
}

fn unsupported_cipher_alert() -> Result<(), TLSError> {
    tlserr(UNSUPPORTED_ALGORITHM)
}

fn invalid_compression_method_alert() -> Result<(), TLSError> {
    tlserr(DECODE_ERROR)
}

pub fn parse_server_hello(
    algs: &Algorithms,
    server_hello: &HandshakeData,
) -> Result<(Random, KemPk), TLSError> {
    let HandshakeData(server_hello) =
        get_handshake_message_ty(HandshakeType::ServerHello, server_hello)?;
    let ver = bytes2(3, 3);
    let cip = algs.ciphersuite()?;
    let comp = bytes1(0);
    let mut next = 0;
    match check_eq(&ver, &server_hello.slice_range(next..next + 2)) {
        Ok(_) => (),
        Err(_) => protocol_version_alert()?,
    };
    next = next + 2;
    let srand = server_hello.slice_range(next..next + 32);
    next = next + 32;
    let sidlen = check_lbyte(&server_hello.slice_range(next..server_hello.len()))?;
    next = next + 1 + sidlen;
    match check_eq(&cip, &server_hello.slice_range(next..next + 2)) {
        Ok(_) => (),
        Err(_) => unsupported_cipher_alert()?,
    };
    next = next + 2;
    match check_eq(&comp, &server_hello.slice_range(next..next + 1)) {
        Ok(_) => (),
        Err(_) => invalid_compression_method_alert()?,
    };
    next = next + 1;
    check_lbytes2_full(&server_hello.slice_range(next..server_hello.len()))?;
    next = next + 2;
    let gy = check_server_extensions(algs, &server_hello.slice_range(next..server_hello.len()))?;
    if let Some(gy) = gy {
        Ok((srand, gy))
    } else {
        Err(MISSING_KEY_SHARE)
    }
}

pub fn encrypted_extensions(_algs: &Algorithms) -> Result<HandshakeData, TLSError> {
    let handshake_type = bytes1(HandshakeType::EncryptedExtensions as u8);
    Ok(HandshakeData(
        handshake_type.concat(&encode_lbytes3(&encode_lbytes2(&Bytes::new())?)?),
    ))
}

pub fn parse_encrypted_extensions(
    _algs: &Algorithms,
    encrypted_extensions: &HandshakeData,
) -> Result<(), TLSError> {
    let HandshakeData(encrypted_extension_bytes) = encrypted_extensions;
    let expected_handshake_type = bytes1(HandshakeType::EncryptedExtensions as u8);
    check_eq(
        &expected_handshake_type,
        &encrypted_extension_bytes.slice_range(0..1),
    )?;
    check_lbytes3_full(&encrypted_extension_bytes.slice_range(1..encrypted_extension_bytes.len()))
}

pub fn server_certificate(_algs: &Algorithms, cert: &Bytes) -> Result<HandshakeData, TLSError> {
    let creq = encode_lbyte(&Bytes::new())?;
    let crt = encode_lbytes3(cert)?;
    let ext = encode_lbytes2(&Bytes::new())?;
    let crts = encode_lbytes3(&crt.concat(&ext))?;
    handshake_message(HandshakeType::Certificate, &creq.concat(&crts))
}

pub fn parse_server_certificate(_algs: &Algorithms, sc: &HandshakeData) -> Result<Bytes, TLSError> {
    let HandshakeData(sc) = get_handshake_message_ty(HandshakeType::Certificate, sc)?;
    let mut next = 0;
    let creqlen = check_lbyte(&sc.slice_range(4..sc.len()))?;
    next = next + 1 + creqlen;
    check_lbytes3_full(&sc.slice_range(next..sc.len()))?;
    next = next + 3;
    let crtlen = check_lbytes3(&sc.slice_range(next..sc.len()))?;
    next = next + 3;
    let crt = sc.slice_range(next..next + crtlen);
    next = next + crtlen;
    let _extlen = check_lbytes2(&sc.slice_range(next..sc.len()))?;
    Ok(crt)
}

fn ecdsa_signature(sv: &Bytes) -> Result<Bytes, TLSError> {
    if sv.len() != 64 {
        tlserr(parse_failed())
    } else {
        let b0 = bytes1(0x0);
        let b1 = bytes1(0x30);
        let b2 = bytes1(0x02);
        let mut r: Bytes = sv.slice(0, 32);
        let mut s: Bytes = sv.slice(32, 32);
        if (r[0] as U8).declassify() >= 128 {
            r = b0.concat(&r);
        }
        if (s[0] as U8).declassify() >= 128 {
            s = b0.concat(&s);
        }
        Ok(b1.concat(&encode_lbyte(
            &b2.concat(&encode_lbyte(&r)?)
                .concat(&b2)
                .concat(&encode_lbyte(&s)?),
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
        tlserr(parse_failed())
    } else {
        check_eq(&bytes1(0x30), &sig.slice_range(0..1))?;
        check_lbyte_full(&sig.slice_range(1..sig.len()))?;
        check_eq(&bytes1(0x02), &sig.slice_range(2..3))?;
        let rlen = check_lbyte(&sig.slice_range(3..sig.len()))?;
        check_r_len(rlen)?;
        let r = sig.slice(4 + rlen - 32, 32);
        if sig.len() < 6 + rlen + 32 {
            tlserr(INVALID_SIGNATURE)
        } else {
            check_eq(&bytes1(0x02), &sig.slice_range(4 + rlen..5 + rlen))?;
            check_lbyte_full(&sig.slice_range(5 + rlen..sig.len()))?;
            let s = sig.slice(sig.len() - 32, 32);
            Ok(r.concat(&s))
        }
    }
}
pub fn certificate_verify(algs: &Algorithms, cv: &Bytes) -> Result<HandshakeData, TLSError> {
    let sv = match algs.signature {
        SignatureScheme::RsaPssRsaSha256 => cv.clone(),
        SignatureScheme::EcdsaSecp256r1Sha256 => {
            if cv.len() != 64 {
                return tlserr(parse_failed());
            } else {
                ecdsa_signature(cv)?
            }
        }
        SignatureScheme::ED25519 => {
            unimplemented!()
        }
    };

    let sig = algs.signature_algorithm()?.concat(&encode_lbytes2(&sv)?);
    handshake_message(HandshakeType::CertificateVerify, &sig)
}

pub fn parse_certificate_verify(algs: &Algorithms, cv: &HandshakeData) -> Result<Bytes, TLSError> {
    let HandshakeData(cv) = get_handshake_message_ty(HandshakeType::CertificateVerify, cv)?;
    let sa = algs.signature();
    check_eq(&algs.signature_algorithm()?, &cv.slice_range(0..2))?;
    check_lbytes2_full(&cv.slice_range(2..cv.len()))?;
    match sa {
        SignatureScheme::EcdsaSecp256r1Sha256 => parse_ecdsa_signature(cv.slice_range(4..cv.len())),
        SignatureScheme::RsaPssRsaSha256 => Ok(cv.slice_range(4..cv.len())),
        SignatureScheme::ED25519 => {
            if cv.len() - 4 == 64 {
                Ok(cv.slice_range(8..cv.len()))
            } else {
                tlserr(INVALID_SIGNATURE)
            }
        }
    }
}

pub fn finished(_algs: &Algorithms, vd: &Bytes) -> Result<HandshakeData, TLSError> {
    handshake_message(HandshakeType::Finished, vd)
}

pub fn parse_finished(_algs: &Algorithms, fin: &HandshakeData) -> Result<Bytes, TLSError> {
    let HandshakeData(fin) = get_handshake_message_ty(HandshakeType::Finished, fin)?;
    Ok(fin)
}

pub fn session_ticket(_algs: &Algorithms, tkt: &Bytes) -> Result<HandshakeData, TLSError> {
    let lifetime = U32::from(172800).as_be_bytes();
    let age = U32::from(9999).as_be_bytes();
    let nonce = encode_lbyte(&bytes1(1))?;
    let stkt = encode_lbytes2(tkt)?;
    let grease_ext = bytes2(0x5a, 0x5a).concat(&encode_lbytes2(&Bytes::new())?);
    let ext = encode_lbytes2(&grease_ext)?;
    handshake_message(
        HandshakeType::NewSessionTicket,
        &lifetime
            .concat(&age)
            .concat(&nonce)
            .concat(&stkt)
            .concat(&ext),
    )
}

pub fn parse_session_ticket(
    _algs: &Algorithms,
    tkt: &HandshakeData,
) -> Result<(U32, Bytes), TLSError> {
    let HandshakeData(tkt) = get_handshake_message_ty(HandshakeType::NewSessionTicket, tkt)?;
    let lifetime = U32::from_be_bytes(&tkt.slice_range(0..4))?;
    let age = U32::from_be_bytes(&tkt.slice_range(4..8))?;
    let nonce_len = check_lbyte(&tkt.slice_range(8..tkt.len()))?;
    let stkt_len = check_lbytes2(&tkt.slice_range(9 + nonce_len..tkt.len()))?;
    let stkt = tkt.slice_range(11 + nonce_len..11 + nonce_len + stkt_len);
    check_lbytes2_full(&tkt.slice_range(11 + nonce_len + stkt_len..tkt.len()))?;
    Ok((lifetime + age, stkt))
}

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
pub enum ContentType {
    Invalid,
    ChangeCipherSpec,
    Alert,
    Handshake,
    ApplicationData,
}

impl ContentType {
    /// Get the `u8` representation of this [`ContentType`].
    pub(crate) fn as_u8(self) -> u8 {
        match self {
            ContentType::Invalid => 0,
            ContentType::ChangeCipherSpec => 20,
            ContentType::Alert => 21,
            ContentType::Handshake => 22,
            ContentType::ApplicationData => 23,
        }
    }

    /// Get the [`ContentType`] from the `u8` representation.
    pub fn try_from_u8(t: u8) -> Result<Self, TLSError> {
        match t {
            0 => tlserr(parse_failed()),
            20 => Ok(ContentType::ChangeCipherSpec),
            21 => Ok(ContentType::Alert),
            22 => Ok(ContentType::Handshake),
            23 => Ok(ContentType::ApplicationData),
            _ => tlserr(parse_failed()),
        }
    }
}

pub fn handshake_record(p: &HandshakeData) -> Result<Bytes, TLSError> {
    let HandshakeData(p) = p;
    let ty = bytes1(ContentType::Handshake.as_u8());
    let ver = bytes2(3, 3);
    Ok(ty.concat(&ver).concat(&encode_lbytes2(p)?))
}

fn protocol_version_alert() -> Result<(), TLSError> {
    Result::<(), TLSError>::Err(PROTOCOL_VERSION_ALERT)
}

fn application_data_instead_of_handshake() -> Result<(), TLSError> {
    Result::<(), TLSError>::Err(APPLICATION_DATA_INSTEAD_OF_HANDSHAKE)
}

pub fn check_handshake_record(p: &Bytes) -> Result<(HandshakeData, usize), TLSError> {
    if p.len() < 5 {
        tlserr(parse_failed())
    } else {
        let ty = bytes1(ContentType::Handshake.as_u8());
        let ver = bytes2(3, 3);
        match check_eq(&ty, &p.slice_range(0..1)) {
            Ok(_) => (),
            Err(_) => application_data_instead_of_handshake()?,
        };
        match check_eq(&ver, &p.slice_range(1..3)) {
            Ok(_) => (),
            Err(_) => protocol_version_alert()?,
        };
        let len = check_lbytes2(&p.slice_range(3..p.len()))?;
        Ok((HandshakeData(p.slice_range(5..5 + len)), 5 + len))
    }
}

pub fn get_handshake_record(p: &Bytes) -> Result<HandshakeData, TLSError> {
    let (hd, len) = check_handshake_record(p)?;
    if len == p.len() {
        Ok(hd)
    } else {
        tlserr(parse_failed())
    }
}

/* Incremental Transcript Construction
For simplicity, we store the full transcript, but an internal Digest state would suffice. */

pub struct Transcript(HashAlgorithm, HandshakeData);

pub fn transcript_empty(ha: HashAlgorithm) -> Transcript {
    Transcript(ha, HandshakeData(Bytes::new()))
}

pub fn transcript_add1(tx: Transcript, msg: &HandshakeData) -> Transcript {
    let Transcript(ha, tx) = tx;
    Transcript(ha, tx.concat(msg))
}

pub fn get_transcript_hash(tx: &Transcript) -> Result<Digest, TLSError> {
    let Transcript(ha, HandshakeData(txby)) = tx;
    let th = ha.hash(txby)?;
    Ok(th)
}

pub fn get_transcript_hash_truncated_client_hello(
    tx: &Transcript,
    ch: &HandshakeData,
    trunc_len: usize,
) -> Result<Digest, TLSError> {
    let Transcript(ha, HandshakeData(tx)) = tx;
    let HandshakeData(ch) = ch;
    ha.hash(&tx.concat(&ch.slice_range(0..trunc_len)))
}
