// A module that for the formatting code needed by TLS 1.3
// Import hacspec and all needed definitions.
#[cfg(feature = "evercrypt")]
use evercrypt_cryptolib::*;
#[cfg(not(feature = "evercrypt"))]
use hacspec_cryptolib::*;
use hacspec_lib::*;

use crate::*;

pub const PARSE_FAILED: u8 = 133;
pub const UNSUPPORTED_ALGORITHM: u8 = 6u8;

/// Well Known Constants

// Hack...
// pub const LABEL_IV: Bytes2 = Bytes2(secret_bytes!([105, 118]));
// pub const LABEL_KEY: Bytes3 = Bytes3(secret_bytes!([107, 101, 121]));
// pub const LABEL_TLS13: Bytes6 = Bytes6(secret_bytes!([116, 108, 115, 049, 051, 032]));
// pub const LABEL_DERIVED: Bytes7 = Bytes7(secret_bytes!([100, 101, 114, 105, 118, 101, 100]));
// pub const LABEL_FINISHED: Bytes8 = Bytes8(secret_bytes!([102, 105, 110, 105, 115, 104, 101, 100]));
// pub const LABEL_RES_BINDER: Bytes10 = Bytes10(secret_bytes!([
//     114, 101, 115, 032, 098, 105, 110, 100, 101, 114
// ]));
// pub const LABEL_EXT_BINDER: Bytes10 = Bytes10(secret_bytes!([
//     101, 120, 116, 032, 098, 105, 110, 100, 101, 114
// ]));
// pub const LABEL_EXP_MASTER: Bytes10 = Bytes10(secret_bytes!([
//     101, 120, 112, 032, 109, 097, 115, 116, 101, 114
// ]));
// pub const LABEL_RES_MASTER: Bytes10 = Bytes10(secret_bytes!([
//     114, 101, 115, 032, 109, 097, 115, 116, 101, 114
// ]));
// pub const LABEL_C_E_TRAFFIC: Bytes11 = Bytes11(secret_bytes!([
//     099, 032, 101, 032, 116, 114, 097, 102, 102, 105, 099
// ]));
// pub const LABEL_E_EXP_MASTER: Bytes12 = Bytes12(secret_bytes!([
//     101, 032, 101, 120, 112, 032, 109, 097, 115, 116, 101, 114
// ]));
// pub const LABEL_C_HS_TRAFFIC: Bytes12 = Bytes12(secret_bytes!([
//     099, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099
// ]));
// pub const LABEL_S_HS_TRAFFIC: Bytes12 = Bytes12(secret_bytes!([
//     115, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099
// ]));
// pub const LABEL_C_AP_TRAFFIC: Bytes12 = Bytes12(secret_bytes!([
//     099, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099
// ]));
// pub const LABEL_S_AP_TRAFFIC: Bytes12 = Bytes12(secret_bytes!([
//     115, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099
// ]));
//
// pub const PREFIX_SERVER_SIGNATURE: Bytes98 = Bytes98(secret_bytes!([
//     0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
//     0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
//     0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
//     0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
//     0x54, 0x4c, 0x53, 0x20, 0x31, 0x2e, 0x33, 0x2c, 0x20, 0x73, 0x65, 0x72, 0x76, 0x65, 0x72, 0x20,
//     0x43, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x56, 0x65, 0x72, 0x69, 0x66,
//     0x79, 0x00
// ]));

/*
const SHA256_EMPTY: Bytes32 = Bytes32(secret_bytes!([
    0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
    0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55
]));
*/

fn ciphersuite(algs: Algorithms) -> Result<Bytes, TLSError> {
    if hash_alg(algs) == HashAlgorithm::SHA256 {
        if aead_alg(algs) == AeadAlgorithm::Aes128Gcm {
            Ok(bytes2(0x13, 0x01))
        } else {
            if aead_alg(algs) == AeadAlgorithm::Chacha20Poly1305 {
                Ok(bytes2(0x13, 0x03))
            } else {
                Err(UNSUPPORTED_ALGORITHM)
            }
        }
    } else {
        Err(UNSUPPORTED_ALGORITHM)
    }
}

fn supported_group(algs: Algorithms) -> Result<Bytes, TLSError> {
    match kem_alg(algs) {
        NamedGroup::X25519 => Ok(bytes2(0x00, 0x1D)),
        NamedGroup::Secp256r1 => Ok(bytes2(0x00, 0x17)),
        NamedGroup::X448 => Err(UNSUPPORTED_ALGORITHM),
        NamedGroup::Secp384r1 => Err(UNSUPPORTED_ALGORITHM),
        NamedGroup::Secp521r1 => Err(UNSUPPORTED_ALGORITHM),
    }
}

fn signature_algorithm(algs: Algorithms) -> Result<Bytes, TLSError> {
    match sig_alg(algs) {
        SignatureScheme::RsaPssRsaSha256 => Ok(bytes2(0x08, 0x04)),
        SignatureScheme::EcdsaSecp256r1Sha256 => Ok(bytes2(0x04, 0x03)),
        SignatureScheme::ED25519 => Err(UNSUPPORTED_ALGORITHM),
    }
}

fn check_ciphersuites(algs: Algorithms, b: &ByteSeq) -> Result<usize, TLSError> {
    let len = check_lbytes2(b)?;
    let cs = ciphersuite(algs)?;
    let csl = b.slice_range(2..2 + len);
    check_mem(&cs, &csl)?;
    Ok(len + 2)
}

fn server_name(sn: &ByteSeq) -> Result<Bytes, TLSError> {
    let c = lbytes2(sn)?;
    let b = lbytes2(&bytes1(0).concat(&c))?;
    let a = lbytes2(&b)?;
    Ok(bytes2(0, 0).concat(&a))
}

fn check_server_name(ext: &ByteSeq) -> Result<Bytes, TLSError> {
    check_lbytes2_full(ext)?;
    check_eq(&bytes1(0), &ext.slice_range(2..3))?;
    check_lbytes2_full(&ext.slice_range(3..ext.len()))?;
    Ok(ext.slice_range(5..ext.len()))
}

fn supported_versions(_algs: Algorithms) -> Result<Bytes, TLSError> {
    let b = lbytes1(&bytes2(3, 4))?;
    let a = lbytes2(&b)?;
    Ok(bytes2(0, 0x2b).concat(&a))
}

fn check_supported_versions(_algs: Algorithms, ch: &ByteSeq) -> Result<(), TLSError> {
    check_lbytes1_full(ch)?;
    check_mem(&bytes2(3, 4), &ch.slice_range(1..ch.len()))
}

fn server_supported_version(_algs: Algorithms) -> Result<Bytes, TLSError> {
    let a = lbytes2(&bytes2(3, 4))?;
    Ok(bytes2(0, 0x2b).concat(&a))
}

fn check_server_supported_version(_algs: Algorithms, b: &ByteSeq) -> Result<(), TLSError> {
    check_eq(&bytes2(3, 4), b)
}

fn supported_groups(algs: Algorithms) -> Result<Bytes, TLSError> {
    let c = supported_group(algs)?;
    let b = lbytes2(&c)?;
    let a = lbytes2(&b)?;
    Ok(bytes2(0, 0x0a).concat(&a))
}

fn check_supported_groups(algs: Algorithms, ch: &ByteSeq) -> Result<(), TLSError> {
    check_lbytes2_full(ch)?;
    let a = supported_group(algs)?;
    check_mem(&a, &ch.slice_range(2..ch.len()))
}

fn signature_algorithms(algs: Algorithms) -> Result<Bytes, TLSError> {
    let c = signature_algorithm(algs)?;
    let b = lbytes2(&c)?;
    let a = lbytes2(&b)?;
    Ok(bytes2(0, 0x0d).concat(&a))
}

fn check_signature_algorithms(algs: Algorithms, ch: &ByteSeq) -> Result<(), TLSError> {
    check_lbytes2_full(ch)?;
    let a = signature_algorithm(algs)?;
    check_mem(&a, &ch.slice_range(2..ch.len()))
}

pub fn psk_key_exchange_modes(_algs: Algorithms) -> Result<Bytes, TLSError> {
    let b = lbytes1(&bytes1(1))?;
    let a = lbytes2(&b)?;
    Ok(bytes2(0, 0x2d).concat(&a))
}

pub fn check_psk_key_exchange_modes(_algs: Algorithms, ch: &ByteSeq) -> Result<(), TLSError> {
    check_lbytes1_full(ch)?;
    check_eq(&bytes1(1), &ch.slice_range(1..2))
}

pub fn key_shares(algs: Algorithms, gx: &KemPk) -> Result<Bytes, TLSError> {
    let b = supported_group(algs)?;
    let a = lbytes2(&gx)?;
    let ks = b.concat(&a);

    let b = lbytes2(&ks)?;
    let a = lbytes2(&b)?;
    Ok(bytes2(0, 0x33).concat(&a))
}

pub fn check_key_share(algs: Algorithms, ch: &ByteSeq) -> Result<Bytes, TLSError> {
    check_lbytes2_full(ch)?;

    let a = supported_group(algs)?;
    check_eq(&a, &ch.slice_range(2..4))?;
    check_lbytes2_full(&ch.slice_range(4..ch.len()))?;
    Ok(ch.slice_range(6..ch.len()))
}

pub fn server_key_shares(algs: Algorithms, gx: &KemPk) -> Result<Bytes, TLSError> {
    let b = supported_group(algs)?;
    let a = lbytes2(&gx)?;
    let ks = b.concat(&a);

    let a = lbytes2(&ks)?;
    Ok(bytes2(0, 0x33).concat(&a))
}

pub fn check_server_key_share(algs: Algorithms, b: &ByteSeq) -> Result<Bytes, TLSError> {
    let a = supported_group(algs)?;
    check_eq(&a, &b.slice_range(0..2))?;
    check_lbytes2_full(&b.slice_range(2..b.len()))?;
    Ok(b.slice_range(4..b.len()))
}

pub fn pre_shared_key(algs: Algorithms, tkt: &ByteSeq) -> Result<(Bytes, usize), TLSError> {
    let a = lbytes2(tkt)?;
    let identities = lbytes2(&a.concat(&U32_to_be_bytes(U32(0xffffffff))))?;

    let a = lbytes1(&zero_key(&hash_alg(algs)))?;
    let binders = lbytes2(&a)?;

    let a = lbytes2(&identities.concat(&binders))?;
    let ext = bytes2(0, 41).concat(&a);
    Ok((ext, binders.len()))
}

pub fn check_psk_shared_key(_algs: Algorithms, ch: &ByteSeq) -> Result<(), TLSError> {
    let len_id = check_lbytes2(ch)?;
    let len_tkt = check_lbytes2(&ch.slice_range(2..2 + len_id))?;
    if len_id == len_tkt + 6 {
        check_lbytes2_full(&ch.slice_range(2 + len_id..ch.len()))?;
        check_lbytes1_full(&ch.slice_range(4 + len_id..ch.len()))?;
        if ch.len() - 6 - len_id != 32 {
            Err(PARSE_FAILED)
        } else {
            Ok(())
        }
    } else {
        Err(PARSE_FAILED)
    }
}

pub fn server_pre_shared_key(_algs: Algorithms) -> Result<Bytes, TLSError> {
    let a = lbytes2(&bytes2(0, 0))?;
    Ok(bytes2(0, 41).concat(&a))
}

pub fn check_server_psk_shared_key(_algs: Algorithms, b: &ByteSeq) -> Result<(), TLSError> {
    check_eq(&bytes2(0, 0), b)
}

pub struct EXTS(
    pub Option<Bytes>, //SNI
    pub Option<Bytes>, //KeyShare
    pub Option<Bytes>, //Ticket
    pub Option<Bytes>, //Binder
);

pub fn merge_opts(o1: Option<Bytes>, o2: Option<Bytes>) -> Result<Option<Bytes>, TLSError> {
    match o1 {
        Option::Some(o1) => match o2 {
            Option::Some(o2) => Err(PARSE_FAILED),
            Option::None => Ok(Some(o1)),
        },
        Option::None => match o2 {
            Option::Some(o2) => Ok(Some(o2)),
            Option::None => Ok(Option::None),
        },
    }
}

pub fn merge_exts(e1: EXTS, e2: EXTS) -> Result<EXTS, TLSError> {
    let EXTS(sn1, ks1, tkt1, bd1) = e1;
    let EXTS(sn2, ks2, tkt2, bd2) = e2;

    let a = merge_opts(sn1, sn2)?;
    let b = merge_opts(ks1, ks2)?;
    let c = merge_opts(tkt1, tkt2)?;
    let d = merge_opts(bd1, bd2)?;
    Ok(EXTS(a, b, c, d))
}

fn check_extension(algs: Algorithms, b: &ByteSeq) -> Result<(usize, EXTS), TLSError> {
    let l0 = (b[0] as U8).declassify() as usize;
    let l1 = (b[1] as U8).declassify() as usize;
    let len = check_lbytes2(&b.slice_range(2..b.len()))?;
    let mut out = EXTS(Option::None, Option::None, Option::None, Option::None);

    // TODO: Support mechanical transformation of `else if` into `else { if }`?
    if (l0, l1) == (0, 0) {
        let sn = check_server_name(&b.slice_range(4..4 + len))?;
        out = EXTS(Some(sn), Option::None, Option::None, Option::None);
    } else {
        if (l0, l1) == (0, 0x2d) {
            check_psk_key_exchange_modes(algs, &b.slice_range(4..4 + len))?;
        } else {
            if (l0, l1) == (0, 0x2b) {
                check_supported_versions(algs, &b.slice_range(4..4 + len))?;
            } else {
                if (l0, l1) == (0, 0x0a) {
                    check_supported_groups(algs, &b.slice_range(4..4 + len))?;
                } else {
                    if (l0, l1) == (0, 0x0d) {
                        check_signature_algorithms(algs, &b.slice_range(4..4 + len))?;
                    } else {
                        if (l0, l1) == (0, 0x33) {
                            let gx = check_key_share(algs, &b.slice_range(4..4 + len))?;
                            out = EXTS(Option::None, Some(gx), Option::None, Option::None);
                        } else {
                            if (l0, l1) == (0, 41) {
                                // TODO: 41 or 0x41?
                                check_psk_shared_key(algs, &b.slice_range(4..4 + len))?;
                            }
                        }
                    }
                }
            }
        }
    }

    Ok((4 + len, out))
}

pub fn check_server_extension(
    algs: Algorithms,
    b: &ByteSeq,
) -> Result<(usize, Option<Bytes>), TLSError> {
    let l0 = (b[0] as U8).declassify() as usize;
    let l1 = (b[1] as U8).declassify() as usize;
    let len = check_lbytes2(&b.slice_range(2..b.len()))?;
    let mut out = Option::None;

    // TODO: Support mechanical transformation of `else if` into `else { if }`?
    if (l0, l1) == (0, 0x2b) {
        check_server_supported_version(algs, &b.slice_range(4..4 + len))?;
    } else {
        if (l0, l1) == (0, 0x33) {
            let gx = check_server_key_share(algs, &b.slice_range(4..4 + len))?;
            out = Some(gx);
        } else {
            if (l0, l1) == (0, 41) {
                // TODO: 41 or 0x41?
                check_server_psk_shared_key(algs, &b.slice_range(4..4 + len))?;
            }
        }
    }

    Ok((4 + len, out))
}

fn check_extensions(algs: Algorithms, b: &ByteSeq) -> Result<EXTS, TLSError> {
    let (len, out) = check_extension(algs, b)?;
    if len == b.len() {
        Ok(out)
    } else {
        let out_rest = check_extensions(algs, &b.slice_range(len..b.len()))?;
        merge_exts(out, out_rest)
    }
}

pub fn check_server_extensions(algs: Algorithms, b: &ByteSeq) -> Result<Option<Bytes>, TLSError> {
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
pub enum HandshakeType {
    ClientHello,
    ServerHello,
    NewSessionTicket,
    EndOfEarlyData,
    EncryptedExtensions,
    Certificate,
    CertificateRequest,
    CertificateVerify,
    Finished,
    KeyUpdate,
    MessageHash,
}

pub fn hs_type(t: HandshakeType) -> u8 {
    match t {
        HandshakeType::ClientHello => 1,
        HandshakeType::ServerHello => 2,
        HandshakeType::NewSessionTicket => 4,
        HandshakeType::EndOfEarlyData => 5,
        HandshakeType::EncryptedExtensions => 8,
        HandshakeType::Certificate => 11,
        HandshakeType::CertificateRequest => 13,
        HandshakeType::CertificateVerify => 15,
        HandshakeType::Finished => 20,
        HandshakeType::KeyUpdate => 24,
        HandshakeType::MessageHash => 254,
    }
}

pub fn get_hs_type(t: u8) -> Result<HandshakeType, TLSError> {
    // TODO: Support mechanical transformation of `else if` into `else { if }`?
    if t == 1 {
        Ok(HandshakeType::ClientHello)
    } else {
        if t == 2 {
            Ok(HandshakeType::ServerHello)
        } else {
            if t == 4 {
                Ok(HandshakeType::NewSessionTicket)
            } else {
                if t == 5 {
                    Ok(HandshakeType::EndOfEarlyData)
                } else {
                    if t == 8 {
                        Ok(HandshakeType::EncryptedExtensions)
                    } else {
                        if t == 11 {
                            Ok(HandshakeType::Certificate)
                        } else {
                            if t == 13 {
                                Ok(HandshakeType::CertificateRequest)
                            } else {
                                if t == 15 {
                                    Ok(HandshakeType::CertificateVerify)
                                } else {
                                    if t == 20 {
                                        Ok(HandshakeType::Finished)
                                    } else {
                                        if t == 24 {
                                            Ok(HandshakeType::KeyUpdate)
                                        } else {
                                            if t == 254 {
                                                Ok(HandshakeType::MessageHash)
                                            } else {
                                                Err(PARSE_FAILED)
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
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
    // TODO: Support mechanical transformation of `else if` into `else { if }`?
    if t == 1 {
        Ok(AlertLevel::Warning)
    } else {
        if t == 2 {
            Ok(AlertLevel::Fatal)
        } else {
            Err(PARSE_FAILED)
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
    // Here comes a beautiful waterfall <3
    // TODO: Support mechanical transformation of `else if` into `else { if }`?
    if t == 0 {
        Ok(AlertDescription::CloseNotify)
    } else {
        if t == 10 {
            Ok(AlertDescription::UnexpectedMessage)
        } else {
            if t == 20 {
                Ok(AlertDescription::BadRecordMac)
            } else {
                if t == 22 {
                    Ok(AlertDescription::RecordOverflow)
                } else {
                    if t == 40 {
                        Ok(AlertDescription::HandshakeFailure)
                    } else {
                        if t == 42 {
                            Ok(AlertDescription::BadCertificate)
                        } else {
                            if t == 43 {
                                Ok(AlertDescription::UnsupportedCertificate)
                            } else {
                                if t == 44 {
                                    Ok(AlertDescription::CertificateRevoked)
                                } else {
                                    if t == 45 {
                                        Ok(AlertDescription::CertificateExpired)
                                    } else {
                                        if t == 46 {
                                            Ok(AlertDescription::CertificateUnknown)
                                        } else {
                                            if t == 47 {
                                                Ok(AlertDescription::IllegalParameter)
                                            } else {
                                                if t == 48 {
                                                    Ok(AlertDescription::UnknownCa)
                                                } else {
                                                    if t == 49 {
                                                        Ok(AlertDescription::AccessDenied)
                                                    } else {
                                                        if t == 50 {
                                                            Ok(AlertDescription::DecodeError)
                                                        } else {
                                                            if t == 51 {
                                                                Ok(AlertDescription::DecryptError)
                                                            } else {
                                                                if t == 70 {
                                                                    Ok(AlertDescription::ProtocolVersion)
                                                                } else {
                                                                    if t == 71 {
                                                                        Ok(AlertDescription::InsufficientSecurity)
                                                                    } else {
                                                                        if t == 80 {
                                                                            Ok(AlertDescription::InternalError)
                                                                        } else {
                                                                            if t == 86 {
                                                                                Ok(AlertDescription::InappropriateFallback)
                                                                            } else {
                                                                                if t == 90 {
                                                                                    Ok(AlertDescription::UserCanceled)
                                                                                } else {
                                                                                    if t == 109 {
                                                                                        Ok(AlertDescription::MissingExtension)
                                                                                    } else {
                                                                                        if t == 110
                                                                                        {
                                                                                            Ok(AlertDescription::UnsupportedExtension)
                                                                                        } else {
                                                                                            if t == 112 {
                                                                                                Ok(AlertDescription::UnrecognizedName)
                                                                                            } else {
                                                                                                if t == 113 {
                                                                                                    Ok(AlertDescription::BadCertificateStatusResponse)
                                                                                                } else {
                                                                                                    if t == 115 {
                                                                                                        Ok(AlertDescription::UnknownPskIdentity)
                                                                                                    } else {
                                                                                                        if t == 116 {
                                                                                                            Ok(AlertDescription::CertificateRequired)
                                                                                                        } else {
                                                                                                            if t == 120 {
                                                                                                                Ok(AlertDescription::NoApplicationProtocol)
                                                                                                            } else {
                                                                                                                Err(PARSE_FAILED)
                                                                                                            }
                                                                                                        }
                                                                                                    }
                                                                                                }
                                                                                            }
                                                                                        }
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

// Tagged Handshake Data

pub fn handshake_message(ty: HandshakeType, by: &ByteSeq) -> Result<HandshakeData, TLSError> {
    let a = lbytes3(by)?;
    Ok(handshake_data(bytes1(hs_type(ty)).concat(&a)))
}

pub fn get_first_handshake_message(
    p: &HandshakeData,
) -> Result<(HandshakeData, HandshakeData), TLSError> {
    let p = handshake_data_bytes(p);
    if p.len() < 4 {
        Err(PARSE_FAILED)
    } else {
        let len = check_lbytes3(&p.slice_range(1..p.len()))?;
        let msg = p.slice_range(0..4 + len);
        let rest = p.slice_range(4 + len..p.len());
        Ok((HandshakeData(msg), HandshakeData(rest)))
    }
}

pub fn get_handshake_message(p: &HandshakeData) -> Result<HandshakeData, TLSError> {
    let (m1, p) = get_first_handshake_message(p)?;
    if handshake_data_len(&p) != 0 {
        Err(PARSE_FAILED)
    } else {
        Ok(m1)
    }
}

pub fn get_handshake_message_ty(
    ty: HandshakeType,
    p: &HandshakeData,
) -> Result<HandshakeData, TLSError> {
    let HandshakeData(m) = get_handshake_message(p)?;
    let tyb = bytes1(hs_type(ty));
    check_eq(&tyb, &m.slice_range(0..1))?;
    Ok(HandshakeData(m.slice_range(4..m.len())))
}

pub fn get_handshake_messages2(
    p: &HandshakeData,
) -> Result<(HandshakeData, HandshakeData), TLSError> {
    let (m1, p) = get_first_handshake_message(p)?;
    let (m2, p) = get_first_handshake_message(&p)?;
    if handshake_data_len(&p) != 0 {
        Err(PARSE_FAILED)
    } else {
        Ok((m1, m2))
    }
}
pub fn get_handshake_messages4(
    p: &HandshakeData,
) -> Result<(HandshakeData, HandshakeData, HandshakeData, HandshakeData), TLSError> {
    let (m1, p) = get_first_handshake_message(p)?;
    let (m2, p) = get_first_handshake_message(&p)?;
    let (m3, p) = get_first_handshake_message(&p)?;
    let (m4, p) = get_first_handshake_message(&p)?;
    if handshake_data_len(&p) != 0 {
        Err(PARSE_FAILED)
    } else {
        Ok((m1, m2, m3, m4))
    }
}

pub fn find_handshake_message(ty: HandshakeType, payload: &HandshakeData, start: usize) -> bool {
    let HandshakeData(p) = payload;
    if p.len() < start + 4 {
        false
    } else {
        match check_lbytes3(&p.slice_range(start + 1..p.len())) {
            Result::Ok(len) => {
                if eq1(p[start], U8(hs_type(ty))) {
                    true
                } else {
                    find_handshake_message(ty, payload, start + 4 + len)
                }
            }
            Result::Err(_) => false,
        }
    }
}

pub fn client_hello(
    algs: Algorithms,
    cr: &Random,
    gx: &KemPk,
    sn: &ByteSeq,
    tkt: &Option<Bytes>,
) -> Result<(HandshakeData, usize), TLSError> {
    let ver = bytes2(3, 3);
    let sid = lbytes1(&ByteSeq::new(32))?;

    let a = ciphersuite(algs)?;
    let cip = lbytes2(&a)?;
    let comp = bytes2(1, 0);
    let sn = server_name(sn)?;
    let sv = supported_versions(algs)?;
    let sg = supported_groups(algs)?;
    let sa = signature_algorithms(algs)?;
    let ks = key_shares(algs, gx)?;
    let mut exts = sn.concat(&sv).concat(&sg).concat(&sa).concat(&ks);
    let mut trunc_len = 0;

    if psk_mode(algs) {
        let tkt = tkt.as_ref().ok_or(PSK_MODE_MISMATCH)?;
        let pskm = psk_key_exchange_modes(algs)?;
        let (psk, len) = pre_shared_key(algs, tkt)?;
        exts = exts.concat(&pskm).concat(&psk);
        trunc_len = len;
    } else {
        if tkt.is_some() {
            Err(PSK_MODE_MISMATCH)?;
        }
    }

    let a = lbytes2(&exts)?;
    let ch = handshake_message(
        HandshakeType::ClientHello,
        &ver.concat(cr)
            .concat(&sid)
            .concat(&cip)
            .concat(&comp)
            .concat(&a),
    )?;
    Ok((ch, trunc_len))
}

pub fn set_client_hello_binder(
    algs: Algorithms,
    binder: &Option<HMAC>,
    ch: HandshakeData,
    trunc_len: Option<usize>,
) -> Result<HandshakeData, TLSError> {
    let HandshakeData(ch) = ch;
    let chlen = ch.len();
    let hlen = hash_len(&hash_alg(algs));

    match binder {
        Option::Some(binder) => match trunc_len {
            Option::Some(trunc_len) => {
                if chlen - hlen == trunc_len {
                    Ok(HandshakeData(ch.update_slice(trunc_len, binder, 0, hlen)))
                } else {
                    Err(PARSE_FAILED)
                }
            }
            Option::None => Err(PARSE_FAILED),
        },
        Option::None => match trunc_len {
            Option::Some(trunc_len) => Err(PARSE_FAILED),
            Option::None => Ok(HandshakeData(ch)),
        },
    }
}

pub fn parse_client_hello(
    algs: Algorithms,
    ch: &HandshakeData,
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
    let HandshakeData(ch) = get_handshake_message_ty(HandshakeType::ClientHello, ch)?;
    let ver = bytes2(3, 3);
    let comp = bytes2(1, 0);
    let mut next = 0;
    check_eq(&ver, &ch.slice_range(next..next + 2))?;
    next = next + 2;
    let crand = ch.slice_range(next..next + 32);
    next = next + 32;
    let sidlen = check_lbytes1(&ch.slice_range(next..ch.len()))?;
    let sid = ch.slice_range(next + 1..next + 1 + sidlen);
    next = next + 1 + sidlen;
    let cslen = check_ciphersuites(algs, &ch.slice_range(next..ch.len()))?;
    next = next + cslen;
    check_eq(&comp, &ch.slice_range(next..next + 2))?;
    next = next + 2;
    check_lbytes2_full(&ch.slice_range(next..ch.len()))?;
    next = next + 2;
    let exts = check_extensions(algs, &ch.slice_range(next..ch.len()))?;
    let trunc_len = ch.len() - hash_len(&hash_alg(algs)) - 3;

    let EXTS(sn, gx, tkt, binder) = exts;
    if psk_mode(algs) {
        match sn {
            Option::Some(sn) => match gx {
                Option::Some(gx) => match tkt {
                    Option::Some(tkt) => match binder {
                        Option::Some(binder) => Ok((
                            Random::from_seq(&crand),
                            sid,
                            sn,
                            gx,
                            Some(tkt),
                            Some(binder),
                            trunc_len,
                        )),
                        Option::None => Err(PARSE_FAILED),
                    },
                    Option::None => Err(PARSE_FAILED),
                },
                Option::None => Err(PARSE_FAILED),
            },
            Option::None => Err(PARSE_FAILED),
        }
    } else {
        match sn {
            Option::Some(sn) => match gx {
                Option::Some(gx) => match tkt {
                    Option::Some(tkt) => Err(PARSE_FAILED),
                    Option::None => match binder {
                        Option::Some(binder) => Err(PARSE_FAILED),
                        Option::None => Ok((
                            Random::from_seq(&crand),
                            sid,
                            sn,
                            gx,
                            Option::None,
                            Option::None,
                            0,
                        )),
                    },
                },
                Option::None => Err(PARSE_FAILED),
            },
            Option::None => Err(PARSE_FAILED),
        }
    }
}

pub fn server_hello(
    algs: Algorithms,
    sr: &Random,
    sid: &ByteSeq,
    gy: &KemPk,
) -> Result<HandshakeData, TLSError> {
    let ver = bytes2(3, 3);
    let sid = lbytes1(sid)?;
    let cip = ciphersuite(algs)?;
    let comp = bytes1(0);
    let ks = server_key_shares(algs, gy)?;
    let sv = server_supported_version(algs)?;
    let mut exts = ks.concat(&sv);
    if psk_mode(algs) {
        let a = server_pre_shared_key(algs)?;
        exts = exts.concat(&a);
    }
    let a = lbytes2(&exts)?;
    let sh = handshake_message(
        HandshakeType::ServerHello,
        &ver.concat(sr)
            .concat(&sid)
            .concat(&cip)
            .concat(&comp)
            .concat(&a),
    )?;
    Ok(sh)
}

pub fn parse_server_hello(
    algs: Algorithms,
    sh: &HandshakeData,
) -> Result<(Random, KemPk), TLSError> {
    let HandshakeData(sh) = get_handshake_message_ty(HandshakeType::ServerHello, sh)?;
    let ver = bytes2(3, 3);
    let cip = ciphersuite(algs)?;
    let comp = bytes1(0);
    let mut next = 0;
    check_eq(&ver, &sh.slice_range(next..next + 2))?;
    next = next + 2;
    let srand = sh.slice_range(next..next + 32);
    next = next + 32;
    let sidlen = check_lbytes1(&sh.slice_range(next..sh.len()))?;
    next = next + 1 + sidlen;
    check_eq(&cip, &sh.slice_range(next..next + 2))?;
    next = next + 2;
    check_eq(&comp, &sh.slice_range(next..next + 1))?;
    next = next + 1;
    check_lbytes2_full(&sh.slice_range(next..sh.len()))?;
    next = next + 2;
    let gy = check_server_extensions(algs, &sh.slice_range(next..sh.len()))?;

    match gy {
        Option::Some(gy) => Ok((Random::from_seq(&srand), gy)),
        Option::None => Err(UNSUPPORTED_ALGORITHM),
    }
}

pub fn encrypted_extensions(_algs: Algorithms) -> Result<HandshakeData, TLSError> {
    let ty = bytes1(hs_type(HandshakeType::EncryptedExtensions));

    let a = lbytes3(&empty())?;
    Ok(HandshakeData(ty.concat(&a)))
}

pub fn parse_encrypted_extensions(_algs: Algorithms, ee: &HandshakeData) -> Result<(), TLSError> {
    let HandshakeData(ee) = ee;
    let ty = bytes1(hs_type(HandshakeType::EncryptedExtensions));
    check_eq(&ty, &ee.slice_range(0..1))?;
    check_lbytes3_full(&ee.slice_range(1..ee.len()))
}

pub fn server_certificate(_algs: Algorithms, cert: &ByteSeq) -> Result<HandshakeData, TLSError> {
    let creq = lbytes1(&empty())?;
    let crt = lbytes3(cert)?;
    let ext = lbytes2(&empty())?;
    let crts = lbytes3(&crt.concat(&ext))?;
    handshake_message(HandshakeType::Certificate, &creq.concat(&crts))
}

pub fn parse_server_certificate(_algs: Algorithms, sc: &HandshakeData) -> Result<Bytes, TLSError> {
    let HandshakeData(sc) = get_handshake_message_ty(HandshakeType::Certificate, sc)?;
    let mut next = 0;
    let creqlen = check_lbytes1(&sc.slice_range(4..sc.len()))?;
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

fn ecdsa_signature(sv: &ByteSeq) -> Result<Bytes, TLSError> {
    if sv.len() != 64 {
        Err(PARSE_FAILED)
    } else {
        let b0 = bytes1(0x0);
        let b1 = bytes1(0x30);
        let b2 = bytes1(0x02);
        let mut r: Seq<U8> = sv.slice(0, 32);
        let mut s: Seq<U8> = sv.slice(32, 32);
        if (r[0] as U8).declassify() >= 128 {
            r = b0.concat(&r);
        }
        if (s[0] as U8).declassify() >= 128 {
            s = b0.concat(&s);
        }

        let c = lbytes1(&r)?;
        let b = lbytes1(&s)?;
        let a = lbytes1(&b2.concat(&c).concat(&b2).concat(&b))?;
        Ok(b1.concat(&a))
    }
}

fn parse_ecdsa_signature(sig: Bytes) -> Result<Bytes, TLSError> {
    if sig.len() < 4 {
        Err(PARSE_FAILED)
    } else {
        check_eq(&bytes1(0x30), &sig.slice_range(0..1))?;
        check_lbytes1_full(&sig.slice_range(1..sig.len()))?;
        check_eq(&bytes1(0x02), &sig.slice_range(2..3))?;
        let rlen = check_lbytes1(&sig.slice_range(3..sig.len()))?;
        let r = sig.slice(4 + rlen - 32, 32);
        if sig.len() < 6 + rlen + 32 {
            Err(PARSE_FAILED)
        } else {
            check_eq(&bytes1(0x02), &sig.slice_range(4 + rlen..5 + rlen))?;
            check_lbytes1_full(&sig.slice_range(5 + rlen..sig.len()))?;
            let s = sig.slice(sig.len() - 32, 32);
            Ok(r.concat(&s))
        }
    }
}
pub fn certificate_verify(algs: Algorithms, cv: &ByteSeq) -> Result<HandshakeData, TLSError> {
    if cv.len() != 64 {
        Err(PARSE_FAILED)
    } else {
        let sv = ecdsa_signature(cv)?;

        let b = signature_algorithm(algs)?;
        let a = lbytes2(&sv)?;
        let sig = b.concat(&a);

        let a = handshake_message(HandshakeType::CertificateVerify, &sig)?;
        Ok(a)
    }
}

pub fn parse_certificate_verify(algs: Algorithms, cv: &HandshakeData) -> Result<Bytes, TLSError> {
    let HandshakeData(cv) = get_handshake_message_ty(HandshakeType::CertificateVerify, cv)?;
    let sa = sig_alg(algs);

    let a = signature_algorithm(algs)?;
    check_eq(&a, &cv.slice_range(0..2))?;
    check_lbytes2_full(&cv.slice_range(2..cv.len()))?;
    match sa {
        SignatureScheme::EcdsaSecp256r1Sha256 => parse_ecdsa_signature(cv.slice_range(4..cv.len())),
        SignatureScheme::RsaPssRsaSha256 => Ok(cv.slice_range(4..cv.len())),
        SignatureScheme::ED25519 => {
            if cv.len() - 4 == 64 {
                Ok(cv.slice_range(8..cv.len()))
            } else {
                Err(PARSE_FAILED)
            }
        }
    }
}

pub fn finished(_algs: Algorithms, vd: &ByteSeq) -> Result<HandshakeData, TLSError> {
    handshake_message(HandshakeType::Finished, vd)
}

pub fn parse_finished(_algs: Algorithms, fin: &HandshakeData) -> Result<Bytes, TLSError> {
    let HandshakeData(fin) = get_handshake_message_ty(HandshakeType::Finished, fin)?;
    Ok(fin)
}

pub fn session_ticket(_algs: Algorithms, tkt: &ByteSeq) -> Result<HandshakeData, TLSError> {
    let lifetime = U32_to_be_bytes(U32(172800));
    let age = U32_to_be_bytes(U32(9999));
    let nonce = lbytes1(&bytes1(1))?;
    let stkt = lbytes2(tkt)?;

    let a = lbytes2(&empty())?;
    let grease_ext = bytes2(0x5a, 0x5a).concat(&a);
    let ext = lbytes2(&grease_ext)?;
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
    _algs: Algorithms,
    tkt: &HandshakeData,
) -> Result<(U32, Bytes), TLSError> {
    let HandshakeData(tkt) = get_handshake_message_ty(HandshakeType::NewSessionTicket, tkt)?;
    let lifetime = U32_from_be_bytes(U32Word::from_seq(&tkt.slice_range(0..4)));
    let age = U32_from_be_bytes(U32Word::from_seq(&tkt.slice_range(4..8)));
    let nonce_len = check_lbytes1(&tkt.slice_range(8..tkt.len()))?;
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

pub fn content_type(t: ContentType) -> u8 {
    match t {
        ContentType::Invalid => 0,
        ContentType::ChangeCipherSpec => 20,
        ContentType::Alert => 21,
        ContentType::Handshake => 22,
        ContentType::ApplicationData => 23,
    }
}

pub fn get_content_type(t: u8) -> Result<ContentType, TLSError> {
    // TODO: Support mechanical transformation of `else if` into `else { if }`?
    if t == 0 {
        Err(PARSE_FAILED)
    } else {
        if t == 20 {
            Ok(ContentType::ChangeCipherSpec)
        } else {
            if t == 21 {
                Ok(ContentType::Alert)
            } else {
                if t == 22 {
                    Ok(ContentType::Handshake)
                } else {
                    if t == 23 {
                        Ok(ContentType::ApplicationData)
                    } else {
                        Err(PARSE_FAILED)
                    }
                }
            }
        }
    }
}

pub fn handshake_record(p: &HandshakeData) -> Result<Bytes, TLSError> {
    let HandshakeData(p) = p;
    let ty = bytes1(content_type(ContentType::Handshake));
    let ver = bytes2(3, 3);

    let a = lbytes2(p)?;
    Ok(ty.concat(&ver).concat(&a))
}

pub fn check_handshake_record(p: &ByteSeq) -> Result<(HandshakeData, usize), TLSError> {
    if p.len() < 5 {
        Err(PARSE_FAILED)
    } else {
        let ty = bytes1(content_type(ContentType::Handshake));
        let ver = bytes2(3, 3);
        check_eq(&ty, &p.slice_range(0..1))?;
        check_eq(&ver, &p.slice_range(1..3))?;
        let len = check_lbytes2(&p.slice_range(3..p.len()))?;
        Ok((HandshakeData(p.slice_range(5..5 + len)), 5 + len))
    }
}

pub fn get_handshake_record(p: &ByteSeq) -> Result<HandshakeData, TLSError> {
    let (hd, len) = check_handshake_record(p)?;
    if len == p.len() {
        Ok(hd)
    } else {
        Err(PARSE_FAILED)
    }
}

/* Incremental Transcript Construction
For simplicity, we store the full transcript, but an internal Digest state would suffice. */

pub struct Transcript(HashAlgorithm, HandshakeData);

pub fn transcript_empty(ha: HashAlgorithm) -> Transcript {
    Transcript(ha, HandshakeData(empty()))
}

pub fn transcript_add1(tx: Transcript, msg: &HandshakeData) -> Transcript {
    let Transcript(ha, tx) = tx;
    Transcript(ha, handshake_concat(tx, msg))
}

pub fn get_transcript_hash(tx: &Transcript) -> Result<Digest, TLSError> {
    let Transcript(ha, HandshakeData(txby)) = tx;
    let th = hash(ha, txby)?;
    Ok(th)
}

pub fn get_transcript_hash_truncated_client_hello(
    tx: &Transcript,
    ch: &HandshakeData,
    trunc_len: usize,
) -> Result<Digest, TLSError> {
    let Transcript(ha, HandshakeData(tx)) = tx;
    let HandshakeData(ch) = ch;
    hash(ha, &tx.concat(&ch.slice_range(0..trunc_len)))
}
