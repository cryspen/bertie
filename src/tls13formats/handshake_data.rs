use crate::tls13utils::{
    check_eq1, encode_length_u24, eq1, length_u24_encoded, parse_failed, tlserr, Bytes, TLSError,
    U8,
};
#[allow(unused_imports)]
use hax_lib::ToInt;
#[cfg(feature = "hax-pv")]
use hax_lib::{proverif, pv_constructor};

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
#[cfg_attr(feature = "hax-pv", hax_lib::opaque)]
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

/// Hadshake data of the TLS handshake.
pub struct HandshakeData(pub(crate) Bytes);

#[cfg_attr(
    feature = "hax-pv",
    proverif::replace(
        "reduc forall
                   hs1: $:{Bytes},
                   hs2: $:{Bytes};

            ${to_two_inner}(
                ${HandshakeData}(
                    ${crate::tls13utils::concat_inner}(hs1, hs2)
                )
            )
            = (hs1, hs2).
    "
    )
)]
fn to_two_inner(hs_data: &HandshakeData) -> Result<(HandshakeData, HandshakeData), TLSError> {
    let (message1, payload_rest) = hs_data.next_handshake_message()?;
    let (message2, payload_rest) = payload_rest.next_handshake_message()?;
    if payload_rest.len() != 0 {
        tlserr(parse_failed())
    } else {
        Ok((message1, message2))
    }
}
#[cfg_attr(
    feature = "hax-pv",
    proverif::replace(
        "reduc forall
                   hs1: $:{Bytes},
                   hs2: $:{Bytes},
                   hs3: $:{Bytes},
                   hs4: $:{Bytes};

            ${to_four_inner}(
                ${HandshakeData}(
                    ${crate::tls13utils::concat_inner}(
                        ${crate::tls13utils::concat_inner}(
                            ${crate::tls13utils::concat_inner}(
                                hs1,
                                hs2
                            ),
                            hs3
                        ),
                        hs4
                    )
                )
            )
            = (hs1,
               hs2,
               hs3,
               hs4)."
    )
)]
fn to_four_inner(
    hs_data: &HandshakeData,
) -> Result<(HandshakeData, HandshakeData, HandshakeData, HandshakeData), TLSError> {
    let (message1, payload_rest) = hs_data.next_handshake_message()?;
    let (message2, payload_rest) = payload_rest.next_handshake_message()?;
    let (message3, payload_rest) = payload_rest.next_handshake_message()?;
    let (message4, payload_rest) = payload_rest.next_handshake_message()?;

    if payload_rest.len() != 0 {
        tlserr(parse_failed())
    } else {
        Ok((message1, message2, message3, message4))
    }
}

#[cfg_attr(feature = "hax-pv", pv_constructor)]
#[hax_lib::ensures(|result| match result {
    Ok(hd) => hd.len() >= 4 && hd.len() - 4 == handshake_bytes.len(),
    _ => true })]
pub(crate) fn from_bytes_inner(
    handshake_type: HandshakeType,
    handshake_bytes: &Bytes,
) -> Result<HandshakeData, TLSError> {
    Ok(HandshakeData::from(
        encode_length_u24(handshake_bytes)?.prefix(&[U8(handshake_type as u8)]),
    ))
}

#[cfg_attr(feature = "hax-pv", pv_constructor)]
pub(crate) fn to_bytes_inner(hs: &HandshakeData) -> Bytes {
    hs.0.clone()
}

#[hax_lib::attributes]
impl HandshakeData {
    /// Generate a new [`HandshakeData`] from [`Bytes`] and the [`HandshakeType`].
    #[hax_lib::ensures(|result| match result {
        Ok(hd) => hd.len() >= 4 && hd.len() - 4 == handshake_bytes.len(),
        _ => true })]
    pub(crate) fn from_bytes(
        handshake_type: HandshakeType,
        handshake_bytes: &Bytes,
    ) -> Result<HandshakeData, TLSError> {
        from_bytes_inner(handshake_type, handshake_bytes)
    }

    /// Returns the length, in bytes.
    #[hax_lib::ensures(|result| fstar!("v result == Seq.length self._0._0"))]
    #[hax_lib::proverif::replace_body("(0)")]
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns the handshake data bytes.
    pub(crate) fn to_bytes(&self) -> Bytes {
        to_bytes_inner(self)
    }

    /// Returns a new [`HandshakeData`] that contains the bytes of
    /// `other` appended to the bytes of `self`.
    #[hax_lib::pv_constructor]
    pub(crate) fn concat(self, other: &HandshakeData) -> HandshakeData {
        let mut message1 = self.to_bytes();
        let message2 = other.to_bytes();

        message1.extend_from_slice(&message2);
        HandshakeData::from(message1)
    }

    /// Attempt to parse exactly one handshake message of the `expected_type` from
    /// `payload`.
    ///
    /// If successful, returns the parsed handshake message. Returns a [TLSError] if
    /// parsing is unsuccessful or the type of the parsed message disagrees with the
    /// expected type.
    #[hax_lib::ensures(|result| match result {
                                    Result::Ok(d) => self.len() >= 4 && self.len() - 4 == d.len(),
                                    _ => true })]
    pub(crate) fn as_handshake_message(
        &self,
        expected_type: HandshakeType,
    ) -> Result<HandshakeData, TLSError> {
        let (message, payload_rest) = self.next_handshake_message()?;
        if payload_rest.len() != 0 {
            tlserr(parse_failed())
        } else {
            let HandshakeData(tagged_message_bytes) = message;
            check_eq1(U8(expected_type as u8), tagged_message_bytes[0])?;
            Ok(HandshakeData(
                tagged_message_bytes.slice_range(4..tagged_message_bytes.len()),
            ))
        }
    }

    /// Attempt to parse a handshake message from the beginning of the payload.
    ///
    /// If successful, returns the parsed message and the unparsed rest of the
    /// payload. Returns a [TLSError] if the payload is too short to contain a
    /// handshake message or if the payload is shorter than the expected length
    /// encoded in its first three bytes.
    #[hax_lib::ensures(|result| match result {
                                    Result::Ok((m,r)) => m.len() >= 4 && self.len() >= m.len() && self.len() - m.len() == r.len(),
                                    _ => true })]
    pub(crate) fn next_handshake_message(&self) -> Result<(Self, Self), TLSError> {
        if (self.len()) < 4 {
            tlserr(parse_failed())
        } else {
            let len = length_u24_encoded(self.0.raw_slice(1..self.0.len()))?;
            let message = self.0.slice_range(0..4 + len);
            let rest = self.0.slice_range(4 + len..self.0.len());
            Ok((HandshakeData(message), HandshakeData(rest)))
        }
    }

    /// Attempt to parse exactly two handshake messages from `payload`.
    ///
    /// If successful, returns the parsed handshake messages. Returns a [TLSError]
    /// if parsing of either message fails or if the payload is not fully consumed
    /// by parsing two messages.
    pub(crate) fn to_two(&self) -> Result<(HandshakeData, HandshakeData), TLSError> {
        to_two_inner(self)
    }

    /// Attempt to parse exactly four handshake messages from `payload`.
    ///
    /// If successful, returns the parsed handshake messages. Returns a [TLSError]
    /// if parsing of any message fails or if the payload is not fully consumed
    /// by parsing four messages.
    pub(crate) fn to_four(
        &self,
    ) -> Result<(HandshakeData, HandshakeData, HandshakeData, HandshakeData), TLSError> {
        to_four_inner(self)
    }

    /// Beginning at offset `start`, attempt to find a message of type `handshake_type` in `payload`.
    ///
    /// Returns `true`` if `payload` contains a message of the given type, `false` otherwise.
    #[hax_lib::requires(self.len() >= start)]
    #[hax_lib::decreases(self.len().to_int() - start.to_int())]
    pub(crate) fn find_handshake_message(
        &self,
        handshake_type: HandshakeType,
        start: usize,
    ) -> bool {
        if self.len() - start < 4 {
            false
        } else {
            match length_u24_encoded(self.0.raw_slice(start + 1..self.0.len())) {
                Err(_) => false,
                Ok(len) => {
                    if eq1(self.0[start], U8(handshake_type as u8)) {
                        true
                    } else {
                        self.find_handshake_message(handshake_type, start + 4 + len)
                    }
                }
            }
        }
    }
}

#[hax_lib::attributes]
impl From<Bytes> for HandshakeData {
    #[ensures(|result| fstar!("result._0 = value"))]
    fn from(value: Bytes) -> Self {
        HandshakeData(value)
    }
}
