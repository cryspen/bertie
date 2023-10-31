use crate::{check_eq, eq, parse_failed, Bytes, SignatureKey, TLSError, PSK, PSK_MODE_MISMATCH};

pub struct ServerDB(
    pub Bytes,
    pub Bytes,
    pub SignatureKey,
    pub Option<(Bytes, PSK)>,
);

pub fn lookup_db(
    algs: crate::Algorithms,
    db: &ServerDB,
    sni: &Bytes,
    tkt: &Option<Bytes>,
) -> Result<(Bytes, SignatureKey, Option<PSK>), TLSError> {
    let ServerDB(server_name, cert, sk, psk_opt) = db;
    if eq(&sni, &Bytes::new()) || eq(&sni, &server_name) {
        match (crate::psk_mode(&algs), tkt, psk_opt) {
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
