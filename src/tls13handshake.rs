use rand::{CryptoRng, RngCore};

use crate::{
    server::{lookup_db, ServerDB, ServerInfo},
    tls13cert::{cert_public_key, rsa_public_key, verification_key_from_cert},
    tls13crypto::{
        hkdf_expand, hkdf_extract, hmac_tag, hmac_verify, kem_decap, kem_encap, kem_keygen, sign,
        sign_rsa, verify, zero_key, AeadAlgorithm, AeadKey, AeadKeyIV, Algorithms, Digest,
        HashAlgorithm, KemSk, Key, MacKey, Psk, Random, SignatureScheme,
    },
    tls13formats::*,
    tls13record::*,
    tls13utils::*,
};

/* TLS 1.3 Key Schedule: See RFC 8446 Section 7 */

/// Get the hash of an empty byte slice.
fn hash_empty(algorithm: &HashAlgorithm) -> Result<Digest, TLSError> {
    algorithm.hash(&Bytes::new())
}

/// HKDF expand with a `label`.
fn hkdf_expand_label(
    ha: &HashAlgorithm,
    k: &Key,
    label: &Bytes,
    context: &Bytes,
    len: usize,
) -> Result<Key, TLSError> {
    if len >= 65536 {
        Err(PAYLOAD_TOO_LONG)
    } else {
        let lenb = U16::from(len as u16).to_be_bytes();
        let tls13_label = Bytes::from_slice(&LABEL_TLS13).concat(label);
        let info = lenb
            .concat(&encode_u8(&tls13_label)?)
            .concat(&encode_u8(context)?);
        hkdf_expand(ha, k, &info, len)
    }
}

pub fn derive_secret(
    hash_algorithm: &HashAlgorithm,
    key: &Key,
    label: &Bytes,
    tx: &Digest,
) -> Result<Key, TLSError> {
    hkdf_expand_label(hash_algorithm, key, label, tx, hash_algorithm.hash_len())
}

pub fn derive_binder_key(ha: &HashAlgorithm, k: &Key) -> Result<MacKey, TLSError> {
    let early_secret = hkdf_extract(ha, k, &zero_key(ha))?;
    derive_secret(
        ha,
        &early_secret,
        &bytes(&LABEL_RES_BINDER),
        &hash_empty(ha)?,
    )
}

pub fn derive_aead_key_iv(
    hash_algorithm: &HashAlgorithm,
    aead_algorithm: &AeadAlgorithm,
    key: &Key,
) -> Result<AeadKeyIV, TLSError> {
    let sender_write_key = hkdf_expand_label(
        hash_algorithm,
        key,
        &bytes(&LABEL_KEY),
        &Bytes::new(),
        aead_algorithm.key_len(),
    )?;
    let sender_write_iv = hkdf_expand_label(
        hash_algorithm,
        key,
        &bytes(&LABEL_IV),
        &Bytes::new(),
        aead_algorithm.iv_len(),
    )?;
    Ok(AeadKeyIV::new(
        AeadKey::new(sender_write_key, *aead_algorithm),
        sender_write_iv,
    ))
}

pub fn derive_0rtt_keys(
    hash_algorithm: &HashAlgorithm,
    aead_algoorithm: &AeadAlgorithm,
    key: &Key,
    tx: &Digest,
) -> Result<(AeadKeyIV, Key), TLSError> {
    let early_secret = hkdf_extract(hash_algorithm, key, &zero_key(hash_algorithm))?;
    let client_early_traffic_secret = derive_secret(
        hash_algorithm,
        &early_secret,
        &bytes(&LABEL_C_E_TRAFFIC),
        tx,
    )?;
    let early_exporter_master_secret = derive_secret(
        hash_algorithm,
        &early_secret,
        &bytes(&LABEL_E_EXP_MASTER),
        tx,
    )?;
    let sender_write_key_iv = derive_aead_key_iv(
        hash_algorithm,
        aead_algoorithm,
        &client_early_traffic_secret,
    )?;
    Ok((sender_write_key_iv, early_exporter_master_secret))
}

pub fn derive_finished_key(ha: &HashAlgorithm, k: &Key) -> Result<MacKey, TLSError> {
    hkdf_expand_label(
        ha,
        k,
        &bytes(&LABEL_FINISHED),
        &Bytes::new(),
        ha.hmac_tag_len(),
    )
}

/// Derive the handshake keys and master secret.
pub(crate) fn derive_hk_ms(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    shared_secret: &Key,
    psko: &Option<Psk>,
    transcript_hash: &Digest,
) -> Result<(AeadKeyIV, AeadKeyIV, MacKey, MacKey, Key), TLSError> {
    let psk = if let Some(k) = psko {
        k.clone()
    } else {
        zero_key(ha)
    };
    let early_secret = hkdf_extract(ha, &psk, &zero_key(ha))?;
    let digest_emp = hash_empty(ha)?;
    let derived_secret = derive_secret(ha, &early_secret, &bytes(&LABEL_DERIVED), &digest_emp)?;
    let handshake_secret = hkdf_extract(ha, shared_secret, &derived_secret)?;
    let client_handshake_traffic_secret = derive_secret(
        ha,
        &handshake_secret,
        &bytes(&LABEL_C_HS_TRAFFIC),
        transcript_hash,
    )?;
    let server_handshake_traffic_secret = derive_secret(
        ha,
        &handshake_secret,
        &bytes(&LABEL_S_HS_TRAFFIC),
        transcript_hash,
    )?;
    let client_finished_key = derive_finished_key(ha, &client_handshake_traffic_secret)?;
    let server_finished_key = derive_finished_key(ha, &server_handshake_traffic_secret)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_handshake_traffic_secret)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_handshake_traffic_secret)?;
    let master_secret_ = derive_secret(ha, &handshake_secret, &bytes(&LABEL_DERIVED), &digest_emp)?;
    let master_secret = hkdf_extract(ha, &zero_key(ha), &master_secret_)?;
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
    master_secret: &Key,
    tx: &Digest,
) -> Result<(AeadKeyIV, AeadKeyIV, Key), TLSError> {
    let client_application_traffic_secret_0 =
        derive_secret(ha, master_secret, &bytes(&LABEL_C_AP_TRAFFIC), tx)?;
    let server_application_traffic_secret_0 =
        derive_secret(ha, master_secret, &bytes(&LABEL_S_AP_TRAFFIC), tx)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_application_traffic_secret_0)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_application_traffic_secret_0)?;
    let exporter_master_secret = derive_secret(ha, master_secret, &bytes(&LABEL_EXP_MASTER), tx)?;
    Ok((
        client_write_key_iv,
        server_write_key_iv,
        exporter_master_secret,
    ))
}

pub(crate) fn derive_rms(
    ha: &HashAlgorithm,
    master_secret: &Key,
    tx: &Digest,
) -> Result<Key, TLSError> {
    derive_secret(ha, master_secret, &bytes(&LABEL_RES_MASTER), tx)
}

/* Handshake State Machine */
/* We implement a simple linear state machine:
PostClientHello -> PostServerHello -> PostCertificateVerify ->
PostServerFinished -> PostClientFinished
There are no optional steps, all states must be traversed, even if the traversals are NOOPS.
See "put_psk_skip_server_signature" below */

pub struct ClientPostClientHello(Random, Algorithms, KemSk, Option<Psk>, Transcript);
pub struct ClientPostServerHello(Random, Random, Algorithms, Key, MacKey, MacKey, Transcript);
pub struct ClientPostCertificateVerify(Random, Random, Algorithms, Key, MacKey, MacKey, Transcript);
pub struct ClientPostServerFinished(Random, Random, Algorithms, Key, MacKey, Transcript);
pub struct ClientPostClientFinished(Random, Random, Algorithms, Key, Transcript);

pub fn algs_post_client_hello(st: &ClientPostClientHello) -> Algorithms {
    st.1
}
pub fn algs_post_server_hello(st: &ClientPostServerHello) -> Algorithms {
    st.2
}
pub fn algs_post_client_finished(st: &ClientPostClientFinished) -> Algorithms {
    st.2
}

pub struct ServerPostClientHello(Random, Algorithms, Bytes, Bytes, ServerInfo, Transcript);
pub struct ServerPostServerHello(
    Random,
    Random,
    Algorithms,
    ServerInfo,
    Key,
    MacKey,
    MacKey,
    Transcript,
);
pub struct ServerPostCertificateVerify(Random, Random, Algorithms, Key, MacKey, MacKey, Transcript);
pub struct ServerPostServerFinished(Random, Random, Algorithms, Key, MacKey, Transcript);
pub struct ServerPostClientFinished(Random, Random, Algorithms, Key, Transcript);

/* Handshake Core Functions: See RFC 8446 Section 4 */
/* We delegate all details of message formatting and transcript Digestes to the caller */

/* TLS 1.3 Client Side Handshake Functions */

fn build_client_hello(
    ciphersuite: Algorithms,
    sn: &Bytes,
    tkt: Option<Bytes>,
    psk: Option<Psk>,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<
    (
        HandshakeData,
        Option<ClientCipherState0>,
        ClientPostClientHello,
    ),
    TLSError,
> {
    let gx_len = ciphersuite.kem().kem_priv_len();
    let tx = transcript_empty(ciphersuite.hash());
    let mut cr = [0u8; 32];
    rng.fill_bytes(&mut cr);
    let (x, gx) = kem_keygen(ciphersuite.kem(), rng)?;
    let (ch, trunc_len) = client_hello(&ciphersuite, &cr.into(), &gx, sn, &tkt)?;
    let (nch, cipher0, tx_ch) = compute_psk_binder_zero_rtt(ciphersuite, ch, trunc_len, &psk, tx)?;
    Ok((
        nch,
        cipher0,
        ClientPostClientHello(cr.into(), ciphersuite, x, psk, tx_ch),
    ))
}

fn compute_psk_binder_zero_rtt(
    algs0: Algorithms,
    ch: HandshakeData,
    trunc_len: usize,
    psk: &Option<Psk>,
    tx: Transcript,
) -> Result<(HandshakeData, Option<ClientCipherState0>, Transcript), TLSError> {
    let Algorithms {
        hash: ha,
        aead: ae,
        signature: _sa,
        kem: _ks,
        psk_mode,
        zero_rtt,
    } = algs0;
    match (psk_mode, psk, trunc_len as u8) {
        (true, Some(k), _) => {
            let th_trunc = get_transcript_hash_truncated_client_hello(&tx, &ch, trunc_len)?;
            let mk = derive_binder_key(&ha, k)?;
            let binder = hmac_tag(&ha, &mk, &th_trunc)?;
            let nch = set_client_hello_binder(&algs0, &Some(binder), ch, Some(trunc_len))?;
            let tx_ch = transcript_add1(tx, &nch);
            if zero_rtt {
                let th = get_transcript_hash(&tx_ch)?;
                let (aek, key) = derive_0rtt_keys(&ha, &ae, k, &th)?;
                let cipher0 = Some(client_cipher_state0(ae, aek, 0, key));
                Ok((nch, cipher0, tx_ch))
            } else {
                Ok((nch, None, tx_ch))
            }
        }
        (false, None, 0) => {
            let tx_ch = transcript_add1(tx, &ch);
            Ok((ch, None, tx_ch))
        }
        _ => Err(PSK_MODE_MISMATCH),
    }
}

fn put_server_hello(
    handshake: &HandshakeData,
    state: ClientPostClientHello,
) -> Result<(DuplexCipherStateH, ClientPostServerHello), TLSError> {
    let ClientPostClientHello(cr, ciphersuite, sk, psk, tx) = state;

    let (sr, ct) = parse_server_hello(&ciphersuite, handshake)?;
    let tx = transcript_add1(tx, handshake);
    let shared_secret = kem_decap(ciphersuite.kem, &ct, &sk)?;
    let th = get_transcript_hash(&tx)?;
    let (chk, shk, cfk, sfk, ms) = derive_hk_ms(
        &ciphersuite.hash,
        &ciphersuite.aead,
        &shared_secret,
        &psk,
        &th,
    )?;

    Ok((
        DuplexCipherStateH::new(chk, 0, shk, 0),
        ClientPostServerHello(cr, sr, ciphersuite, ms, cfk, sfk, tx),
    ))
}

fn put_server_signature(
    ee: &HandshakeData,
    sc: &HandshakeData,
    scv: &HandshakeData,
    st: ClientPostServerHello,
) -> Result<ClientPostCertificateVerify, TLSError> {
    let ClientPostServerHello(cr, sr, algs, ms, cfk, sfk, tx) = st;
    if !algs.psk_mode() {
        parse_encrypted_extensions(&algs, ee)?;
        let tx = transcript_add1(tx, ee);
        let cert = parse_server_certificate(&algs, sc)?;
        let tx = transcript_add1(tx, sc);
        let th_sc = get_transcript_hash(&tx)?;
        let spki = verification_key_from_cert(&cert)?;
        // println!("Server signature scheme: {:?}", spki.0);
        let pk = cert_public_key(&cert, &spki)?;
        let sig = parse_certificate_verify(&algs, scv)?;
        let sigval = (Bytes::from_slice(&PREFIX_SERVER_SIGNATURE)).concat(&th_sc);
        verify(&algs.signature(), &pk, &sigval, &sig)?;
        let tx = transcript_add1(tx, scv);
        Ok(ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk, tx))
    } else {
        Err(PSK_MODE_MISMATCH)
    }
}

fn put_psk_skip_server_signature(
    ee: &HandshakeData,
    st: ClientPostServerHello,
) -> Result<ClientPostCertificateVerify, TLSError> {
    let ClientPostServerHello(cr, sr, algs, ms, cfk, sfk, tx) = st;
    if algs.psk_mode() {
        parse_encrypted_extensions(&algs, ee)?;
        let tx = transcript_add1(tx, ee);
        Ok(ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk, tx))
    } else {
        Err(PSK_MODE_MISMATCH)
    }
}

fn put_server_finished(
    sfin: &HandshakeData,
    st: ClientPostCertificateVerify,
) -> Result<(DuplexCipherState1, ClientPostServerFinished), TLSError> {
    let ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk, tx) = st;
    let Algorithms {
        hash: ha,
        aead: ae,
        signature: _sa,
        kem: _gn,
        psk_mode: _psk_mode,
        zero_rtt: _zero_rtt,
    } = algs;
    let th = get_transcript_hash(&tx)?;
    let vd = parse_finished(&algs, sfin)?;
    hmac_verify(&ha, &sfk, &th, &vd)?;
    let tx = transcript_add1(tx, sfin);
    let th_sfin = get_transcript_hash(&tx)?;
    let (cak, sak, exp) = derive_app_keys(&ha, &ae, &ms, &th_sfin)?;
    let cipher1 = duplex_cipher_state1(ae, cak, 0, sak, 0, exp);
    Ok((cipher1, ClientPostServerFinished(cr, sr, algs, ms, cfk, tx)))
}

fn get_client_finished(
    st: ClientPostServerFinished,
) -> Result<(HandshakeData, ClientPostClientFinished), TLSError> {
    let ClientPostServerFinished(cr, sr, algs, ms, cfk, tx) = st;
    let th = get_transcript_hash(&tx)?;
    let vd = hmac_tag(&algs.hash(), &cfk, &th)?;
    let cfin = finished(&algs, &vd)?;
    let tx = transcript_add1(tx, &cfin);
    let th = get_transcript_hash(&tx)?;
    let rms = derive_rms(&algs.hash(), &ms, &th)?;
    Ok((cfin, ClientPostClientFinished(cr, sr, algs, rms, tx)))
}

// Client-Side Handshake API: Usable by Quic and TLS
// client_init -> (encrypt_zerortt)* ->
// client_set_params -> (encrypt_handshake | decrypt_handshake)* ->
// client_finish -> (encrypt_data | decrypt_data)*

pub fn client_init(
    algs: Algorithms,
    sn: &Bytes,
    tkt: Option<Bytes>,
    psk: Option<Psk>,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<
    (
        HandshakeData,
        Option<ClientCipherState0>,
        ClientPostClientHello,
    ),
    TLSError,
> {
    build_client_hello(algs, sn, tkt, psk, rng)
}

/// Update the client state after generating the client hello message.
pub(crate) fn client_set_params(
    payload: &HandshakeData,
    st: ClientPostClientHello,
) -> Result<(DuplexCipherStateH, ClientPostServerHello), TLSError> {
    put_server_hello(payload, st)
}

pub fn client_finish(
    payload: &HandshakeData,
    st: ClientPostServerHello,
) -> Result<(HandshakeData, DuplexCipherState1, ClientPostClientFinished), TLSError> {
    match algs_post_server_hello(&st).psk_mode() {
        false => {
            let (ee, sc, scv, sfin) = get_handshake_messages4(payload)?;
            let cstate_cv = put_server_signature(&ee, &sc, &scv, st)?;
            let (cipher, cstate_fin) = put_server_finished(&sfin, cstate_cv)?;
            let (cfin, cstate) = get_client_finished(cstate_fin)?;
            Ok((cfin, cipher, cstate))
        }
        true => {
            let (ee, sfin) = get_handshake_messages2(payload)?;
            let cstate_cv = put_psk_skip_server_signature(&ee, st)?;
            let (cipher, cstate_fin) = put_server_finished(&sfin, cstate_cv)?;
            let (cfin, cstate) = get_client_finished(cstate_fin)?;
            Ok((cfin, cipher, cstate))
        }
    }
}

/* TLS 1.3 Server Side Handshake Functions */

fn put_client_hello(
    algs: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
) -> Result<(Option<ServerCipherState0>, ServerPostClientHello), TLSError> {
    let (cr, sid, sni, gx, tkto, bindero, trunc_len) = parse_client_hello(&algs, ch)?;
    //println!("parse_client_hello");
    let tx = transcript_empty(algs.hash());
    let th_trunc = get_transcript_hash_truncated_client_hello(&tx, ch, trunc_len)?;
    let tx = transcript_add1(tx, ch);
    let th = get_transcript_hash(&tx)?;
    let server = lookup_db(algs, &db, &sni, &tkto)?;
    let cipher0 = process_psk_binder_zero_rtt(algs, th, th_trunc, &server.psk_opt, bindero)?;
    Ok((
        cipher0,
        ServerPostClientHello(cr, algs, sid, gx, server, tx),
    ))
}

/// Process the PSK binder for 0-RTT
fn process_psk_binder_zero_rtt(
    ciphersuite: Algorithms,
    th_trunc: Digest,
    th: Digest,
    psko: &Option<Psk>,
    bindero: Option<Bytes>,
) -> Result<Option<ServerCipherState0>, TLSError> {
    match (ciphersuite.psk_mode, psko, bindero) {
        (true, Some(k), Some(binder)) => {
            let mk = derive_binder_key(&ciphersuite.hash, k)?;
            hmac_verify(&ciphersuite.hash, &mk, &th_trunc, &binder)?;
            if ciphersuite.zero_rtt {
                let (key_iv, early_exporter_ms) =
                    derive_0rtt_keys(&ciphersuite.hash, &ciphersuite.aead, k, &th)?;
                let cipher0 = Some(server_cipher_state0(key_iv, 0, early_exporter_ms));
                Ok(cipher0)
            } else {
                Ok(None)
            }
        }
        (false, None, None) => Ok(None),
        _ => Err(PSK_MODE_MISMATCH),
    }
}

fn get_server_hello(
    st: ServerPostClientHello,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<(HandshakeData, DuplexCipherStateH, ServerPostServerHello), TLSError> {
    let ServerPostClientHello(cr, algs, sid, gx, server, tx) = st;
    let Algorithms {
        hash: ha,
        aead: ae,
        signature: _sa,
        kem: ks,
        psk_mode: _psk_mode,
        zero_rtt: _zero_rtt,
    } = algs;

    let mut sr = [0u8; 32];
    rng.fill_bytes(&mut sr);
    let (shared_secret, gy) = kem_encap(ks, &gx, rng)?;
    let sh = server_hello(&algs, &sr.into(), &sid, &gy)?;
    let tx = transcript_add1(tx, &sh);
    let transcript_hash = get_transcript_hash(&tx)?;
    let (chk, shk, cfk, sfk, ms) =
        derive_hk_ms(&ha, &ae, &shared_secret, &server.psk_opt, &transcript_hash)?;
    Ok((
        sh,
        DuplexCipherStateH::new(shk, 0, chk, 0),
        ServerPostServerHello(cr, sr.into(), algs, server, ms, cfk, sfk, tx),
    ))
}

fn get_server_signature(
    st: ServerPostServerHello,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<
    (
        HandshakeData,
        HandshakeData,
        HandshakeData,
        ServerPostCertificateVerify,
    ),
    TLSError,
> {
    let ServerPostServerHello(cr, sr, algs, server, ms, cfk, sfk, tx) = st;
    let ee = encrypted_extensions(&algs)?;
    let tx = transcript_add1(tx, &ee);
    if !algs.psk_mode() {
        let sc = server_certificate(&algs, &server.cert)?;
        let tx = transcript_add1(tx, &sc);
        let th = get_transcript_hash(&tx)?;
        let sigval = Bytes::from_slice(&PREFIX_SERVER_SIGNATURE).concat(&th);
        let sig = match algs.signature() {
            SignatureScheme::EcdsaSecp256r1Sha256 => {
                sign(&algs.signature(), &server.sk, &sigval, rng)?
            }
            SignatureScheme::RsaPssRsaSha256 => {
                // To avoid cyclic dependencies between the modules we pull out
                // the values from the RSA certificate here.
                // We could really read this from the key as well.
                let (cert_scheme, cert_slice) = verification_key_from_cert(&server.cert)?;
                let pk = rsa_public_key(&server.cert, cert_slice)?;
                sign_rsa(
                    &server.sk,
                    &pk.modulus,
                    &pk.exponent,
                    cert_scheme,
                    &sigval,
                    rng,
                )?
            }
            SignatureScheme::ED25519 => unimplemented!(),
        };
        let scv = certificate_verify(&algs, &sig)?;
        let tx = transcript_add1(tx, &scv);
        Ok((
            ee,
            sc,
            scv,
            ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk, tx),
        ))
    } else {
        Err(PSK_MODE_MISMATCH)
    }
}

fn get_skip_server_signature(
    st: ServerPostServerHello,
) -> Result<(HandshakeData, ServerPostCertificateVerify), TLSError> {
    let ServerPostServerHello(cr, sr, algs, server, ms, cfk, sfk, tx) = st;
    if algs.psk_mode() {
        let ee = encrypted_extensions(&algs)?;
        let tx = transcript_add1(tx, &ee);
        Ok((
            ee,
            ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk, tx),
        ))
    } else {
        Err(PSK_MODE_MISMATCH)
    }
}

fn get_server_finished(
    st: ServerPostCertificateVerify,
) -> Result<(HandshakeData, DuplexCipherState1, ServerPostServerFinished), TLSError> {
    let ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk, tx) = st;
    let Algorithms {
        hash: ha,
        aead: ae,
        signature: _sa,
        kem: _gn,
        psk_mode: _psk_mode,
        zero_rtt: _zero_rtt,
    } = algs;
    let th_scv = get_transcript_hash(&tx)?;
    let vd = hmac_tag(&ha, &sfk, &th_scv)?;
    let sfin = finished(&algs, &vd)?;
    let tx = transcript_add1(tx, &sfin);
    let th_sfin = get_transcript_hash(&tx)?;
    let (cak, sak, exp) = derive_app_keys(&ha, &ae, &ms, &th_sfin)?;
    let cipher1 = duplex_cipher_state1(ae, sak, 0, cak, 0, exp);
    Ok((
        sfin,
        cipher1,
        ServerPostServerFinished(cr, sr, algs, ms, cfk, tx),
    ))
}

fn put_client_finished(
    cfin: &HandshakeData,
    st: ServerPostServerFinished,
) -> Result<ServerPostClientFinished, TLSError> {
    let ServerPostServerFinished(cr, sr, algs, ms, cfk, tx) = st;
    let th = get_transcript_hash(&tx)?;
    let vd = parse_finished(&algs, cfin)?;
    hmac_verify(&algs.hash(), &cfk, &th, &vd)?;
    let tx = transcript_add1(tx, cfin);
    let th = get_transcript_hash(&tx)?;
    let rms = derive_rms(&algs.hash(), &ms, &th)?;
    Ok(ServerPostClientFinished(cr, sr, algs, rms, tx))
}

// Server-Side Handshake API: Usable by Quic and TLS
// server_init -> (decrypt_zerortt)* | (encrypt_handshake | decrypt_handshake)* ->
// server_finish -> (encrypt_data | decrypt_data)*

#[allow(clippy::type_complexity)]
pub fn server_init(
    algs: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<
    (
        HandshakeData,
        HandshakeData,
        Option<ServerCipherState0>,
        DuplexCipherStateH,
        DuplexCipherState1,
        ServerPostServerFinished,
    ),
    TLSError,
> {
    let (cipher0, st) = put_client_hello(algs, ch, db)?;
    let (sh, cipher_hs, st) = get_server_hello(st, rng)?;
    match algs.psk_mode() {
        false => {
            let (ee, sc, scv, st) = get_server_signature(st, rng)?;
            let (sfin, cipher1, st) = get_server_finished(st)?;
            let flight = handshake_concat(ee, &handshake_concat(sc, &handshake_concat(scv, &sfin)));
            Ok((sh, flight, cipher0, cipher_hs, cipher1, st))
        }
        true => {
            let (ee, st) = get_skip_server_signature(st)?;
            let (sfin, cipher1, st) = get_server_finished(st)?;
            let flight = handshake_concat(ee, &sfin);
            Ok((sh, flight, cipher0, cipher_hs, cipher1, st))
        }
    }
}

pub fn server_finish(
    cf: &HandshakeData,
    st: ServerPostServerFinished,
) -> Result<ServerPostClientFinished, TLSError> {
    put_client_finished(cf, st)
}
