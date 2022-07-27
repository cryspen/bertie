// Import hacspec and all needed definitions.
#[cfg(feature = "evercrypt")]
use evercrypt_cryptolib::*;
#[cfg(not(feature = "evercrypt"))]
use hacspec_cryptolib::*;
use hacspec_lib::*;

use crate::*;

/* TLS 1.3 Key Schedule: See RFC 8446 Section 7 */

pub fn hash_empty(ha: &HashAlgorithm) -> Result<Digest, TLSError> {
    hash(ha, &empty())
}

pub fn hkdf_expand_label(
    ha: &HashAlgorithm,
    k: &Key,
    label: &Bytes,
    context: &Bytes,
    len: usize,
) -> Result<Key, TLSError> {
    // Hack...
    let LABEL_TLS13 = ByteSeq::from_hex("746c733133");

    if len >= 65536 {
        Err(PAYLOAD_TOO_LONG)
    } else {
        let lenb = U16_to_be_bytes(U16(len as u16));
        let tls13_label = LABEL_TLS13.concat(label);

        let a = lbytes1(&tls13_label)?;
        let b = lbytes1(context)?;
        let info = lenb.concat(&a).concat(&b);
        hkdf_expand(ha, k, &info, len as usize)
    }
}

pub fn derive_secret(
    ha: &HashAlgorithm,
    k: &Key,
    label: &Bytes,
    tx: &Digest,
) -> Result<Key, TLSError> {
    hkdf_expand_label(ha, k, label, tx, hash_len(ha))
}

pub fn derive_binder_key(ha: &HashAlgorithm, k: &Key) -> Result<MacKey, TLSError> {
    // Hack...
    let LABEL_RES_BINDER = ByteSeq::from_hex("7265732062696e646572");

    let early_secret = hkdf_extract(ha, k, &zero_key(ha))?;
    let a = hash_empty(ha)?;
    derive_secret(ha, &early_secret, &LABEL_RES_BINDER, &a)
}

pub fn derive_aead_key_iv(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    k: &Key,
) -> Result<AeadKeyIV, TLSError> {
    // Hack...
    let LABEL_KEY = ByteSeq::from_hex("6b6579");
    let LABEL_IV = ByteSeq::from_hex("6976");

    let sender_write_key = hkdf_expand_label(ha, k, &LABEL_KEY, &empty(), ae_key_len(ae))?;
    let sender_write_iv = hkdf_expand_label(ha, k, &LABEL_IV, &empty(), ae_iv_len(ae))?;
    Ok((
        AeadKey::from_seq(&sender_write_key),
        AeadIv::from_seq(&sender_write_iv),
    ))
}

pub fn derive_0rtt_keys(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    k: &Key,
    tx: &Digest,
) -> Result<(AeadKeyIV, Key), TLSError> {
    // Hack...
    let LABEL_C_E_TRAFFIC = ByteSeq::from_hex("6320652074726166666963");
    let LABEL_E_EXP_MASTER = ByteSeq::from_hex("6520657870206d6173746572");

    let early_secret = hkdf_extract(ha, k, &zero_key(ha))?;
    let client_early_traffic_secret = derive_secret(ha, &early_secret, &LABEL_C_E_TRAFFIC, tx)?;
    let early_exporter_master_secret = derive_secret(ha, &early_secret, &LABEL_E_EXP_MASTER, tx)?;
    let sender_write_key_iv = derive_aead_key_iv(ha, ae, &client_early_traffic_secret)?;
    Ok((sender_write_key_iv, early_exporter_master_secret))
}

pub fn derive_finished_key(ha: &HashAlgorithm, k: &Key) -> Result<MacKey, TLSError> {
    // Hack...
    let LABEL_FINISHED = ByteSeq::from_hex("66696e6973686564");

    hkdf_expand_label(ha, k, &LABEL_FINISHED, &empty(), hmac_tag_len(ha))
}

pub fn derive_hk_ms(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    gxy: &Key,
    psko: &Option<PSK>,
    tx: &Digest,
) -> Result<(AeadKeyIV, AeadKeyIV, MacKey, MacKey, Key), TLSError> {
    // Hack...
    let LABEL_DERIVED = ByteSeq::from_hex("64657269766564");
    let LABEL_C_HS_TRAFFIC = ByteSeq::from_hex("632068732074726166666963");
    let LABEL_S_HS_TRAFFIC = ByteSeq::from_hex("732068732074726166666963");

    let psk = match psko {
        Option::Some(k) => Key::from_seq(k),
        Option::None => zero_key(ha),
    };
    let early_secret = hkdf_extract(ha, &psk, &zero_key(ha))?;
    let digest_emp = hash_empty(ha)?;
    let derived_secret = derive_secret(ha, &early_secret, &LABEL_DERIVED, &digest_emp)?;
    //    println!("derived secret: {}", derived_secret.to_hex());
    let handshake_secret = hkdf_extract(ha, gxy, &derived_secret)?;
    //    println!("handshake secret: {}", handshake_secret.to_hex());
    let client_handshake_traffic_secret =
        derive_secret(ha, &handshake_secret, &LABEL_C_HS_TRAFFIC, tx)?;
    //    println!("c h ts: {}", client_handshake_traffic_secret.to_hex());
    let server_handshake_traffic_secret =
        derive_secret(ha, &handshake_secret, &LABEL_S_HS_TRAFFIC, tx)?;
    //   println!("s h ts: {}", server_handshake_traffic_secret.to_hex());
    let client_finished_key = derive_finished_key(ha, &client_handshake_traffic_secret)?;
    //   println!("cfk: {}", client_finished_key.to_hex());
    let server_finished_key = derive_finished_key(ha, &server_handshake_traffic_secret)?;
    //    println!("sfk: {}", server_finished_key.to_hex());
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_handshake_traffic_secret)?;
    //   let (k,iv) = &client_write_key_iv; println!("chk: {}\n     {}", k.to_hex(), iv.to_hex());
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_handshake_traffic_secret)?;
    //   let (k,iv) = &server_write_key_iv; println!("shk: {}\n     {}", k.to_hex(), iv.to_hex());
    let master_secret_ = derive_secret(ha, &handshake_secret, &LABEL_DERIVED, &digest_emp)?;
    let master_secret = hkdf_extract(ha, &zero_key(ha), &master_secret_)?;
    Ok((
        client_write_key_iv,
        server_write_key_iv,
        client_finished_key,
        server_finished_key,
        master_secret,
    ))
}

pub fn derive_app_keys(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    master_secret: &Key,
    tx: &Digest,
) -> Result<(AeadKeyIV, AeadKeyIV, Key), TLSError> {
    // Hack...
    let LABEL_C_AP_TRAFFIC = ByteSeq::from_hex("632061702074726166666963");
    let LABEL_S_AP_TRAFFIC = ByteSeq::from_hex("732061702074726166666963");
    let LABEL_EXP_MASTER = ByteSeq::from_hex("657870206d6173746572");

    let client_application_traffic_secret_0 =
        derive_secret(ha, master_secret, &LABEL_C_AP_TRAFFIC, tx)?;
    let server_application_traffic_secret_0 =
        derive_secret(ha, master_secret, &LABEL_S_AP_TRAFFIC, tx)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_application_traffic_secret_0)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_application_traffic_secret_0)?;
    let exporter_master_secret = derive_secret(ha, master_secret, &LABEL_EXP_MASTER, tx)?;
    Ok((
        client_write_key_iv,
        server_write_key_iv,
        exporter_master_secret,
    ))
}

pub fn derive_rms(ha: &HashAlgorithm, master_secret: &Key, tx: &Digest) -> Result<Key, TLSError> {
    // Hack...
    let LABEL_RES_MASTER = ByteSeq::from_hex("726573206d6173746572");

    derive_secret(ha, master_secret, &LABEL_RES_MASTER, tx)
}

/* Handshake State Machine */
/* We implement a simple linear state machine:
PostClientHello -> PostServerHello -> PostCertificateVerify ->
PostServerFinished -> PostClientFinished
There are no optional steps, all states must be traversed, even if the traversals are NOOPS.
See "put_psk_skip_server_signature" below */

pub struct ClientPostClientHello(Random, Algorithms, KemSk, Option<PSK>, Transcript);

pub struct ClientPostServerHello(Random, Random, Algorithms, Key, MacKey, MacKey, Transcript);

pub struct ClientPostCertificateVerify(Random, Random, Algorithms, Key, MacKey, MacKey, Transcript);

pub struct ClientPostServerFinished(Random, Random, Algorithms, Key, MacKey, Transcript);

pub struct ClientPostClientFinished(Random, Random, Algorithms, Key, Transcript);

pub fn algs_post_client_hello(st: &ClientPostClientHello) -> Algorithms {
    let ClientPostClientHello(_, algs, _, _, _) = st;

    algs.clone()
}

pub fn algs_post_server_hello(st: &ClientPostServerHello) -> Algorithms {
    let ClientPostServerHello(_, _, algs, _, _, _, _) = st;

    algs.clone()
}

pub fn algs_post_client_finished(st: &ClientPostClientFinished) -> Algorithms {
    let ClientPostClientFinished(_, _, algs, _, _) = st;

    algs.clone()
}

pub struct ServerPostClientHello(
    Random,
    Algorithms,
    Bytes,
    Bytes,
    Bytes,
    SignatureKey,
    Option<PSK>,
    Transcript,
);

pub struct ServerPostServerHello(
    Random,
    Random,
    Algorithms,
    Bytes,
    SignatureKey,
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

fn get_client_hello(
    algs0: Algorithms,
    sn: &Bytes,
    tkt: Option<Bytes>,
    psk: Option<PSK>,
    ent: Entropy,
) -> Result<
    (
        HandshakeData,
        Option<ClientCipherState0>,
        ClientPostClientHello,
    ),
    TLSError,
> {
    let gx_len = dh_priv_len(&kem_alg(algs0));
    if ent.len() < 32 + gx_len {
        Err(INSUFFICIENT_ENTROPY)
    } else {
        let tx = transcript_empty(hash_alg(algs0));
        let cr = Random::from_seq(&ent.slice_range(0..32));
        let (x, gx) = kem_keygen(&kem_alg(algs0), ent.slice_range(32..32 + gx_len))?;
        let (ch, trunc_len) = client_hello(algs0, &cr, &gx, sn, &tkt)?;
        let (nch, cipher0, tx_ch) = compute_psk_binder_zero_rtt(algs0, ch, trunc_len, &psk, tx)?;
        Ok((
            nch,
            cipher0,
            ClientPostClientHello(cr, algs0, x, psk, tx_ch),
        ))
    }
}

fn compute_psk_binder_zero_rtt(
    algs0: Algorithms,
    ch: HandshakeData,
    trunc_len: usize,
    psk: &Option<PSK>,
    tx: Transcript,
) -> Result<(HandshakeData, Option<ClientCipherState0>, Transcript), TLSError> {
    let Algorithms(ha, ae, _sa, _ks, psk_mode, zero_rtt) = algs0;

    if psk_mode {
        let k = psk.as_ref().ok_or(PSK_MODE_MISMATCH)?;

        let th_trunc = get_transcript_hash_truncated_client_hello(&tx, &ch, trunc_len)?;
        let mk = derive_binder_key(&ha, k)?;
        let binder = hmac_tag(&ha, &mk, &th_trunc)?;
        let nch = set_client_hello_binder(algs0, &Some(binder), ch, Some(trunc_len))?;
        let tx_ch = transcript_add1(tx, &nch);
        if zero_rtt {
            let th = get_transcript_hash(&tx_ch)?;
            let (aek, key) = derive_0rtt_keys(&ha, &ae, k, &th)?;
            let cipher0 = Some(client_cipher_state0(ae, aek, 0, key));
            Ok((nch, cipher0, tx_ch))
        } else {
            Ok((nch, None, tx_ch))
        }
    } else {
        if psk.is_some() {
            Err(PSK_MODE_MISMATCH)?;
        }

        let tx_ch = transcript_add1(tx, &ch);
        Ok((ch, None, tx_ch))
    }
}

fn put_server_hello(
    sh: &HandshakeData,
    st: ClientPostClientHello,
) -> Result<(DuplexCipherStateH, ClientPostServerHello), TLSError> {
    let ClientPostClientHello(cr, algs0, x, psk, tx) = st;
    let Algorithms(ha, ae, _sa, ks, _psk_mode, _zero_rtt) = algs0;
    let (sr, gy) = parse_server_hello(algs0, sh)?;
    let tx = transcript_add1(tx, sh);
    let gxy = kem_decap(&ks, &gy, x)?;
    let th = get_transcript_hash(&tx)?;
    let (chk, shk, cfk, sfk, ms) = derive_hk_ms(&ha, &ae, &gxy, &psk, &th)?;
    Ok((
        duplex_cipher_state_hs(ae, chk, 0, shk, 0),
        ClientPostServerHello(cr, sr, algs0, ms, cfk, sfk, tx),
    ))
}

fn put_server_signature(
    ee: &HandshakeData,
    sc: &HandshakeData,
    scv: &HandshakeData,
    st: ClientPostServerHello,
) -> Result<ClientPostCertificateVerify, TLSError> {
    // Hack...
    let PREFIX_SERVER_SIGNATURE = ByteSeq::from_hex("20202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020544c5320312e332c2073657276657220436572746966696361746556657269667900");

    let ClientPostServerHello(cr, sr, algs, ms, cfk, sfk, tx) = st;
    if !psk_mode(algs) {
        parse_encrypted_extensions(algs, ee)?;
        let tx = transcript_add1(tx, ee);
        let cert = parse_server_certificate(algs, sc)?;
        let tx = transcript_add1(tx, sc);
        let th_sc = get_transcript_hash(&tx)?;
        let (signature_scheme, certificate_key) = verification_key_from_cert(&cert)?;
        let sig = parse_certificate_verify(algs, scv)?;
        let sigval = PREFIX_SERVER_SIGNATURE.concat(&th_sc);
        // TODO(Refactor): This is used because the API of `evercrypt_cryptolib::verify` wants a `PublicVerificationKey`.
        //                 That enum is directly unpacked in `verify`, though.
        if signature_scheme == SignatureScheme::EcdsaSecp256r1Sha256 {
            let verification_key = ecdsa_public_key(&cert, certificate_key)?;
            let pk = PublicVerificationKey::EcDsa(verification_key);
            verify(&sig_alg(algs), &pk, &bytes(&sigval), &sig)?;
        } else if signature_scheme == SignatureScheme::RsaPssRsaSha256 {
            let verification_key = rsa_public_key(&cert, certificate_key)?;
            let pk = PublicVerificationKey::Rsa(verification_key);
            verify(&sig_alg(algs), &pk, &bytes(&sigval), &sig)?;
        } else {
            Err(UNSUPPORTED)?;
        }
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
    if psk_mode(algs) {
        parse_encrypted_extensions(algs, ee)?;
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
    let Algorithms(ha, ae, _sa, _gn, _psk_mode, _zero_rtt) = algs;
    let th = get_transcript_hash(&tx)?;
    let vd = parse_finished(algs, sfin)?;
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
    let vd = hmac_tag(&hash_alg(algs), &cfk, &th)?;
    let cfin = finished(algs, &vd)?;
    let tx = transcript_add1(tx, &cfin);
    let th = get_transcript_hash(&tx)?;
    let rms = derive_rms(&hash_alg(algs), &ms, &th)?;
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
    psk: Option<PSK>,
    ent: Entropy,
) -> Result<
    (
        HandshakeData,
        Option<ClientCipherState0>,
        ClientPostClientHello,
    ),
    TLSError,
> {
    get_client_hello(algs, sn, tkt, psk, ent)
}

pub fn client_set_params(
    payload: &HandshakeData,
    st: ClientPostClientHello,
) -> Result<(DuplexCipherStateH, ClientPostServerHello), TLSError> {
    put_server_hello(payload, st)
}

pub fn client_finish(
    payload: &HandshakeData,
    st: ClientPostServerHello,
) -> Result<(HandshakeData, DuplexCipherState1, ClientPostClientFinished), TLSError> {
    if psk_mode(algs_post_server_hello(&st)) {
        let (ee, sfin) = get_handshake_messages2(payload)?;
        let cstate_cv = put_psk_skip_server_signature(&ee, st)?;
        let (cipher, cstate_fin) = put_server_finished(&sfin, cstate_cv)?;
        let (cfin, cstate) = get_client_finished(cstate_fin)?;
        Ok((cfin, cipher, cstate))
    } else {
        let (ee, sc, scv, sfin) = get_handshake_messages4(payload)?;
        let cstate_cv = put_server_signature(&ee, &sc, &scv, st)?;
        let (cipher, cstate_fin) = put_server_finished(&sfin, cstate_cv)?;
        let (cfin, cstate) = get_client_finished(cstate_fin)?;
        Ok((cfin, cipher, cstate))
    }
}

/* TLS 1.3 Server Side Handshake Functions */

fn put_client_hello(
    algs: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
) -> Result<(Option<ServerCipherState0>, ServerPostClientHello), TLSError> {
    let (cr, sid, sni, gx, tkto, bindero, trunc_len) = parse_client_hello(algs, ch)?;
    let tx = transcript_empty(hash_alg(algs));
    let th_trunc = get_transcript_hash_truncated_client_hello(&tx, ch, trunc_len)?;
    let tx = transcript_add1(tx, ch);
    let th = get_transcript_hash(&tx)?;
    let (cert, sigk, psko) = lookup_db(algs, &db, &sni, &tkto)?;
    let cipher0 = process_psk_binder_zero_rtt(algs, th, th_trunc, &psko, bindero)?;
    Ok((
        cipher0,
        ServerPostClientHello(cr, algs, sid, gx, cert, sigk, psko, tx),
    ))
}

fn process_psk_binder_zero_rtt(
    algs: Algorithms,
    th_trunc: Digest,
    th: Digest,
    psko: &Option<PSK>,
    bindero: Option<Bytes>,
) -> Result<Option<ServerCipherState0>, TLSError> {
    let Algorithms(ha, ae, _sa, _ks, psk_mode, zero_rtt) = algs;

    if psk_mode {
        match psko {
            Option::Some(k) => match bindero {
                Option::Some(binder) => {
                    process_psk_binder_zero_rtt_a(&th_trunc, &th, &ha, &ae, zero_rtt, k, &binder)
                }
                Option::None => Err(PSK_MODE_MISMATCH),
            },
            Option::None => Err(PSK_MODE_MISMATCH),
        }
    } else {
        if psko.is_none() && bindero.is_none() {
            Ok(None)
        } else {
            Err(PSK_MODE_MISMATCH)
        }
    }
}

fn process_psk_binder_zero_rtt_a(
    th_trunc: &Digest,
    th: &Digest,
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    zero_rtt: bool,
    k: &PSK,
    binder: &Bytes,
) -> Result<Option<ServerCipherState0>, TLSError> {
    let mk = derive_binder_key(&ha, k)?;
    hmac_verify(&ha, &mk, &th_trunc, &binder)?;
    if zero_rtt {
        let (aek, key) = derive_0rtt_keys(&ha, &ae, k, &th)?;
        let cipher0 = Some(server_cipher_state0(ae.clone(), aek, 0, key));
        Ok(cipher0)
    } else {
        Ok(None)
    }
}

fn get_server_hello(
    st: ServerPostClientHello,
    ent: Entropy,
) -> Result<(HandshakeData, DuplexCipherStateH, ServerPostServerHello), TLSError> {
    let ServerPostClientHello(cr, algs, sid, gx, cert, sigk, psk, tx) = st;
    let Algorithms(ha, ae, _sa, ks, _psk_mode, _zero_rtt) = algs;
    if ent.len() < 32 + dh_priv_len(&ks) {
        Err(INSUFFICIENT_ENTROPY)
    } else {
        let sr = Random::from_seq(&ent.slice_range(0..32));
        let (gxy, gy) = kem_encap(&ks, &gx, ent.slice_range(32..32 + dh_priv_len(&ks)))?;
        let sh = server_hello(algs, &sr, &sid, &gy)?;
        let tx = transcript_add1(tx, &sh);
        let th = get_transcript_hash(&tx)?;
        let (chk, shk, cfk, sfk, ms) = derive_hk_ms(&ha, &ae, &gxy, &psk, &th)?;
        Ok((
            sh,
            duplex_cipher_state_hs(ae, shk, 0, chk, 0),
            ServerPostServerHello(cr, sr, algs, cert, sigk, ms, cfk, sfk, tx),
        ))
    }
}

fn get_server_signature(
    st: ServerPostServerHello,
    ent: Entropy,
) -> Result<
    (
        HandshakeData,
        HandshakeData,
        HandshakeData,
        ServerPostCertificateVerify,
    ),
    TLSError,
> {
    // Hack...
    let PREFIX_SERVER_SIGNATURE = ByteSeq::from_hex("20202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020544c5320312e332c2073657276657220436572746966696361746556657269667900");

    let ServerPostServerHello(cr, sr, algs, cert, sigk, ms, cfk, sfk, tx) = st;
    let ee = encrypted_extensions(algs)?;
    let tx = transcript_add1(tx, &ee);
    if !psk_mode(algs) {
        let sc = server_certificate(algs, &cert)?;
        let tx = transcript_add1(tx, &sc);
        let th = get_transcript_hash(&tx)?;
        let sigval = PREFIX_SERVER_SIGNATURE.concat(&th);
        let sig = sign(&sig_alg(algs), &sigk, &sigval, ent)?;
        let scv = certificate_verify(algs, &sig)?;
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
    let ServerPostServerHello(cr, sr, algs, _cert, _sigk, ms, cfk, sfk, tx) = st;
    if psk_mode(algs) {
        let ee = encrypted_extensions(algs)?;
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
    let Algorithms(ha, ae, _sa, _gn, _psk_mode, _zero_rtt) = algs;
    let th_scv = get_transcript_hash(&tx)?;
    let vd = hmac_tag(&ha, &sfk, &th_scv)?;
    let sfin = finished(algs, &vd)?;
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
    let vd = parse_finished(algs, cfin)?;
    hmac_verify(&hash_alg(algs), &cfk, &th, &vd)?;
    let tx = transcript_add1(tx, cfin);
    let th = get_transcript_hash(&tx)?;
    let rms = derive_rms(&hash_alg(algs), &ms, &th)?;
    Ok(ServerPostClientFinished(cr, sr, algs, rms, tx))
}

// Server-Side Handshake API: Usable by Quic and TLS
// server_init -> (decrypt_zerortt)* | (encrypt_handshake | decrypt_handshake)* ->
// server_finish -> (encrypt_data | decrypt_data)*

pub fn server_init(
    algs: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
    ent: Entropy,
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
    let (sh, cipher_hs, st) = get_server_hello(st, ent.slice(0, 32 + dh_priv_len(&kem_alg(algs))))?;

    if psk_mode(algs) {
        let (ee, st) = get_skip_server_signature(st)?;
        let (sfin, cipher1, st) = get_server_finished(st)?;
        let flight = handshake_concat(ee, &sfin);
        Ok((sh, flight, cipher0, cipher_hs, cipher1, st))
    } else {
        let (ee, sc, scv, st) = get_server_signature(st, ent.slice(0, 32))?; //FIX: use 32 extra bytes
        let (sfin, cipher1, st) = get_server_finished(st)?;
        let flight = handshake_concat(ee, &handshake_concat(sc, &handshake_concat(scv, &sfin)));
        Ok((sh, flight, cipher0, cipher_hs, cipher1, st))
    }
}

pub fn server_finish(
    cf: &HandshakeData,
    st: ServerPostServerFinished,
) -> Result<ServerPostClientFinished, TLSError> {
    put_client_finished(cf, st)
}
