// Import hacspec and all needed definitions.
use crate::tls13formats::*;
use crate::tls13handshake::*;
use crate::tls13record::*;
use crate::tls13utils::*;
use crate::tls13crypto::*;

pub enum Client {
    Client0(ClientPostClientHello, Option<ClientCipherState0>),
    ClientH(
        ClientPostServerHello,
        Option<ClientCipherState0>,
        DuplexCipherStateH,
        HandshakeData,
    ),
    Client1(ClientPostClientFinished, DuplexCipherState1),
}

pub fn in_psk_mode(c: &Client) -> bool {
    match c {
        Client::Client0(cstate, _) => psk_mode(&algs_post_client_hello(cstate)),
        Client::ClientH(cstate, _, _, _) => psk_mode(&algs_post_server_hello(cstate)),
        Client::Client1(cstate, _) => psk_mode(&algs_post_client_finished(cstate)),
    }
}

// Connect
pub fn client_connect(
    algs: Algorithms,
    sn: &Bytes,
    tkt: Option<Bytes>,
    psk: Option<Key>,
    ent: Entropy,
) -> Result<(Bytes, Client), TLSError> {
    let (ch, cipher0, cstate) = client_init(algs, sn, tkt, psk, ent)?;
    let mut ch_rec = handshake_record(&ch)?;
    ch_rec[2] = U8(0x01);
    Ok((ch_rec, Client::Client0(cstate, cipher0)))
}

// The following function reads handshake records and decrypts them using the TLS 1.3 record protocol
// A slightly modified version would work for QUIC
pub fn client_read_handshake(d: &Bytes, st: Client) -> Result<(Option<Bytes>, Client), TLSError> {
    match st {
        Client::Client0(cstate, cipher0) => {
            let sf = get_handshake_record(d)?;
            let (cipher1, cstate) = client_set_params(&sf, cstate)?;
            let buf = handshake_data(empty());
            Ok((None, Client::ClientH(cstate, cipher0, cipher1, buf)))
        }
        Client::ClientH(cstate, cipher0, cipher_hs, buf) => {
            let (hd, cipher_hs) = decrypt_handshake(d, cipher_hs)?;
            let buf = handshake_concat(buf, &hd);
            if find_handshake_message(HandshakeType::Finished, &buf, 0) {
                let (cfin, cipher1, cstate) = client_finish(&buf, cstate)?;
                let (cf_rec, _cipher_hs) = encrypt_handshake(cfin, 0, cipher_hs)?;
                Ok((Some(cf_rec), Client::Client1(cstate, cipher1)))
            } else {
                Ok((None, Client::ClientH(cstate, cipher0, cipher_hs, buf)))
            }
        }
        _ => Err(INCORRECT_STATE),
    }
}

// Reads AppData and Tickets
pub fn client_read(d: &Bytes, st: Client) -> Result<(Option<AppData>, Client), TLSError> {
    match st {
        Client::Client1(cstate, cipher1) => {
            let (ty, hd, cipher1) = decrypt_data_or_hs(d, cipher1)?;
            match ty {
                ContentType::ApplicationData => {
                    Ok((Some(app_data(hd)), Client::Client1(cstate, cipher1)))
                }
                ContentType::Handshake => {
                    println!("Received Session Ticket");
                    Ok((None, Client::Client1(cstate, cipher1)))
                }
                _ => Err(PARSE_FAILED),
            }
        }
        _ => Err(INCORRECT_STATE),
    }
}

// Writes AppData
pub fn client_write(d: AppData, st: Client) -> Result<(Bytes, Client), TLSError> {
    match st {
        Client::Client1(cstate, cipher1) => {
            let (by, cipher1) = encrypt_data(d, 0, cipher1)?;
            Ok((by, Client::Client1(cstate, cipher1)))
        }
        _ => Err(INCORRECT_STATE),
    }
}

pub enum Server {
    ServerH(
        ServerPostServerFinished,
        Option<ServerCipherState0>,
        DuplexCipherStateH,
        DuplexCipherState1,
    ),
    Server1(ServerPostClientFinished, DuplexCipherState1),
}

pub fn server_accept(
    algs: Algorithms,
    db: ServerDB,
    ch_rec: &Bytes,
    ent: Entropy,
) -> Result<(Bytes, Bytes, Server), TLSError> {
    let mut ch_rec = ch_rec.clone();
    ch_rec[2] = U8(0x03);
    let ch = get_handshake_record(&ch_rec)?;
    //println!("pre-init succeeded");
    let (sh, sf, cipher0, cipher_hs, cipher1, sstate) = server_init(algs, &ch, db, ent)?;
    //println!("init succeeded");
    let sh_rec = handshake_record(&sh)?;
    let (sf_rec, cipher_hs) = encrypt_handshake(sf, 0, cipher_hs)?;
    Ok((
        sh_rec,
        sf_rec,
        Server::ServerH(sstate, cipher0, cipher_hs, cipher1),
    ))
}

pub fn server_read_handshake(cfin_rec: &Bytes, st: Server) -> Result<Server, TLSError> {
    match st {
        Server::ServerH(sstate, _cipher0, cipher_hs, cipher1) => {
            //println!("to decrypt");
            let (cf, _cipher_hs) = decrypt_handshake(cfin_rec, cipher_hs)?;
            //println!("decrypted");
            let sstate = server_finish(&cf, sstate)?;
            Ok(Server::Server1(sstate, cipher1))
        }
        _ => Err(INCORRECT_STATE),
    }
}

pub fn server_write(d: AppData, st: Server) -> Result<(Bytes, Server), TLSError> {
    match st {
        Server::Server1(sstate, cipher1) => {
            let (by, cipher1) = encrypt_data(d, 0, cipher1)?;
            Ok((by, Server::Server1(sstate, cipher1)))
        }
        _ => Err(INCORRECT_STATE),
    }
}

pub fn server_read(d: &Bytes, st: Server) -> Result<(Option<AppData>, Server), TLSError> {
    match st {
        Server::Server1(sstate, cipher1) => {
            let (ad, cipher1) = decrypt_data(d, cipher1)?;
            Ok((Some(ad), Server::Server1(sstate, cipher1)))
        }
        _ => Err(INCORRECT_STATE),
    }
}
