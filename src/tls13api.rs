// Import hacspec and all needed definitions.
use crate::*;
use hacspec_cryptolib::*;
use hacspec_lib::*;

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
        Client::Client0(cstate, _) => psk_mode(algs_post_client_hello(cstate)),
        Client::ClientH(cstate, _, _, _) => psk_mode(algs_post_server_hello(cstate)),
        Client::Client1(cstate, _) => psk_mode(algs_post_client_finished(cstate)),
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
        Client::Client0(cstate, cipher0) => client_read_handshake_a(d, cstate, cipher0),
        Client::ClientH(cstate, cipher0, cipher_hs, buf) => {
            client_read_handshake_b(d, cstate, cipher0, cipher_hs, buf)
        }
        Client::Client1(_, _) => Err(INCORRECT_STATE),
    }
}

fn client_read_handshake_a(
    d: &Bytes,
    cstate: ClientPostClientHello,
    cipher0: Option<ClientCipherState0>,
) -> Result<(Option<Bytes>, Client), TLSError> {
    let sf = get_handshake_record(d)?;
    let (cipher1, cstate) = client_set_params(&sf, cstate)?;
    let buf = handshake_data(empty());
    Ok((Option::None, Client::ClientH(cstate, cipher0, cipher1, buf)))
}

fn client_read_handshake_b(
    d: &Bytes,
    cstate: ClientPostServerHello,
    cipher0: Option<ClientCipherState0>,
    cipher_hs: DuplexCipherStateH,
    buf: HandshakeData,
) -> Result<(Option<Bytes>, Client), TLSError> {
    let (hd, cipher_hs) = decrypt_handshake(d, cipher_hs)?;
    let buf = handshake_concat(buf, &hd);
    if find_handshake_message(HandshakeType::Finished, &buf, 0) {
        let (cfin, cipher1, cstate) = client_finish(&buf, cstate)?;
        let (cf_rec, _cipher_hs) = encrypt_handshake(cfin, 0, cipher_hs)?;
        Ok((Some(cf_rec), Client::Client1(cstate, cipher1)))
    } else {
        Ok((
            Option::None,
            Client::ClientH(cstate, cipher0, cipher_hs, buf),
        ))
    }
}

// Reads AppData and Tickets
pub fn client_read(d: &Bytes, st: Client) -> Result<(Option<AppData>, Client), TLSError> {
    match st {
        Client::Client0(_, _) => Err(INCORRECT_STATE),
        Client::ClientH(_, _, _, _) => Err(INCORRECT_STATE),
        Client::Client1(cstate, cipher1) => client_read_a(d, cstate, cipher1),
    }
}

fn client_read_a(
    d: &Bytes,
    cstate: ClientPostClientFinished,
    cipher1: DuplexCipherState1,
) -> Result<(Option<AppData>, Client), TLSError> {
    let (ty, hd, cipher1) = decrypt_data_or_hs(d, cipher1)?;

    match ty {
        ContentType::Invalid => Err(PARSE_FAILED),
        ContentType::ChangeCipherSpec => Err(PARSE_FAILED),
        ContentType::Alert => Err(PARSE_FAILED),
        ContentType::Handshake => {
            println!("Received Session Ticket");
            Ok((Option::None, Client::Client1(cstate, cipher1)))
        }
        ContentType::ApplicationData => Ok((Some(app_data(hd)), Client::Client1(cstate, cipher1))),
    }
}

// Writes AppData
pub fn client_write(d: AppData, st: Client) -> Result<(Bytes, Client), TLSError> {
    match st {
        Client::Client0(_, _) => Err(INCORRECT_STATE),
        Client::ClientH(_, _, _, _) => Err(INCORRECT_STATE),
        Client::Client1(cstate, cipher1) => client_write_a(d, cstate, cipher1),
    }
}

fn client_write_a(
    d: AppData,
    cstate: ClientPostClientFinished,
    cipher1: DuplexCipherState1,
) -> Result<(Bytes, Client), TLSError> {
    let (by, cipher1) = encrypt_data(d, 0, cipher1)?;
    Ok((by, Client::Client1(cstate, cipher1)))
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
    let (sh, sf, cipher0, cipher_hs, cipher1, sstate) = server_init(algs, &ch, db, ent)?;
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
            server_read_handshake_a(cfin_rec, sstate, cipher_hs, cipher1)
        }
        Server::Server1(_, _) => Err(INCORRECT_STATE),
    }
}

fn server_read_handshake_a(
    cfin_rec: &Bytes,
    sstate: ServerPostServerFinished,
    cipher_hs: DuplexCipherStateH,
    cipher1: DuplexCipherState1,
) -> Result<Server, TLSError> {
    let (cf, _cipher_hs) = decrypt_handshake(cfin_rec, cipher_hs)?;
    let sstate = server_finish(&cf, sstate)?;
    Ok(Server::Server1(sstate, cipher1))
}

pub fn server_write(d: AppData, st: Server) -> Result<(Bytes, Server), TLSError> {
    match st {
        Server::ServerH(_, _, _, _) => Err(INCORRECT_STATE),
        Server::Server1(sstate, cipher1) => server_write_a(d, sstate, cipher1),
    }
}

fn server_write_a(
    d: AppData,
    sstate: ServerPostClientFinished,
    cipher1: DuplexCipherState1,
) -> Result<(Bytes, Server), TLSError> {
    let (by, cipher1) = encrypt_data(d, 0, cipher1)?;
    Ok((by, Server::Server1(sstate, cipher1)))
}

pub fn server_read(d: &Bytes, st: Server) -> Result<(Option<AppData>, Server), TLSError> {
    match st {
        Server::ServerH(_, _, _, _) => Err(INCORRECT_STATE),
        Server::Server1(sstate, cipher1) => server_read_a(d, sstate, cipher1),
    }
}

fn server_read_a(
    d: &Bytes,
    sstate: ServerPostClientFinished,
    cipher1: DuplexCipherState1,
) -> Result<(Option<AppData>, Server), TLSError> {
    let (ad, cipher1) = decrypt_data(d, cipher1)?;
    Ok((Some(ad), Server::Server1(sstate, cipher1)))
}
