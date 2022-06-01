// Import hacspec and all needed definitions.
use hacspec_lib::*;
use hacspec_cryptolib::*;
use crate::tls13utils::*;
use crate::tls13formats::*;
use crate::tls13record::*;
use crate::tls13handshake::*;

pub enum Client {
    Client0(ClientPostClientHello,Option<ClientCipherState0>),
    ClientH(ClientPostServerHello,Option<ClientCipherState0>,DuplexCipherStateH,HandshakeData),
    Client1(ClientPostClientFinished,DuplexCipherState1)
}

pub fn in_psk_mode(c:&Client) -> bool {
    match c {
        Client::Client0(cstate,_) => psk_mode(&algs_post_client_hello(cstate)),
        Client::ClientH(cstate,_,_,_) => psk_mode(&algs_post_server_hello(cstate)),
        Client::Client1(cstate,_) => psk_mode(&algs_post_client_finished(cstate)),
    }
}

// Connect
pub fn client_connect(algs:Algorithms,sn:&Bytes,tkt:Option<Bytes>,psk:Option<Key>,ent:Entropy)
-> Res<(Bytes,Client)> {
    let (ch,cipher0,cstate) = client_init(algs,sn,tkt,psk,ent)?;
    let mut ch_rec = handshake_record(&ch)?;
    ch_rec[2] = U8(0x01);
    Ok((ch_rec,Client::Client0(cstate,cipher0)))
}

// The following function reads handshake records and decrypts them using the TLS 1.3 record protocol
// A slightly modified version would work for QUIC
pub fn client_read_handshake(d:&Bytes,st:Client) -> Res<(Option<Bytes>,Client)> {
    match st {
        Client::Client0(cstate,cipher0) => {
            let sf = get_handshake_record(d)?;
            let (cipher1,cstate) = client_set_params(&sf,cstate)?;
            let buf = handshake_data(empty());
            return Ok((None,Client::ClientH(cstate,cipher0,cipher1,buf)))},
        Client::ClientH(cstate,cipher0,cipherH,buf) => {
            let (hd, cipherH) = decrypt_handshake(&d, cipherH)?;
            let buf = handshake_concat(buf,&hd);
            if find_handshake_message(HandshakeType::Finished,&buf,0) {
                let (cfin,cipher1,cstate) = client_finish(&buf,cstate)?;
                let (cf_rec, cipherH) = encrypt_handshake(cfin, 0, cipherH)?;
                return Ok((Some(cf_rec),Client::Client1(cstate,cipher1)))
            } else {
                return Ok((None,Client::ClientH(cstate,cipher0,cipherH,buf)))}},
        _ => {return Err(parse_failed)} 
    }
}

// Reads AppData and Tickets
pub fn client_read(d:&Bytes,st:Client) -> Res<(Option<AppData>,Client)> {
    match st {
        Client::Client1(cstate,cipher1) => {
            let (ty, hd, cipher1) = decrypt_data_or_hs(&d, cipher1)?;
            match ty {
                ContentType::ApplicationData => {
                    return Ok((Some(app_data(hd)),Client::Client1(cstate,cipher1)))
                },
                ContentType::Handshake => {
                    println!("Received Session Ticket");
                    return Ok((None,Client::Client1(cstate,cipher1)))
                }
                _ => {return Err(parse_failed)}
            }
        }
        _ => {return Err(parse_failed)}
    }
}

// Writes AppData
pub fn client_write(d:AppData,st:Client) -> Res<(Bytes,Client)> {
    match st {
        Client::Client1(cstate,cipher1) => {
            let (by,cipher1) = encrypt_data(d, 0, cipher1)?;
            Ok((by,Client::Client1(cstate,cipher1)))
        },
        _ => {return Err(parse_failed)}
    }
}

pub enum Server {
    ServerH(ServerPostServerFinished,Option<ServerCipherState0>,DuplexCipherStateH,DuplexCipherState1),
    Server1(ServerPostClientFinished,DuplexCipherState1)
}


pub fn server_accept(algs:Algorithms,db:ServerDB,ch_rec:&Bytes,ent:Entropy)
-> Res<(Bytes,Bytes,Server)> {
    let ch = get_handshake_record(ch_rec)?;
    let (sh,sf,cipher0,cipherH,cipher1,sstate) = server_init(algs,&ch,db,ent)?;
    let sh_rec = handshake_record(&sh)?;
    let (sf_rec, cipherH) = encrypt_handshake(sf, 0, cipherH)?;
    Ok((sh_rec,sf_rec,Server::ServerH(sstate,cipher0,cipherH,cipher1)))
}
    
pub fn server_read_handshake(cfin_rec:&Bytes,st:Server) -> Res<Server> {
    match st {
        Server::ServerH(sstate,cipher0,cipherH,cipher1) => {
            let cf = get_handshake_record(cfin_rec)?;
            let sstate = server_finish(&cf,sstate)?;
            Ok(Server::Server1(sstate,cipher1))
        },
        _ => {Err(parse_failed)}
    }
}

pub fn server_write(d:AppData,st:Server) -> Res<(Bytes,Server)> {
    match st {
        Server::Server1(sstate,cipher1) => {
            let (by,cipher1) = encrypt_data(d, 0, cipher1)?;
            Ok((by,Server::Server1(sstate,cipher1)))
        },
        _ => {return Err(parse_failed)}
    }    
}

pub fn server_read(d:&Bytes,st:Server) -> Res<(Option<AppData>,Server)> {
    match st {
        Server::Server1(sstate,cipher1) => {
            let (ad, cipher1) = decrypt_data(&d, cipher1)?;
            Ok((Some(ad),Server::Server1(sstate,cipher1)))
        }
        _ => {return Err(parse_failed)}
    }
}
