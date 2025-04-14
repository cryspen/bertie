module t13.Server
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_ServerDB = {
  f_server_name:t13.Tls13utils.t_Bytes;
  f_cert:t13.Tls13utils.t_Bytes;
  f_sk:t13.Tls13utils.t_Bytes;
  f_psk_opt:Core.Option.t_Option (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes)
}

val impl__ServerDB__new
      (server_name cert sk: t13.Tls13utils.t_Bytes)
      (psk_opt: Core.Option.t_Option (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes))
    : Prims.Pure t_ServerDB Prims.l_True (fun _ -> Prims.l_True)

type t_ServerInfo = {
  f_cert:t13.Tls13utils.t_Bytes;
  f_sk:t13.Tls13utils.t_Bytes;
  f_psk_opt:Core.Option.t_Option t13.Tls13utils.t_Bytes
}

val lookup_db
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (db: t_ServerDB)
      (sni: t13.Tls13utils.t_Bytes)
      (tkt: Core.Option.t_Option t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_ServerInfo u8) Prims.l_True (fun _ -> Prims.l_True)
