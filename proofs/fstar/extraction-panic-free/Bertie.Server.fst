module Bertie.Server
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let impl__ServerDB__new
      (server_name cert sk: Bertie.Tls13utils.t_Bytes)
      (psk_opt: Core.Option.t_Option (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
     = { f_server_name = server_name; f_cert = cert; f_sk = sk; f_psk_opt = psk_opt } <: t_ServerDB

let lookup_db
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (db: t_ServerDB)
      (sni: Bertie.Tls13utils.t_Bytes)
      (tkt: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
     =
  if
    Bertie.Tls13utils.eq sni (Bertie.Tls13utils.impl__Bytes__new () <: Bertie.Tls13utils.t_Bytes) ||
    Bertie.Tls13utils.eq sni db.f_server_name
  then
    match
      Bertie.Tls13crypto.impl__Algorithms__psk_mode ciphersuite, tkt, db.f_psk_opt
      <:
      (bool & Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
    with
    | true, Core.Option.Option_Some ctkt, Core.Option.Option_Some (stkt, psk) ->
      (match Bertie.Tls13utils.check_eq ctkt stkt with
        | Core.Result.Result_Ok _ ->
          let server:t_ServerInfo =
            {
              f_cert = Core.Clone.f_clone db.f_cert;
              f_sk = Core.Clone.f_clone db.f_sk;
              f_psk_opt
              =
              Core.Option.Option_Some (Core.Clone.f_clone psk)
              <:
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes
            }
            <:
            t_ServerInfo
          in
          Core.Result.Result_Ok server <: Core.Result.t_Result t_ServerInfo u8
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result t_ServerInfo u8)
    | false, _, _ ->
      let server:t_ServerInfo =
        {
          f_cert = Core.Clone.f_clone db.f_cert;
          f_sk = Core.Clone.f_clone db.f_sk;
          f_psk_opt = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
        }
        <:
        t_ServerInfo
      in
      Core.Result.Result_Ok server <: Core.Result.t_Result t_ServerInfo u8
    | _ ->
      Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
      <:
      Core.Result.t_Result t_ServerInfo u8
  else
    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result t_ServerInfo u8
