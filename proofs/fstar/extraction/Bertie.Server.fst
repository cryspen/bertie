module Bertie.Server
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13utils in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core_models.Fmt.t_Debug t_ServerDB

let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Default.t_Default t_ServerDB

let impl_3 = impl_3'

let impl_ServerDB__new
      (server_name cert sk: Bertie.Tls13utils.t_Bytes)
      (psk_opt: Core_models.Option.t_Option (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
     = { f_server_name = server_name; f_cert = cert; f_sk = sk; f_psk_opt = psk_opt } <: t_ServerDB

let lookup_db
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (db: t_ServerDB)
      (sni: Bertie.Tls13utils.t_Bytes)
      (tkt: Core_models.Option.t_Option Bertie.Tls13utils.t_Bytes)
     =
  if Bertie.Tls13utils.eq sni db.f_server_name
  then
    match
      Bertie.Tls13crypto.impl_Algorithms__psk_mode ciphersuite, tkt, db.f_psk_opt
      <:
      (bool & Core_models.Option.t_Option Bertie.Tls13utils.t_Bytes &
        Core_models.Option.t_Option (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
    with
    | true, Core_models.Option.Option_Some ctkt, Core_models.Option.Option_Some (stkt, psk) ->
      (match Bertie.Tls13utils.check_eq ctkt stkt <: Core_models.Result.t_Result Prims.unit u8 with
        | Core_models.Result.Result_Ok _ ->
          let server:t_ServerInfo =
            {
              f_cert
              =
              Core_models.Clone.f_clone #Bertie.Tls13utils.t_Bytes
                #FStar.Tactics.Typeclasses.solve
                db.f_cert;
              f_sk
              =
              Core_models.Clone.f_clone #Bertie.Tls13utils.t_Bytes
                #FStar.Tactics.Typeclasses.solve
                db.f_sk;
              f_psk_opt
              =
              Core_models.Option.Option_Some
              (Core_models.Clone.f_clone #Bertie.Tls13utils.t_Bytes
                  #FStar.Tactics.Typeclasses.solve
                  psk)
              <:
              Core_models.Option.t_Option Bertie.Tls13utils.t_Bytes
            }
            <:
            t_ServerInfo
          in
          Core_models.Result.Result_Ok server <: Core_models.Result.t_Result t_ServerInfo u8
        | Core_models.Result.Result_Err err ->
          Core_models.Result.Result_Err err <: Core_models.Result.t_Result t_ServerInfo u8)
    | false, _, _ ->
      let server:t_ServerInfo =
        {
          f_cert
          =
          Core_models.Clone.f_clone #Bertie.Tls13utils.t_Bytes
            #FStar.Tactics.Typeclasses.solve
            db.f_cert;
          f_sk
          =
          Core_models.Clone.f_clone #Bertie.Tls13utils.t_Bytes
            #FStar.Tactics.Typeclasses.solve
            db.f_sk;
          f_psk_opt
          =
          Core_models.Option.Option_None <: Core_models.Option.t_Option Bertie.Tls13utils.t_Bytes
        }
        <:
        t_ServerInfo
      in
      Core_models.Result.Result_Ok server <: Core_models.Result.t_Result t_ServerInfo u8
    | _ ->
      Core_models.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
      <:
      Core_models.Result.t_Result t_ServerInfo u8
  else
    Core_models.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core_models.Result.t_Result t_ServerInfo u8
