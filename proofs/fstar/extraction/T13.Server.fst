module t13.Server
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open t13.Tls13utils in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Fmt.t_Debug t_ServerDB

let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Clone.t_Clone t_ServerDB

let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core.Default.t_Default t_ServerDB

let impl_3 = impl_3'

let impl_ServerDB__new
      (server_name cert sk: t13.Tls13utils.t_Bytes)
      (psk_opt: Core.Option.t_Option (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes))
     = { f_server_name = server_name; f_cert = cert; f_sk = sk; f_psk_opt = psk_opt } <: t_ServerDB

let lookup_db
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (db: t_ServerDB)
      (sni: t13.Tls13utils.t_Bytes)
      (tkt: Core.Option.t_Option t13.Tls13utils.t_Bytes)
     =
  if
    t13.Tls13utils.eq sni (t13.Tls13utils.impl_Bytes__new () <: t13.Tls13utils.t_Bytes) ||
    t13.Tls13utils.eq sni db.f_server_name
  then
    match
      t13.Tls13crypto.impl_Algorithms__psk_mode ciphersuite, tkt, db.f_psk_opt
      <:
      (bool & Core.Option.t_Option t13.Tls13utils.t_Bytes &
        Core.Option.t_Option (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes))
    with
    | true, Core.Option.Option_Some ctkt, Core.Option.Option_Some (stkt, psk) ->
      (match t13.Tls13utils.check_eq ctkt stkt <: Core.Result.t_Result Prims.unit u8 with
        | Core.Result.Result_Ok _ ->
          let server:t_ServerInfo =
            {
              f_cert
              =
              Core.Clone.f_clone #t13.Tls13utils.t_Bytes
                #FStar.Tactics.Typeclasses.solve
                db.f_cert;
              f_sk
              =
              Core.Clone.f_clone #t13.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve db.f_sk;
              f_psk_opt
              =
              Core.Option.Option_Some
              (Core.Clone.f_clone #t13.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve psk)
              <:
              Core.Option.t_Option t13.Tls13utils.t_Bytes
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
          f_cert
          =
          Core.Clone.f_clone #t13.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve db.f_cert;
          f_sk
          =
          Core.Clone.f_clone #t13.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve db.f_sk;
          f_psk_opt = Core.Option.Option_None <: Core.Option.t_Option t13.Tls13utils.t_Bytes
        }
        <:
        t_ServerInfo
      in
      Core.Result.Result_Ok server <: Core.Result.t_Result t_ServerInfo u8
    | _ ->
      Core.Result.Result_Err t13.Tls13utils.v_PSK_MODE_MISMATCH
      <:
      Core.Result.t_Result t_ServerInfo u8
  else
    Core.Result.Result_Err (t13.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result t_ServerInfo u8
