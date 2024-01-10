module Bertie.Server
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_ServerDB = {
  f_server_name:Bertie.Tls13utils.t_Bytes;
  f_cert:Bertie.Tls13utils.t_Bytes;
  f_sk:Bertie.Tls13utils.t_Bytes;
  f_psk_opt:Core.Option.t_Option (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
}

let impl__ServerDB__new
      (server_name cert sk: Bertie.Tls13utils.t_Bytes)
      (psk_opt: Core.Option.t_Option (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
    : t_ServerDB =
  { f_server_name = server_name; f_cert = cert; f_sk = sk; f_psk_opt = psk_opt } <: t_ServerDB

type t_ServerInfo = {
  f_cert:Bertie.Tls13utils.t_Bytes;
  f_sk:Bertie.Tls13utils.t_Bytes;
  f_psk_opt:Core.Option.t_Option Bertie.Tls13utils.t_Bytes
}

let lookup_db
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (db: t_ServerDB)
      (sni: Bertie.Tls13utils.t_Bytes)
      (tkt: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result t_ServerInfo u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.eq sni
            (Bertie.Tls13utils.impl__Bytes__new () <: Bertie.Tls13utils.t_Bytes)
          <:
          bool) ||
        (Bertie.Tls13utils.eq sni db.f_server_name <: bool)
      then
        match
          (Bertie.Tls13crypto.impl__Algorithms__psk_mode ciphersuite <: bool), tkt, db.f_psk_opt
          <:
          (bool & Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
            Core.Option.t_Option (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
        with
        | true, Core.Option.Option_Some ctkt, Core.Option.Option_Some (stkt, psk) ->
          let* _:Prims.unit =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq ctkt stkt
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist256:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result t_ServerInfo u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist256)
              <:
              Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerInfo u8) Prims.unit
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerInfo u8) Prims.unit
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let server:t_ServerInfo =
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
            Core.Result.Result_Ok server <: Core.Result.t_Result t_ServerInfo u8)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerInfo u8)
            (Core.Result.t_Result t_ServerInfo u8)
        | false, _, _ ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (let server:t_ServerInfo =
              {
                f_cert = Core.Clone.f_clone db.f_cert;
                f_sk = Core.Clone.f_clone db.f_sk;
                f_psk_opt
                =
                Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
              }
              <:
              t_ServerInfo
            in
            Core.Result.Result_Ok server <: Core.Result.t_Result t_ServerInfo u8)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerInfo u8)
            (Core.Result.t_Result t_ServerInfo u8)
        | _ ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
            <:
            Core.Result.t_Result t_ServerInfo u8)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerInfo u8)
            (Core.Result.t_Result t_ServerInfo u8)
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err (Bertie.Tls13utils.parse_failed () <: u8)
          <:
          Core.Result.t_Result t_ServerInfo u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerInfo u8)
          (Core.Result.t_Result t_ServerInfo u8))
