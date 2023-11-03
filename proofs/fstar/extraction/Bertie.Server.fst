module Bertie.Server
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_ServerDB =
  | ServerDB :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Core.Option.t_Option (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
    -> t_ServerDB

let lookup_db
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (db: t_ServerDB)
      (sni: Bertie.Tls13utils.t_Bytes)
      (tkt: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ServerDB server_name cert sk psk_opt:t_ServerDB
      =
        db
      in
      if
        Bertie.Tls13utils.eq sni (Bertie.Tls13utils.impl__Bytes__new <: Bertie.Tls13utils.t_Bytes) ||
        Bertie.Tls13utils.eq sni server_name
      then
        match Bertie.Tls13crypto.psk_mode algs, tkt, psk_opt with
        | true, Core.Option.Option_Some ctkt, Core.Option.Option_Some (stkt, psk) ->
          let* _:Prims.unit =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq ctkt stkt
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist539:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist539)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (Core.Result.Result_Ok
            (Core.Clone.f_clone cert,
              Core.Clone.f_clone sk,
              Core.Option.Option_Some (Core.Clone.f_clone psk)))
        | false, _, _ ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (Core.Result.Result_Ok
            (Core.Clone.f_clone cert, Core.Clone.f_clone sk, Core.Option.Option_None))
        | _ ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH)
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.parse_failed))