module Bertie.Server
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13utils in
  ()

/// The Server Database
type t_ServerDB = {
  f_server_name:Bertie.Tls13utils.t_Bytes;
  f_cert:Bertie.Tls13utils.t_Bytes;
  f_sk:Bertie.Tls13utils.t_Bytes;
  f_psk_opt:Core.Option.t_Option (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
}

/// Create a new server database.
/// Note that this only holds one value at a time right now. #51
val impl__ServerDB__new
      (server_name cert sk: Bertie.Tls13utils.t_Bytes)
      (psk_opt: Core.Option.t_Option (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
    : Prims.Pure t_ServerDB Prims.l_True (fun _ -> Prims.l_True)

/// Global server information.
type t_ServerInfo = {
  f_cert:Bertie.Tls13utils.t_Bytes;
  f_sk:Bertie.Tls13utils.t_Bytes;
  f_psk_opt:Core.Option.t_Option Bertie.Tls13utils.t_Bytes
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core.Fmt.t_Debug t_ServerDB

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:Core.Clone.t_Clone t_ServerDB

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_3:Core.Default.t_Default t_ServerDB

/// Look up a server for the given `ciphersuite`.
/// The function returns a server with the first algorithm it finds.
val lookup_db
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (db: t_ServerDB)
      (sni: Bertie.Tls13utils.t_Bytes)
      (tkt: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_ServerInfo u8) Prims.l_True (fun _ -> Prims.l_True)
