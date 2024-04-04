module Bertie.Tls13api
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Client =
  | Client_Client0 :
      Bertie.Tls13handshake.t_ClientPostClientHello ->
      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0
    -> t_Client
  | Client_ClientH :
      Bertie.Tls13handshake.t_ClientPostServerHello ->
      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 ->
      Bertie.Tls13record.t_DuplexCipherStateH ->
      Bertie.Tls13formats.Handshake_data.t_HandshakeData
    -> t_Client
  | Client_Client1 :
      Bertie.Tls13handshake.t_ClientPostClientFinished ->
      Bertie.Tls13record.t_DuplexCipherState1
    -> t_Client

val in_psk_mode (c: t_Client) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

type t_Server =
  | Server_ServerH :
      Bertie.Tls13handshake.t_ServerPostServerFinished ->
      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 ->
      Bertie.Tls13record.t_DuplexCipherStateH ->
      Bertie.Tls13record.t_DuplexCipherState1
    -> t_Server
  | Server_Server1 :
      Bertie.Tls13handshake.t_ServerPostClientFinished ->
      Bertie.Tls13record.t_DuplexCipherState1
    -> t_Server

val impl__Client__connect
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (server_name: Bertie.Tls13utils.t_Bytes)
      (session_ticket psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : Prims.Pure (impl_916461611_ & Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl__Server__read (self: t_Server) (application_data: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Server) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl__Client__read (self: t_Client) (message_bytes: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Client) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl__Server__read_handshake (self: t_Server) (handshake_bytes: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_Server u8) Prims.l_True (fun _ -> Prims.l_True)

val impl__Client__write (self: t_Client) (application_data: Bertie.Tls13utils.t_AppData)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl__Server__write (self: t_Server) (application_data: Bertie.Tls13utils.t_AppData)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Server) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl__Client__read_handshake (self: t_Client) (handshake_bytes: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl__Server__accept
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (db: Bertie.Server.t_ServerDB)
      (client_hello: Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : Prims.Pure
      (impl_916461611_ &
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
