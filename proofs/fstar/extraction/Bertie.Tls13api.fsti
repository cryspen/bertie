module Bertie.Tls13api
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13formats.Handshake_data in
  let open Bertie.Tls13utils in
  let open Rand_core in
  ()

/// The TLS server state.
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

/// The TLS Client state.
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

/// Check if the client is using a PSK mode or not.
/// Returns `true` if the client is in PSK mode and `false` otherwise.
val in_psk_mode (c: t_Client) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Send application data to the server.
/// The function returns a [`Result`].
/// When successful, the function returns a tuple with the first element the
/// encrypted `application_data` as bytes, and the new [`Client`] state as the second element.
/// If an error occurs, it returns a [`TLSError`].
val impl__Client__write (self: t_Client) (application_data: Bertie.Tls13utils.t_AppData)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Send application data to the client.
/// The function returns a [`Result`].
/// When successful, the function returns a tuple with the first element the
/// encrypted `application_data` as bytes, and the new [`Server`] state as the second element.
/// If an error occurs, it returns a [`TLSError`].
val impl__Server__write (self: t_Server) (application_data: Bertie.Tls13utils.t_AppData)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Server) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Start a TLS handshake as client.
/// Note that Bertie clients only support a single ciphersuite at a time and
/// do not perform ciphersuite negotiation.
/// This function takes the
/// * `ciphersuite` to use for this client
/// * `server_name` for the server to connect to
/// * `session_ticket` for an optional session ticket
/// * `psk` for an optional pre-shared-key
/// * `entropy` for the randomness required in the handshake
/// The function returns a [`Result`].
/// When successful, the function returns a tuple with the first element the
/// client hello record as bytes, and the [`Client`] state as the second element.
/// If an error occurs, it returns a [`TLSError`].
val impl__Client__connect
      (#impl_916461611_: Type0)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (server_name: Bertie.Tls13utils.t_Bytes)
      (session_ticket psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : Prims.Pure (impl_916461611_ & Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Read application data.
/// This function can be used when the TLS handshake is complete, to read
/// application data from the client.
/// It takes the current state and `application_data` and returns
/// the next state or a [`TLSError`].
/// The function returns a [`Result`].
/// When successful, the function returns a tuple with the first element the
/// application data as bytes option, and the new [`Server`] state as the second element.
/// If there\'s no application data, the first element is [`None`].
/// If an error occurs, it returns a [`TLSError`].
val impl__Server__read (self: t_Server) (application_data: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Server) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Read application data and session tickets.
/// This function can be used when the TLS handshake is complete, to read
/// application data and session tickets from the server.
/// It takes the current state and `message_bytes` and returns
/// the next state or a [`TLSError`].
/// The function returns a [`Result`].
/// When successful, the function returns a tuple with the first element the
/// application data as bytes option, and the new [`Client`] state as the second element.
/// If there's no application data, the first element is [`None`].
/// If an error occurs, it returns a [`TLSError`].
val impl__Client__read (self: t_Client) (message_bytes: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Client) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Read the next handshake Message.
/// This function takes the current state and `handshake_bytes` and returns
/// the next state or a [`TLSError`].
/// The function returns a [`Result`].
/// When successful, the function returns a tuple with the first element the
/// next client handshake message as bytes option, and the next [`Client`] state as
/// the second element.
/// If there's no handshake message, the first element is [`None`].
/// If an error occurs, it returns a [`TLSError`].
val impl__Client__read_handshake (self: t_Client) (handshake_bytes: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Read the next handshake Message.
/// This function takes the current state and `handshake_bytes` and returns
/// the next state or a [`TLSError`].
/// The function returns a [`Result`].
/// When successful, the function returns the next [`Server`] state.
/// If an error occurs, it returns a [`TLSError`].
val impl__Server__read_handshake (self: t_Server) (handshake_bytes: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_Server u8) Prims.l_True (fun _ -> Prims.l_True)

/// Start a new TLS handshake as server.
/// Note that Bertie servers only support a single ciphersuite at a time and
/// do not perform ciphersuite negotiation.
/// This function takes the
/// * `ciphersuite` to use for this server
/// * `db` for the server database containing certificates and keys
/// * `client_hello` for the initial client hello message
/// * `entropy` for the randomness required in the handshake
/// The function returns a [`Result`].
/// When successful, the function returns a three-tuple with the first element the
/// server hello record as bytes, the second the server finished record as bytes,
/// and the new [`Server`] state as the third element.
/// If an error occurs, it returns a [`TLSError`].
val impl__Server__accept
      (#impl_916461611_: Type0)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (db: Bertie.Server.t_ServerDB)
      (client_hello: Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : Prims.Pure
      (impl_916461611_ &
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server) u8)
      (requires (Bertie.Tls13utils.impl__Bytes__len client_hello <: usize) >=. sz 5)
      (fun _ -> Prims.l_True)
