module t13.Tls13api
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open t13.Tls13formats.Handshake_data in
  let open t13.Tls13utils in
  let open Rand_core in
  ()

/// The TLS Client state.
type t_Client =
  | Client_Client0 :
      t13.Tls13handshake.t_ClientPostClientHello ->
      Core.Option.t_Option t13.Tls13record.t_ClientCipherState0
    -> t_Client
  | Client_ClientH :
      t13.Tls13handshake.t_ClientPostServerHello ->
      Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 ->
      t13.Tls13record.t_DuplexCipherStateH ->
      t13.Tls13formats.Handshake_data.t_HandshakeData
    -> t_Client
  | Client_Client1 :
      t13.Tls13handshake.t_ClientPostClientFinished ->
      t13.Tls13record.t_DuplexCipherState1
    -> t_Client

/// Check if the client is using a PSK mode or not.
/// Returns `true` if the client is in PSK mode and `false` otherwise.
val in_psk_mode (c: t_Client) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Start a TLS handshake as client.
/// Note that t13 clients only support a single ciphersuite at a time and
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
val impl_Client__connect
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (server_name: t13.Tls13utils.t_Bytes)
      (session_ticket psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8)
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
val impl_Client__read_handshake
      (self: t_Client)
      (handshake_bytes: t13.Tls13utils.t_Bytes)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
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
val impl_Client__read (self: t_Client) (message_bytes: t13.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Client) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Send application data to the server.
/// The function returns a [`Result`].
/// When successful, the function returns a tuple with the first element the
/// encrypted `application_data` as bytes, and the new [`Client`] state as the second element.
/// If an error occurs, it returns a [`TLSError`].
val impl_Client__write (self: t_Client) (application_data: t13.Tls13utils.t_AppData)
    : Prims.Pure (Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// The TLS server state.
type t_Server =
  | Server_ServerH :
      t13.Tls13handshake.t_ServerPostServerFinished ->
      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 ->
      t13.Tls13record.t_DuplexCipherStateH ->
      t13.Tls13record.t_DuplexCipherState1
    -> t_Server
  | Server_Server1 :
      t13.Tls13handshake.t_ServerPostClientFinished ->
      t13.Tls13record.t_DuplexCipherState1
    -> t_Server

/// Read the next handshake Message.
/// This function takes the current state and `handshake_bytes` and returns
/// the next state or a [`TLSError`].
/// The function returns a [`Result`].
/// When successful, the function returns the next [`Server`] state.
/// If an error occurs, it returns a [`TLSError`].
val impl_Server__read_handshake
      (self: t_Server)
      (handshake_bytes: t13.Tls13utils.t_Bytes)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler & Core.Result.t_Result t_Server u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Send application data to the client.
/// The function returns a [`Result`].
/// When successful, the function returns a tuple with the first element the
/// encrypted `application_data` as bytes, and the new [`Server`] state as the second element.
/// If an error occurs, it returns a [`TLSError`].
val impl_Server__write (self: t_Server) (application_data: t13.Tls13utils.t_AppData)
    : Prims.Pure (Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Server) u8)
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
val impl_Server__read (self: t_Server) (application_data: t13.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Server) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Start a new TLS handshake as server.
/// Note that t13 servers only support a single ciphersuite at a time and
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
val impl_Server__accept
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (db: t13.Server.t_ServerDB)
      (client_hello: t13.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8)
      (requires (t13.Tls13utils.impl_Bytes__len client_hello <: usize) >=. mk_usize 5)
      (fun _ -> Prims.l_True)
