module Bertie.Tls13formats.Handshake_data
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13utils in
  ()

/// ```TLS
/// enum {
///     client_hello(1),
///     server_hello(2),
///     new_session_ticket(4),
///     end_of_early_data(5),
///     encrypted_extensions(8),
///     certificate(11),
///     certificate_request(13),
///     certificate_verify(15),
///     finished(20),
///     key_update(24),
///     message_hash(254),
///     (255)
/// } HandshakeType;
/// ```
type t_HandshakeType =
  | HandshakeType_ClientHello : t_HandshakeType
  | HandshakeType_ServerHello : t_HandshakeType
  | HandshakeType_NewSessionTicket : t_HandshakeType
  | HandshakeType_EndOfEarlyData : t_HandshakeType
  | HandshakeType_EncryptedExtensions : t_HandshakeType
  | HandshakeType_Certificate : t_HandshakeType
  | HandshakeType_CertificateRequest : t_HandshakeType
  | HandshakeType_CertificateVerify : t_HandshakeType
  | HandshakeType_Finished : t_HandshakeType
  | HandshakeType_KeyUpdate : t_HandshakeType
  | HandshakeType_MessageHash : t_HandshakeType

let anon_const_HandshakeType_ClientHello__anon_const_0: u8 = mk_u8 1

let anon_const_HandshakeType_ServerHello__anon_const_0: u8 = mk_u8 2

let anon_const_HandshakeType_NewSessionTicket__anon_const_0: u8 = mk_u8 4

let anon_const_HandshakeType_EndOfEarlyData__anon_const_0: u8 = mk_u8 5

let anon_const_HandshakeType_EncryptedExtensions__anon_const_0: u8 = mk_u8 8

let anon_const_HandshakeType_Certificate__anon_const_0: u8 = mk_u8 11

let anon_const_HandshakeType_CertificateRequest__anon_const_0: u8 = mk_u8 13

let anon_const_HandshakeType_CertificateVerify__anon_const_0: u8 = mk_u8 15

let anon_const_HandshakeType_Finished__anon_const_0: u8 = mk_u8 20

let anon_const_HandshakeType_KeyUpdate__anon_const_0: u8 = mk_u8 24

let anon_const_HandshakeType_MessageHash__anon_const_0: u8 = mk_u8 254

val t_HandshakeType_cast_to_repr (x: t_HandshakeType)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core.Clone.t_Clone t_HandshakeType

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:Core.Marker.t_Copy t_HandshakeType

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_3:Core.Fmt.t_Debug t_HandshakeType

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_4:Core.Marker.t_StructuralPartialEq t_HandshakeType

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_5:Core.Cmp.t_PartialEq t_HandshakeType t_HandshakeType

val get_hs_type (t: u8)
    : Prims.Pure (Core.Result.t_Result t_HandshakeType u8) Prims.l_True (fun _ -> Prims.l_True)

/// Hadshake data of the TLS handshake.
type t_HandshakeData = | HandshakeData : Bertie.Tls13utils.t_Bytes -> t_HandshakeData

val to_bytes_inner (hs: t_HandshakeData)
    : Prims.Pure Bertie.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Returns the handshake data bytes.
val impl_HandshakeData__to_bytes (self: t_HandshakeData)
    : Prims.Pure Bertie.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Returns the length, in bytes.
val impl_HandshakeData__len (self: t_HandshakeData)
    : Prims.Pure usize
      Prims.l_True
      (ensures
        fun result ->
          let result:usize = result in
          v result == Seq.length self._0._0)

/// Attempt to parse a handshake message from the beginning of the payload.
/// If successful, returns the parsed message and the unparsed rest of the
/// payload. Returns a [TLSError] if the payload is too short to contain a
/// handshake message or if the payload is shorter than the expected length
/// encoded in its first three bytes.
val impl_HandshakeData__next_handshake_message (self: t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8 = result in
          match result <: Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8 with
          | Core.Result.Result_Ok (m, r) ->
            (impl_HandshakeData__len m <: usize) >=. mk_usize 4 &&
            (impl_HandshakeData__len self <: usize) >=. (impl_HandshakeData__len m <: usize) &&
            ((impl_HandshakeData__len self <: usize) -! (impl_HandshakeData__len m <: usize)
              <:
              usize) =.
            (impl_HandshakeData__len r <: usize)
          | _ -> true)

val to_two_inner (hs_data: t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val to_four_inner (hs_data: t_HandshakeData)
    : Prims.Pure
      (Core.Result.t_Result (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData)
          u8) Prims.l_True (fun _ -> Prims.l_True)

/// Attempt to parse exactly one handshake message of the `expected_type` from
/// `payload`.
/// If successful, returns the parsed handshake message. Returns a [TLSError] if
/// parsing is unsuccessful or the type of the parsed message disagrees with the
/// expected type.
val impl_HandshakeData__as_handshake_message
      (self: t_HandshakeData)
      (expected_type: t_HandshakeType)
    : Prims.Pure (Core.Result.t_Result t_HandshakeData u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result t_HandshakeData u8 = result in
          match result <: Core.Result.t_Result t_HandshakeData u8 with
          | Core.Result.Result_Ok d ->
            (impl_HandshakeData__len self <: usize) >=. mk_usize 4 &&
            ((impl_HandshakeData__len self <: usize) -! mk_usize 4 <: usize) =.
            (impl_HandshakeData__len d <: usize)
          | _ -> true)

/// Attempt to parse exactly two handshake messages from `payload`.
/// If successful, returns the parsed handshake messages. Returns a [TLSError]
/// if parsing of either message fails or if the payload is not fully consumed
/// by parsing two messages.
val impl_HandshakeData__to_two (self: t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Attempt to parse exactly four handshake messages from `payload`.
/// If successful, returns the parsed handshake messages. Returns a [TLSError]
/// if parsing of any message fails or if the payload is not fully consumed
/// by parsing four messages.
val impl_HandshakeData__to_four (self: t_HandshakeData)
    : Prims.Pure
      (Core.Result.t_Result (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData)
          u8) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Core.Convert.t_From t_HandshakeData Bertie.Tls13utils.t_Bytes

val from_bytes_inner (handshake_type: t_HandshakeType) (handshake_bytes: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_HandshakeData u8) Prims.l_True (fun _ -> Prims.l_True)

/// Generate a new [`HandshakeData`] from [`Bytes`] and the [`HandshakeType`].
val impl_HandshakeData__from_bytes
      (handshake_type: t_HandshakeType)
      (handshake_bytes: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_HandshakeData u8) Prims.l_True (fun _ -> Prims.l_True)

/// Returns a new [`HandshakeData`] that contains the bytes of
/// `other` appended to the bytes of `self`.
val impl_HandshakeData__concat (self other: t_HandshakeData)
    : Prims.Pure t_HandshakeData Prims.l_True (fun _ -> Prims.l_True)

/// Beginning at offset `start`, attempt to find a message of type `handshake_type` in `payload`.
/// Returns `true`` if `payload` contains a message of the given type, `false` otherwise.
val impl_HandshakeData__find_handshake_message
      (self: t_HandshakeData)
      (handshake_type: t_HandshakeType)
      (start: usize)
    : Prims.Pure bool
      (requires (impl_HandshakeData__len self <: usize) >=. start)
      (fun _ -> Prims.l_True)
      (decreases
        ((Rust_primitives.Hax.Int.from_machine (impl_HandshakeData__len self <: usize)
            <:
            Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine start <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int))
