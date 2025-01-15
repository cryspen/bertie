module Bertie.Tls13formats
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13utils in
  ()

let discriminant_AlertDescription_AccessDenied: u8 = 49uy

let discriminant_AlertDescription_BadCertificate: u8 = 42uy

let discriminant_AlertDescription_BadCertificateStatusResponse: u8 = 113uy

let discriminant_AlertDescription_BadRecordMac: u8 = 20uy

let discriminant_AlertDescription_CertificateExpired: u8 = 45uy

let discriminant_AlertDescription_CertificateRequired: u8 = 116uy

let discriminant_AlertDescription_CertificateRevoked: u8 = 44uy

let discriminant_AlertDescription_CertificateUnknown: u8 = 46uy

let discriminant_AlertDescription_CloseNotify: u8 = 0uy

let discriminant_AlertDescription_DecodeError: u8 = 50uy

let discriminant_AlertDescription_DecryptError: u8 = 51uy

let discriminant_AlertDescription_HandshakeFailure: u8 = 40uy

let discriminant_AlertDescription_IllegalParameter: u8 = 47uy

let discriminant_AlertDescription_InappropriateFallback: u8 = 86uy

let discriminant_AlertDescription_InsufficientSecurity: u8 = 71uy

let discriminant_AlertDescription_InternalError: u8 = 80uy

let discriminant_AlertDescription_MissingExtension: u8 = 109uy

let discriminant_AlertDescription_NoApplicationProtocol: u8 = 120uy

let discriminant_AlertDescription_ProtocolVersion: u8 = 70uy

let discriminant_AlertDescription_RecordOverflow: u8 = 22uy

let discriminant_AlertDescription_UnexpectedMessage: u8 = 10uy

let discriminant_AlertDescription_UnknownCa: u8 = 48uy

let discriminant_AlertDescription_UnknownPskIdentity: u8 = 115uy

let discriminant_AlertDescription_UnrecognizedName: u8 = 112uy

let discriminant_AlertDescription_UnsupportedCertificate: u8 = 43uy

let discriminant_AlertDescription_UnsupportedExtension: u8 = 110uy

/// ```TLS
/// enum {
///     close_notify(0),
///     unexpected_message(10),
///     bad_record_mac(20),
///     record_overflow(22),
///     handshake_failure(40),
///     bad_certificate(42),
///     unsupported_certificate(43),
///     certificate_revoked(44),
///     certificate_expired(45),
///     certificate_unknown(46),
///     illegal_parameter(47),
///     unknown_ca(48),
///     access_denied(49),
///     decode_error(50),
///     decrypt_error(51),
///     protocol_version(70),
///     insufficient_security(71),
///     internal_error(80),
///     inappropriate_fallback(86),
///     user_canceled(90),
///     missing_extension(109),
///     unsupported_extension(110),
///     unrecognized_name(112),
///     bad_certificate_status_response(113),
///     unknown_psk_identity(115),
///     certificate_required(116),
///     no_application_protocol(120),
///     (255)
/// } AlertDescription;
type t_AlertDescription =
  | AlertDescription_CloseNotify : t_AlertDescription
  | AlertDescription_UnexpectedMessage : t_AlertDescription
  | AlertDescription_BadRecordMac : t_AlertDescription
  | AlertDescription_RecordOverflow : t_AlertDescription
  | AlertDescription_HandshakeFailure : t_AlertDescription
  | AlertDescription_BadCertificate : t_AlertDescription
  | AlertDescription_UnsupportedCertificate : t_AlertDescription
  | AlertDescription_CertificateRevoked : t_AlertDescription
  | AlertDescription_CertificateExpired : t_AlertDescription
  | AlertDescription_CertificateUnknown : t_AlertDescription
  | AlertDescription_IllegalParameter : t_AlertDescription
  | AlertDescription_UnknownCa : t_AlertDescription
  | AlertDescription_AccessDenied : t_AlertDescription
  | AlertDescription_DecodeError : t_AlertDescription
  | AlertDescription_DecryptError : t_AlertDescription
  | AlertDescription_ProtocolVersion : t_AlertDescription
  | AlertDescription_InsufficientSecurity : t_AlertDescription
  | AlertDescription_InternalError : t_AlertDescription
  | AlertDescription_InappropriateFallback : t_AlertDescription
  | AlertDescription_UserCanceled : t_AlertDescription
  | AlertDescription_MissingExtension : t_AlertDescription
  | AlertDescription_UnsupportedExtension : t_AlertDescription
  | AlertDescription_UnrecognizedName : t_AlertDescription
  | AlertDescription_BadCertificateStatusResponse : t_AlertDescription
  | AlertDescription_UnknownPskIdentity : t_AlertDescription
  | AlertDescription_CertificateRequired : t_AlertDescription
  | AlertDescription_NoApplicationProtocol : t_AlertDescription

let discriminant_AlertDescription_UserCanceled: u8 = 90uy

val t_AlertDescription_cast_to_repr (x: t_AlertDescription)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let discriminant_AlertLevel_Fatal: u8 = 2uy

/// ```TLS
/// enum {
///     warning(1),
///     fatal(2),
///     (255)
/// } AlertLevel;
/// ```
type t_AlertLevel =
  | AlertLevel_Warning : t_AlertLevel
  | AlertLevel_Fatal : t_AlertLevel

let discriminant_AlertLevel_Warning: u8 = 1uy

val t_AlertLevel_cast_to_repr (x: t_AlertLevel) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let discriminant_ContentType_Alert: u8 = 21uy

let discriminant_ContentType_ApplicationData: u8 = 23uy

let discriminant_ContentType_ChangeCipherSpec: u8 = 20uy

let discriminant_ContentType_Handshake: u8 = 22uy

/// ```TLS
/// enum {
///     invalid(0),
///     change_cipher_spec(20),
///     alert(21),
///     handshake(22),
///     application_data(23),
///     (255)
/// } ContentType;
/// ```
type t_ContentType =
  | ContentType_Invalid : t_ContentType
  | ContentType_ChangeCipherSpec : t_ContentType
  | ContentType_Alert : t_ContentType
  | ContentType_Handshake : t_ContentType
  | ContentType_ApplicationData : t_ContentType

let discriminant_ContentType_Invalid: u8 = 0uy

val t_ContentType_cast_to_repr (x: t_ContentType)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v_LABEL_C_AP_TRAFFIC: t_Array u8 (sz 12) =
  let list = [99uy; 32uy; 97uy; 112uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list 12 list

let v_LABEL_C_E_TRAFFIC: t_Array u8 (sz 11) =
  let list = [99uy; 32uy; 101uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 11);
  Rust_primitives.Hax.array_of_list 11 list

let v_LABEL_C_HS_TRAFFIC: t_Array u8 (sz 12) =
  let list = [99uy; 32uy; 104uy; 115uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list 12 list

let v_LABEL_DERIVED: t_Array u8 (sz 7) =
  let list = [100uy; 101uy; 114uy; 105uy; 118uy; 101uy; 100uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
  Rust_primitives.Hax.array_of_list 7 list

let v_LABEL_EXP_MASTER: t_Array u8 (sz 10) =
  let list = [101uy; 120uy; 112uy; 32uy; 109uy; 97uy; 115uy; 116uy; 101uy; 114uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list 10 list

let v_LABEL_E_EXP_MASTER: t_Array u8 (sz 12) =
  let list = [101uy; 32uy; 101uy; 120uy; 112uy; 32uy; 109uy; 97uy; 115uy; 116uy; 101uy; 114uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list 12 list

let v_LABEL_FINISHED: t_Array u8 (sz 8) =
  let list = [102uy; 105uy; 110uy; 105uy; 115uy; 104uy; 101uy; 100uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
  Rust_primitives.Hax.array_of_list 8 list

let v_LABEL_IV: t_Array u8 (sz 2) =
  let list = [105uy; 118uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

let v_LABEL_KEY: t_Array u8 (sz 3) =
  let list = [107uy; 101uy; 121uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
  Rust_primitives.Hax.array_of_list 3 list

let v_LABEL_RES_BINDER: t_Array u8 (sz 10) =
  let list = [114uy; 101uy; 115uy; 32uy; 98uy; 105uy; 110uy; 100uy; 101uy; 114uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list 10 list

let v_LABEL_RES_MASTER: t_Array u8 (sz 10) =
  let list = [114uy; 101uy; 115uy; 32uy; 109uy; 97uy; 115uy; 116uy; 101uy; 114uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list 10 list

let v_LABEL_S_AP_TRAFFIC: t_Array u8 (sz 12) =
  let list = [115uy; 32uy; 97uy; 112uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list 12 list

let v_LABEL_S_HS_TRAFFIC: t_Array u8 (sz 12) =
  let list = [115uy; 32uy; 104uy; 115uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list 12 list

let v_LABEL_TLS13: t_Array u8 (sz 6) =
  let list = [116uy; 108uy; 115uy; 49uy; 51uy; 32uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 6);
  Rust_primitives.Hax.array_of_list 6 list

let v_PREFIX_SERVER_SIGNATURE: t_Array u8 (sz 98) =
  let list =
    [
      32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy;
      32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy;
      32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy;
      32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy;
      84uy; 76uy; 83uy; 32uy; 49uy; 46uy; 51uy; 44uy; 32uy; 115uy; 101uy; 114uy; 118uy; 101uy; 114uy;
      32uy; 67uy; 101uy; 114uy; 116uy; 105uy; 102uy; 105uy; 99uy; 97uy; 116uy; 101uy; 86uy; 101uy;
      114uy; 105uy; 102uy; 121uy; 0uy
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 98);
  Rust_primitives.Hax.array_of_list 98 list

/// Incremental Transcript Construction
/// For simplicity, we store the full transcript, but an internal Digest state would suffice.
type t_Transcript = {
  f_hash_algorithm:Bertie.Tls13crypto.t_HashAlgorithm;
  f_transcript:Bertie.Tls13formats.Handshake_data.t_HandshakeData
}

val impl__Transcript__new (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
    : Prims.Pure t_Transcript Prims.l_True (fun _ -> Prims.l_True)

let build_server_name__PREFIX1: t_Array u8 (sz 2) =
  let list = [Bertie.Tls13utils.v_U8 0uy; Bertie.Tls13utils.v_U8 0uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

let build_server_name__PREFIX2: t_Array u8 (sz 1) =
  let list = [Bertie.Tls13utils.v_U8 0uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
  Rust_primitives.Hax.array_of_list 1 list

let key_shares__PREFIX: t_Array u8 (sz 2) =
  let list = [Bertie.Tls13utils.v_U8 0uy; Bertie.Tls13utils.v_U8 51uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

let psk_key_exchange_modes__PSK_MODE_PREFIX: t_Array u8 (sz 2) =
  let list = [Bertie.Tls13utils.v_U8 0uy; Bertie.Tls13utils.v_U8 45uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

let server_supported_version__SUPPORTED_VERSION_PREFIX: t_Array u8 (sz 2) =
  let list = [Bertie.Tls13utils.v_U8 0uy; Bertie.Tls13utils.v_U8 43uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

let supported_groups__SUPPORTED_GROUPS_PREFIX: t_Array u8 (sz 2) =
  let list = [Bertie.Tls13utils.v_U8 0uy; Bertie.Tls13utils.v_U8 10uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

/// TLS Extensions
type t_Extensions = {
  f_sni:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_key_share:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_ticket:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_binder:Core.Option.t_Option Bertie.Tls13utils.t_Bytes
}

val application_data_instead_of_handshake: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val invalid_compression_list: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val invalid_compression_method_alert: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val protocol_version_alert: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val unsupported_cipher_alert: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Get the [`ContentType`] from the `u8` representation.
val impl__ContentType__try_from_u8 (t: u8)
    : Prims.Pure (Core.Result.t_Result t_ContentType u8) Prims.l_True (fun _ -> Prims.l_True)

val check_r_len (rlen: usize)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Merge two options as xor and return `Some(value)`, `None`, or an error if
/// both are `Some`.
val merge_opts (#v_T: Type0) (o1 o2: Core.Option.t_Option v_T)
    : Prims.Pure (Core.Result.t_Result (Core.Option.t_Option v_T) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_5:Core.Clone.t_Clone t_AlertLevel

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_6:Core.Marker.t_Copy t_AlertLevel

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_7:Core.Fmt.t_Debug t_AlertLevel

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_8:Core.Marker.t_StructuralPartialEq t_AlertLevel

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_9:Core.Cmp.t_PartialEq t_AlertLevel t_AlertLevel

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_10:Core.Clone.t_Clone t_AlertDescription

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_11:Core.Marker.t_Copy t_AlertDescription

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_12:Core.Fmt.t_Debug t_AlertDescription

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_13:Core.Marker.t_StructuralPartialEq t_AlertDescription

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_14:Core.Cmp.t_PartialEq t_AlertDescription t_AlertDescription

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_15:Core.Clone.t_Clone t_ContentType

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_16:Core.Marker.t_Copy t_ContentType

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_17:Core.Fmt.t_Debug t_ContentType

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_18:Core.Marker.t_StructuralPartialEq t_ContentType

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_19:Core.Cmp.t_PartialEq t_ContentType t_ContentType

/// Add the [`HandshakeData`] `msg` to this transcript.
val impl__Transcript__add
      (self: t_Transcript)
      (msg: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure t_Transcript Prims.l_True (fun _ -> Prims.l_True)

/// Merge the two extensions.
/// This will fail if both have set the same extension.
val impl__Extensions__merge (self e2: t_Extensions)
    : Prims.Pure (Core.Result.t_Result t_Extensions u8) Prims.l_True (fun _ -> Prims.l_True)

/// Get the hash of this transcript
val impl__Transcript__transcript_hash (self: t_Transcript)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the hash of this transcript without the client hello
val impl__Transcript__transcript_hash_without_client_hello
      (self: t_Transcript)
      (client_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: usize)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      (requires
        trunc_len <=.
        (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__len client_hello <: usize))
      (fun _ -> Prims.l_True)

val parse_finished (finished: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val set_client_hello_binder
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (binder: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (client_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: Core.Option.t_Option usize)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      (requires
        (match trunc_len <: Core.Option.t_Option usize with
          | Core.Option.Option_Some tl ->
            tl <=.
            (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__len client_hello <: usize)
          | _ -> true))
      (fun _ -> Prims.l_True)

/// Check the server name for the sni extension.
/// Returns the value for the server name indicator when successful, and a `[TLSError`]
/// otherwise.
val check_server_name (extension: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val parse_server_certificate (certificate: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val check_psk_shared_key (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Build the server name out of the `name` bytes for the client hello.
val build_server_name (name: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val check_psk_key_exchange_modes (client_hello: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val check_server_psk_shared_key (v__algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val check_server_supported_version (v__algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Check the TLS version in the provided `client_hello`.
val check_supported_versions (client_hello: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val finished (vd: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val psk_key_exchange_modes: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val server_certificate (v__algs: Bertie.Tls13crypto.t_Algorithms) (cert: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val check_server_key_share (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// For termination, needs: (decreases Seq.length b)
val check_server_extension (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
            u8 =
            result
          in
          match
            result
            <:
            Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
          with
          | Core.Result.Result_Ok (len, out) -> len >=. sz 4
          | _ -> true)

val check_signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val check_supported_groups (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val supported_groups (algs: Bertie.Tls13crypto.t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Build the supported versions bytes for the client hello.
val supported_versions: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val ecdsa_signature (sv: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val certificate_verify (algs: Bertie.Tls13crypto.t_Algorithms) (cv: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val encrypted_extensions (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val parse_ecdsa_signature (sig: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val parse_certificate_verify
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (certificate_verify: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val parse_encrypted_extensions
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (encrypted_extensions: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val check_handshake_record (p: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val get_handshake_record (p: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val handshake_record (p: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 = result in
          match result <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
          | Core.Result.Result_Ok d ->
            (Bertie.Tls13utils.impl__Bytes__len p.Bertie.Tls13formats.Handshake_data._0 <: usize) <.
            sz 65536 &&
            (Bertie.Tls13utils.impl__Bytes__len d <: usize) =.
            (sz 5 +!
              (Bertie.Tls13utils.impl__Bytes__len p.Bertie.Tls13formats.Handshake_data._0 <: usize)
              <:
              usize)
          | _ -> true)

val pre_shared_key
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (session_ticket: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val get_psk_extensions
      (algorithms: Bertie.Tls13crypto.t_Algorithms)
      (session_ticket extensions: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result (usize & Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val server_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val server_pre_shared_key (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val server_supported_version (v__algorithms: Bertie.Tls13crypto.t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Build the server hello message.
val server_hello (algs: Bertie.Tls13crypto.t_Algorithms) (sr sid gy: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Build a ClientHello message.
val client_hello
      (algorithms: Bertie.Tls13crypto.t_Algorithms)
      (client_random kem_pk server_name: Bertie.Tls13utils.t_Bytes)
      (session_ticket: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_TryFrom t_AlertLevel u8 =
  {
    f_Error = u8;
    f_try_from_pre = (fun (value: u8) -> true);
    f_try_from_post = (fun (value: u8) (out: Core.Result.t_Result t_AlertLevel u8) -> true);
    f_try_from
    =
    fun (value: u8) ->
      match value <: u8 with
      | 1uy ->
        Core.Result.Result_Ok (AlertLevel_Warning <: t_AlertLevel)
        <:
        Core.Result.t_Result t_AlertLevel u8
      | 2uy ->
        Core.Result.Result_Ok (AlertLevel_Fatal <: t_AlertLevel)
        <:
        Core.Result.t_Result t_AlertLevel u8
      | _ -> Bertie.Tls13utils.tlserr #t_AlertLevel (Bertie.Tls13utils.parse_failed () <: u8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_TryFrom t_AlertDescription u8 =
  {
    f_Error = u8;
    f_try_from_pre = (fun (value: u8) -> true);
    f_try_from_post = (fun (value: u8) (out: Core.Result.t_Result t_AlertDescription u8) -> true);
    f_try_from
    =
    fun (value: u8) ->
      match value <: u8 with
      | 0uy ->
        Core.Result.Result_Ok (AlertDescription_CloseNotify <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 10uy ->
        Core.Result.Result_Ok (AlertDescription_UnexpectedMessage <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 20uy ->
        Core.Result.Result_Ok (AlertDescription_BadRecordMac <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 22uy ->
        Core.Result.Result_Ok (AlertDescription_RecordOverflow <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 40uy ->
        Core.Result.Result_Ok (AlertDescription_HandshakeFailure <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 42uy ->
        Core.Result.Result_Ok (AlertDescription_BadCertificate <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 43uy ->
        Core.Result.Result_Ok (AlertDescription_UnsupportedCertificate <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 44uy ->
        Core.Result.Result_Ok (AlertDescription_CertificateRevoked <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 45uy ->
        Core.Result.Result_Ok (AlertDescription_CertificateExpired <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 46uy ->
        Core.Result.Result_Ok (AlertDescription_CertificateUnknown <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 47uy ->
        Core.Result.Result_Ok (AlertDescription_IllegalParameter <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 48uy ->
        Core.Result.Result_Ok (AlertDescription_UnknownCa <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 49uy ->
        Core.Result.Result_Ok (AlertDescription_AccessDenied <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 50uy ->
        Core.Result.Result_Ok (AlertDescription_DecodeError <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 51uy ->
        Core.Result.Result_Ok (AlertDescription_DecryptError <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 70uy ->
        Core.Result.Result_Ok (AlertDescription_ProtocolVersion <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 71uy ->
        Core.Result.Result_Ok (AlertDescription_InsufficientSecurity <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 80uy ->
        Core.Result.Result_Ok (AlertDescription_InternalError <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 86uy ->
        Core.Result.Result_Ok (AlertDescription_InappropriateFallback <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 90uy ->
        Core.Result.Result_Ok (AlertDescription_UserCanceled <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 109uy ->
        Core.Result.Result_Ok (AlertDescription_MissingExtension <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 110uy ->
        Core.Result.Result_Ok (AlertDescription_UnsupportedExtension <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 112uy ->
        Core.Result.Result_Ok (AlertDescription_UnrecognizedName <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 113uy ->
        Core.Result.Result_Ok (AlertDescription_BadCertificateStatusResponse <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 115uy ->
        Core.Result.Result_Ok (AlertDescription_UnknownPskIdentity <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 116uy ->
        Core.Result.Result_Ok (AlertDescription_CertificateRequired <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | 120uy ->
        Core.Result.Result_Ok (AlertDescription_NoApplicationProtocol <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | _ -> Bertie.Tls13utils.tlserr #t_AlertDescription (Bertie.Tls13utils.parse_failed () <: u8)
  }

val check_server_extensions (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Needs decreases clause
val find_key_share (g: Bertie.Tls13utils.t_Bytes) (ch: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val check_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Check an extension for validity.
val check_extension (algs: Bertie.Tls13crypto.t_Algorithms) (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result (usize & t_Extensions) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val parse_server_hello
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (server_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val check_extensions_slice (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result t_Extensions u8) Prims.l_True (fun _ -> Prims.l_True)

val check_extensions (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_Extensions u8) Prims.l_True (fun _ -> Prims.l_True)

/// Parse the provided `client_hello` with the given `ciphersuite`.
val parse_client_hello
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (client_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure
      (Core.Result.t_Result
          (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes &
            Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
            Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
            usize) u8) Prims.l_True (fun _ -> Prims.l_True)
