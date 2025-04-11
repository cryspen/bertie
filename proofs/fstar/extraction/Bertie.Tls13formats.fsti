module Bertie.Tls13formats
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13utils in
  ()

let v_LABEL_IV: t_Array u8 (mk_usize 2) =
  let list = [mk_u8 105; mk_u8 118] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

let v_LABEL_KEY: t_Array u8 (mk_usize 3) =
  let list = [mk_u8 107; mk_u8 101; mk_u8 121] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
  Rust_primitives.Hax.array_of_list 3 list

let v_LABEL_TLS13: t_Array u8 (mk_usize 6) =
  let list = [mk_u8 116; mk_u8 108; mk_u8 115; mk_u8 49; mk_u8 51; mk_u8 32] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 6);
  Rust_primitives.Hax.array_of_list 6 list

let v_LABEL_DERIVED: t_Array u8 (mk_usize 7) =
  let list = [mk_u8 100; mk_u8 101; mk_u8 114; mk_u8 105; mk_u8 118; mk_u8 101; mk_u8 100] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
  Rust_primitives.Hax.array_of_list 7 list

let v_LABEL_FINISHED: t_Array u8 (mk_usize 8) =
  let list =
    [mk_u8 102; mk_u8 105; mk_u8 110; mk_u8 105; mk_u8 115; mk_u8 104; mk_u8 101; mk_u8 100]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
  Rust_primitives.Hax.array_of_list 8 list

let v_LABEL_RES_BINDER: t_Array u8 (mk_usize 10) =
  let list =
    [
      mk_u8 114; mk_u8 101; mk_u8 115; mk_u8 32; mk_u8 98; mk_u8 105; mk_u8 110; mk_u8 100;
      mk_u8 101; mk_u8 114
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list 10 list

let v_LABEL_EXP_MASTER: t_Array u8 (mk_usize 10) =
  let list =
    [
      mk_u8 101; mk_u8 120; mk_u8 112; mk_u8 32; mk_u8 109; mk_u8 97; mk_u8 115; mk_u8 116;
      mk_u8 101; mk_u8 114
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list 10 list

let v_LABEL_RES_MASTER: t_Array u8 (mk_usize 10) =
  let list =
    [
      mk_u8 114; mk_u8 101; mk_u8 115; mk_u8 32; mk_u8 109; mk_u8 97; mk_u8 115; mk_u8 116;
      mk_u8 101; mk_u8 114
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list 10 list

let v_LABEL_C_E_TRAFFIC: t_Array u8 (mk_usize 11) =
  let list =
    [
      mk_u8 99; mk_u8 32; mk_u8 101; mk_u8 32; mk_u8 116; mk_u8 114; mk_u8 97; mk_u8 102; mk_u8 102;
      mk_u8 105; mk_u8 99
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 11);
  Rust_primitives.Hax.array_of_list 11 list

let v_LABEL_E_EXP_MASTER: t_Array u8 (mk_usize 12) =
  let list =
    [
      mk_u8 101; mk_u8 32; mk_u8 101; mk_u8 120; mk_u8 112; mk_u8 32; mk_u8 109; mk_u8 97; mk_u8 115;
      mk_u8 116; mk_u8 101; mk_u8 114
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list 12 list

let v_LABEL_C_HS_TRAFFIC: t_Array u8 (mk_usize 12) =
  let list =
    [
      mk_u8 99; mk_u8 32; mk_u8 104; mk_u8 115; mk_u8 32; mk_u8 116; mk_u8 114; mk_u8 97; mk_u8 102;
      mk_u8 102; mk_u8 105; mk_u8 99
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list 12 list

let v_LABEL_S_HS_TRAFFIC: t_Array u8 (mk_usize 12) =
  let list =
    [
      mk_u8 115; mk_u8 32; mk_u8 104; mk_u8 115; mk_u8 32; mk_u8 116; mk_u8 114; mk_u8 97; mk_u8 102;
      mk_u8 102; mk_u8 105; mk_u8 99
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list 12 list

let v_LABEL_C_AP_TRAFFIC: t_Array u8 (mk_usize 12) =
  let list =
    [
      mk_u8 99; mk_u8 32; mk_u8 97; mk_u8 112; mk_u8 32; mk_u8 116; mk_u8 114; mk_u8 97; mk_u8 102;
      mk_u8 102; mk_u8 105; mk_u8 99
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list 12 list

let v_LABEL_S_AP_TRAFFIC: t_Array u8 (mk_usize 12) =
  let list =
    [
      mk_u8 115; mk_u8 32; mk_u8 97; mk_u8 112; mk_u8 32; mk_u8 116; mk_u8 114; mk_u8 97; mk_u8 102;
      mk_u8 102; mk_u8 105; mk_u8 99
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list 12 list

let v_PREFIX_SERVER_SIGNATURE: t_Array u8 (mk_usize 98) =
  let list =
    [
      mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32;
      mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32;
      mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32;
      mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32;
      mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32;
      mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32;
      mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32; mk_u8 32;
      mk_u8 32; mk_u8 84; mk_u8 76; mk_u8 83; mk_u8 32; mk_u8 49; mk_u8 46; mk_u8 51; mk_u8 44;
      mk_u8 32; mk_u8 115; mk_u8 101; mk_u8 114; mk_u8 118; mk_u8 101; mk_u8 114; mk_u8 32; mk_u8 67;
      mk_u8 101; mk_u8 114; mk_u8 116; mk_u8 105; mk_u8 102; mk_u8 105; mk_u8 99; mk_u8 97;
      mk_u8 116; mk_u8 101; mk_u8 86; mk_u8 101; mk_u8 114; mk_u8 105; mk_u8 102; mk_u8 121; mk_u8 0
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 98);
  Rust_primitives.Hax.array_of_list 98 list

let build_server_name__v_PREFIX1: t_Array u8 (mk_usize 2) =
  let list = [Bertie.Tls13utils.v_U8 (mk_u8 0); Bertie.Tls13utils.v_U8 (mk_u8 0)] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

let build_server_name__v_PREFIX2: t_Array u8 (mk_usize 1) =
  let list = [Bertie.Tls13utils.v_U8 (mk_u8 0)] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
  Rust_primitives.Hax.array_of_list 1 list

/// Build the server name out of the `name` bytes for the client hello.
val build_server_name (name: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 = result in
          match result <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
          | Core.Result.Result_Ok b ->
            (Bertie.Tls13utils.impl_Bytes__len name <: usize) <. mk_usize 65536 &&
            (Bertie.Tls13utils.impl_Bytes__len b <: usize) =.
            ((Bertie.Tls13utils.impl_Bytes__len name <: usize) +! mk_usize 9 <: usize)
          | _ -> true)

/// Check the server name for the sni extension.
/// Returns the value for the server name indicator when successful, and a `[TLSError`]
/// otherwise.
val check_server_name (extension: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Build the supported versions bytes for the client hello.
val supported_versions: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 = result in
          match result <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
          | Core.Result.Result_Ok b ->
            (Bertie.Tls13utils.impl_Bytes__len b <: usize) <=. mk_usize 260
          | _ -> true)

/// Check the TLS version in the provided `client_hello`.
val check_supported_versions (client_hello: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

let server_supported_version__v_SUPPORTED_VERSION_PREFIX: t_Array u8 (mk_usize 2) =
  let list = [Bertie.Tls13utils.v_U8 (mk_u8 0); Bertie.Tls13utils.v_U8 (mk_u8 43)] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

val server_supported_version (e_algorithms: Bertie.Tls13crypto.t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val check_server_supported_version (e_algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

let supported_groups__v_SUPPORTED_GROUPS_PREFIX: t_Array u8 (mk_usize 2) =
  let list = [Bertie.Tls13utils.v_U8 (mk_u8 0); Bertie.Tls13utils.v_U8 (mk_u8 10)] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

val supported_groups (algs: Bertie.Tls13crypto.t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val check_supported_groups (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val check_signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

let psk_key_exchange_modes__v_PSK_MODE_PREFIX: t_Array u8 (mk_usize 2) =
  let list = [Bertie.Tls13utils.v_U8 (mk_u8 0); Bertie.Tls13utils.v_U8 (mk_u8 45)] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

val psk_key_exchange_modes: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val check_psk_key_exchange_modes (client_hello: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

let key_shares__v_PREFIX: t_Array u8 (mk_usize 2) =
  let list = [Bertie.Tls13utils.v_U8 (mk_u8 0); Bertie.Tls13utils.v_U8 (mk_u8 51)] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

val key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val server_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val check_server_key_share (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val pre_shared_key
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (session_ticket: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val check_psk_shared_key (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val server_pre_shared_key (e_algs: Bertie.Tls13crypto.t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val check_server_psk_shared_key (e_algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// TLS Extensions
type t_Extensions = {
  f_sni:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_key_share:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_ticket:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_binder:Core.Option.t_Option Bertie.Tls13utils.t_Bytes
}

/// Merge two options as xor and return `Some(value)`, `None`, or an error if
/// both are `Some`.
val merge_opts (#v_T: Type0) (o1 o2: Core.Option.t_Option v_T)
    : Prims.Pure (Core.Result.t_Result (Core.Option.t_Option v_T) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Merge the two extensions.
/// This will fail if both have set the same extension.
val impl_Extensions__merge (self e2: t_Extensions)
    : Prims.Pure (Core.Result.t_Result t_Extensions u8) Prims.l_True (fun _ -> Prims.l_True)

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
          | Core.Result.Result_Ok (len, out) -> len >=. mk_usize 4
          | _ -> true)

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

let anon_const_AlertLevel_Warning__anon_const_0: u8 = mk_u8 1

let anon_const_AlertLevel_Fatal__anon_const_0: u8 = mk_u8 2

val t_AlertLevel_cast_to_repr (x: t_AlertLevel) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

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
let impl_1: Core.Convert.t_TryFrom t_AlertLevel u8 =
  {
    f_Error = u8;
    f_try_from_pre = (fun (value: u8) -> true);
    f_try_from_post = (fun (value: u8) (out: Core.Result.t_Result t_AlertLevel u8) -> true);
    f_try_from
    =
    fun (value: u8) ->
      match value <: u8 with
      | Rust_primitives.Integers.MkInt 1 ->
        Core.Result.Result_Ok (AlertLevel_Warning <: t_AlertLevel)
        <:
        Core.Result.t_Result t_AlertLevel u8
      | Rust_primitives.Integers.MkInt 2 ->
        Core.Result.Result_Ok (AlertLevel_Fatal <: t_AlertLevel)
        <:
        Core.Result.t_Result t_AlertLevel u8
      | _ -> Bertie.Tls13utils.tlserr #t_AlertLevel (Bertie.Tls13utils.parse_failed () <: u8)
  }

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

let anon_const_AlertDescription_CloseNotify__anon_const_0: u8 = mk_u8 0

let anon_const_AlertDescription_UnexpectedMessage__anon_const_0: u8 = mk_u8 10

let anon_const_AlertDescription_BadRecordMac__anon_const_0: u8 = mk_u8 20

let anon_const_AlertDescription_RecordOverflow__anon_const_0: u8 = mk_u8 22

let anon_const_AlertDescription_HandshakeFailure__anon_const_0: u8 = mk_u8 40

let anon_const_AlertDescription_BadCertificate__anon_const_0: u8 = mk_u8 42

let anon_const_AlertDescription_UnsupportedCertificate__anon_const_0: u8 = mk_u8 43

let anon_const_AlertDescription_CertificateRevoked__anon_const_0: u8 = mk_u8 44

let anon_const_AlertDescription_CertificateExpired__anon_const_0: u8 = mk_u8 45

let anon_const_AlertDescription_CertificateUnknown__anon_const_0: u8 = mk_u8 46

let anon_const_AlertDescription_IllegalParameter__anon_const_0: u8 = mk_u8 47

let anon_const_AlertDescription_UnknownCa__anon_const_0: u8 = mk_u8 48

let anon_const_AlertDescription_AccessDenied__anon_const_0: u8 = mk_u8 49

let anon_const_AlertDescription_DecodeError__anon_const_0: u8 = mk_u8 50

let anon_const_AlertDescription_DecryptError__anon_const_0: u8 = mk_u8 51

let anon_const_AlertDescription_ProtocolVersion__anon_const_0: u8 = mk_u8 70

let anon_const_AlertDescription_InsufficientSecurity__anon_const_0: u8 = mk_u8 71

let anon_const_AlertDescription_InternalError__anon_const_0: u8 = mk_u8 80

let anon_const_AlertDescription_InappropriateFallback__anon_const_0: u8 = mk_u8 86

let anon_const_AlertDescription_UserCanceled__anon_const_0: u8 = mk_u8 90

let anon_const_AlertDescription_MissingExtension__anon_const_0: u8 = mk_u8 109

let anon_const_AlertDescription_UnsupportedExtension__anon_const_0: u8 = mk_u8 110

let anon_const_AlertDescription_UnrecognizedName__anon_const_0: u8 = mk_u8 112

let anon_const_AlertDescription_BadCertificateStatusResponse__anon_const_0: u8 = mk_u8 113

let anon_const_AlertDescription_UnknownPskIdentity__anon_const_0: u8 = mk_u8 115

let anon_const_AlertDescription_CertificateRequired__anon_const_0: u8 = mk_u8 116

let anon_const_AlertDescription_NoApplicationProtocol__anon_const_0: u8 = mk_u8 120

val t_AlertDescription_cast_to_repr (x: t_AlertDescription)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

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
let impl_3: Core.Convert.t_TryFrom t_AlertDescription u8 =
  {
    f_Error = u8;
    f_try_from_pre = (fun (value: u8) -> true);
    f_try_from_post = (fun (value: u8) (out: Core.Result.t_Result t_AlertDescription u8) -> true);
    f_try_from
    =
    fun (value: u8) ->
      match value <: u8 with
      | Rust_primitives.Integers.MkInt 0 ->
        Core.Result.Result_Ok (AlertDescription_CloseNotify <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 10 ->
        Core.Result.Result_Ok (AlertDescription_UnexpectedMessage <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 20 ->
        Core.Result.Result_Ok (AlertDescription_BadRecordMac <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 22 ->
        Core.Result.Result_Ok (AlertDescription_RecordOverflow <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 40 ->
        Core.Result.Result_Ok (AlertDescription_HandshakeFailure <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 42 ->
        Core.Result.Result_Ok (AlertDescription_BadCertificate <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 43 ->
        Core.Result.Result_Ok (AlertDescription_UnsupportedCertificate <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 44 ->
        Core.Result.Result_Ok (AlertDescription_CertificateRevoked <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 45 ->
        Core.Result.Result_Ok (AlertDescription_CertificateExpired <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 46 ->
        Core.Result.Result_Ok (AlertDescription_CertificateUnknown <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 47 ->
        Core.Result.Result_Ok (AlertDescription_IllegalParameter <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 48 ->
        Core.Result.Result_Ok (AlertDescription_UnknownCa <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 49 ->
        Core.Result.Result_Ok (AlertDescription_AccessDenied <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 50 ->
        Core.Result.Result_Ok (AlertDescription_DecodeError <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 51 ->
        Core.Result.Result_Ok (AlertDescription_DecryptError <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 70 ->
        Core.Result.Result_Ok (AlertDescription_ProtocolVersion <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 71 ->
        Core.Result.Result_Ok (AlertDescription_InsufficientSecurity <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 80 ->
        Core.Result.Result_Ok (AlertDescription_InternalError <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 86 ->
        Core.Result.Result_Ok (AlertDescription_InappropriateFallback <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 90 ->
        Core.Result.Result_Ok (AlertDescription_UserCanceled <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 109 ->
        Core.Result.Result_Ok (AlertDescription_MissingExtension <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 110 ->
        Core.Result.Result_Ok (AlertDescription_UnsupportedExtension <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 112 ->
        Core.Result.Result_Ok (AlertDescription_UnrecognizedName <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 113 ->
        Core.Result.Result_Ok (AlertDescription_BadCertificateStatusResponse <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 115 ->
        Core.Result.Result_Ok (AlertDescription_UnknownPskIdentity <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 116 ->
        Core.Result.Result_Ok (AlertDescription_CertificateRequired <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | Rust_primitives.Integers.MkInt 120 ->
        Core.Result.Result_Ok (AlertDescription_NoApplicationProtocol <: t_AlertDescription)
        <:
        Core.Result.t_Result t_AlertDescription u8
      | _ -> Bertie.Tls13utils.tlserr #t_AlertDescription (Bertie.Tls13utils.parse_failed () <: u8)
  }

val get_psk_extensions
      (algorithms: Bertie.Tls13crypto.t_Algorithms)
      (session_ticket extensions: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result (usize & Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result (usize & Bertie.Tls13utils.t_Bytes) u8 = result in
          match result <: Core.Result.t_Result (usize & Bertie.Tls13utils.t_Bytes) u8 with
          | Core.Result.Result_Ok (len, extensions) ->
            len <=. (Bertie.Tls13utils.impl_Bytes__len extensions <: usize)
          | _ -> true)

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
            (Bertie.Tls13formats.Handshake_data.impl_HandshakeData__len client_hello <: usize)
          | _ -> true))
      (fun _ -> Prims.l_True)

val invalid_compression_list: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val unsupported_cipher_alert: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val invalid_compression_method_alert: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val encrypted_extensions (e_algs: Bertie.Tls13crypto.t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val parse_encrypted_extensions
      (e_algs: Bertie.Tls13crypto.t_Algorithms)
      (encrypted_extensions: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val parse_server_certificate (certificate: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val server_certificate (e_algs: Bertie.Tls13crypto.t_Algorithms) (cert: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val ecdsa_signature (sv: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val check_r_len (rlen: usize)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

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

val certificate_verify (algs: Bertie.Tls13crypto.t_Algorithms) (cv: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val parse_finished (finished: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val finished (vd: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

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

let anon_const_ContentType_Invalid__anon_const_0: u8 = mk_u8 0

let anon_const_ContentType_ChangeCipherSpec__anon_const_0: u8 = mk_u8 20

let anon_const_ContentType_Alert__anon_const_0: u8 = mk_u8 21

let anon_const_ContentType_Handshake__anon_const_0: u8 = mk_u8 22

let anon_const_ContentType_ApplicationData__anon_const_0: u8 = mk_u8 23

val t_ContentType_cast_to_repr (x: t_ContentType)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

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

/// Get the [`ContentType`] from the `u8` representation.
val impl_ContentType__try_from_u8 (t: u8)
    : Prims.Pure (Core.Result.t_Result t_ContentType u8) Prims.l_True (fun _ -> Prims.l_True)

val handshake_record (p: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 = result in
          match result <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
          | Core.Result.Result_Ok d ->
            (Bertie.Tls13utils.impl_Bytes__len p.Bertie.Tls13formats.Handshake_data._0 <: usize) <.
            mk_usize 65536 &&
            (Bertie.Tls13utils.impl_Bytes__len d <: usize) =.
            (mk_usize 5 +!
              (Bertie.Tls13utils.impl_Bytes__len p.Bertie.Tls13formats.Handshake_data._0 <: usize)
              <:
              usize)
          | _ -> true)

val protocol_version_alert: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val application_data_instead_of_handshake: Prims.unit
  -> Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val check_handshake_record (p: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val get_handshake_record (p: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Incremental Transcript Construction
/// For simplicity, we store the full transcript, but an internal Digest state would suffice.
type t_Transcript = {
  f_hash_algorithm:Bertie.Tls13crypto.t_HashAlgorithm;
  f_transcript:Bertie.Tls13formats.Handshake_data.t_HandshakeData
}

val impl_Transcript__new (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
    : Prims.Pure t_Transcript Prims.l_True (fun _ -> Prims.l_True)

/// Add the [`HandshakeData`] `msg` to this transcript.
val impl_Transcript__add
      (self: t_Transcript)
      (msg: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure t_Transcript Prims.l_True (fun _ -> Prims.l_True)

/// Get the hash of this transcript
val impl_Transcript__transcript_hash (self: t_Transcript)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the hash of this transcript without the client hello
val impl_Transcript__transcript_hash_without_client_hello
      (self: t_Transcript)
      (client_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: usize)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      (requires
        trunc_len <=.
        (Bertie.Tls13formats.Handshake_data.impl_HandshakeData__len client_hello <: usize))
      (fun _ -> Prims.l_True)

val find_key_share (g: Bertie.Tls13utils.t_Bytes) (ch: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
      (decreases
        (Rust_primitives.Hax.Int.from_machine (Core.Slice.impl__len #u8 ch <: usize)
          <:
          Hax_lib.Int.t_Int))

val check_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Check an extension for validity.
val check_extension (algs: Bertie.Tls13crypto.t_Algorithms) (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result (usize & t_Extensions) u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result (usize & t_Extensions) u8 = result in
          match result <: Core.Result.t_Result (usize & t_Extensions) u8 with
          | Core.Result.Result_Ok (len, exts) -> (Core.Slice.impl__len #u8 bytes <: usize) >=. len
          | _ -> true)

val check_server_extensions (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
      (decreases
        (Rust_primitives.Hax.Int.from_machine (Core.Slice.impl__len #u8 b <: usize)
          <:
          Hax_lib.Int.t_Int))

val parse_server_hello
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (server_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Build the server hello message.
val server_hello
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (server_random session_id kem_ciphertext: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      (requires (Bertie.Tls13utils.impl_Bytes__len server_random <: usize) =. mk_usize 32)
      (ensures
        fun result ->
          let result:Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
            result
          in
          match
            result <: Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
          with
          | Core.Result.Result_Ok sh ->
            (match
                parse_server_hello algs sh
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8
              with
              | Core.Result.Result_Ok (sr, ct) -> sr =. server_random && ct =. kem_ciphertext
              | _ -> false)
          | _ -> true)

val check_extensions_slice (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result t_Extensions u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
      (decreases
        (Rust_primitives.Hax.Int.from_machine (Core.Slice.impl__len #u8 b <: usize)
          <:
          Hax_lib.Int.t_Int))

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
            usize) u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize) u8 =
            result
          in
          match
            result
            <:
            Core.Result.t_Result
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                Bertie.Tls13utils.t_Bytes &
                Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                usize) u8
          with
          | Core.Result.Result_Ok (_, _, _, _, _, _, trunc_len) ->
            trunc_len <=.
            (Bertie.Tls13formats.Handshake_data.impl_HandshakeData__len client_hello <: usize)
          | _ -> true)

/// Build a ClientHello message.
val client_hello
      (algorithms: Bertie.Tls13crypto.t_Algorithms)
      (client_random kem_pk server_name: Bertie.Tls13utils.t_Bytes)
      (session_ticket: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
      (requires (Bertie.Tls13utils.impl_Bytes__len client_random <: usize) =. mk_usize 32)
      (ensures
        fun result ->
          let result:Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8 =
            result
          in
          match
            result
            <:
            Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
          with
          | Core.Result.Result_Ok (ch, trunc_len) ->
            trunc_len <=. (Bertie.Tls13formats.Handshake_data.impl_HandshakeData__len ch <: usize) &&
            (match
                parse_client_hello algorithms ch
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8
              with
              | Core.Result.Result_Ok (cr, _, sn, pk, st, _, _) ->
                cr =. client_random && pk =. kem_pk && sn =. server_name && st =. session_ticket
              | _ -> false)
          | _ -> true)
