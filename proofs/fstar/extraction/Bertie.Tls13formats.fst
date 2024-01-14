module Bertie.Tls13formats
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

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

type t_AlertLevel =
  | AlertLevel_Warning : t_AlertLevel
  | AlertLevel_Fatal : t_AlertLevel

type t_ContentType =
  | ContentType_Invalid : t_ContentType
  | ContentType_ChangeCipherSpec : t_ContentType
  | ContentType_Alert : t_ContentType
  | ContentType_Handshake : t_ContentType
  | ContentType_ApplicationData : t_ContentType

let v_LABEL_C_AP_TRAFFIC: t_Array u8 (sz 12) =
  let list = [99uy; 32uy; 97uy; 112uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_C_E_TRAFFIC: t_Array u8 (sz 11) =
  let list = [99uy; 32uy; 101uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 11);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_C_HS_TRAFFIC: t_Array u8 (sz 12) =
  let list = [99uy; 32uy; 104uy; 115uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_DERIVED: t_Array u8 (sz 7) =
  let list = [100uy; 101uy; 114uy; 105uy; 118uy; 101uy; 100uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_EXP_MASTER: t_Array u8 (sz 10) =
  let list = [101uy; 120uy; 112uy; 32uy; 109uy; 97uy; 115uy; 116uy; 101uy; 114uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_E_EXP_MASTER: t_Array u8 (sz 12) =
  let list = [101uy; 32uy; 101uy; 120uy; 112uy; 32uy; 109uy; 97uy; 115uy; 116uy; 101uy; 114uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_FINISHED: t_Array u8 (sz 8) =
  let list = [102uy; 105uy; 110uy; 105uy; 115uy; 104uy; 101uy; 100uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_IV: t_Array u8 (sz 2) =
  let list = [105uy; 118uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_KEY: t_Array u8 (sz 3) =
  let list = [107uy; 101uy; 121uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_RES_BINDER: t_Array u8 (sz 10) =
  let list = [114uy; 101uy; 115uy; 32uy; 98uy; 105uy; 110uy; 100uy; 101uy; 114uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_RES_MASTER: t_Array u8 (sz 10) =
  let list = [114uy; 101uy; 115uy; 32uy; 109uy; 97uy; 115uy; 116uy; 101uy; 114uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_S_AP_TRAFFIC: t_Array u8 (sz 12) =
  let list = [115uy; 32uy; 97uy; 112uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_S_HS_TRAFFIC: t_Array u8 (sz 12) =
  let list = [115uy; 32uy; 104uy; 115uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_TLS13: t_Array u8 (sz 6) =
  let list = [116uy; 108uy; 115uy; 49uy; 51uy; 32uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 6);
  Rust_primitives.Hax.array_of_list list

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
  Rust_primitives.Hax.array_of_list list

let application_data_instead_of_handshake (_: Prims.unit) : Core.Result.t_Result Prims.unit u8 =
  Core.Result.Result_Err Bertie.Tls13utils.v_APPLICATION_DATA_INSTEAD_OF_HANDSHAKE
  <:
  Core.Result.t_Result Prims.unit u8

let invalid_compression_list (_: Prims.unit) : Core.Result.t_Result Prims.unit u8 =
  Core.Result.Result_Err Bertie.Tls13utils.v_INVALID_COMPRESSION_LIST
  <:
  Core.Result.t_Result Prims.unit u8

let protocol_version_alert (_: Prims.unit) : Core.Result.t_Result Prims.unit u8 =
  Core.Result.Result_Err Bertie.Tls13utils.v_PROTOCOL_VERSION_ALERT
  <:
  Core.Result.t_Result Prims.unit u8

let check_r_len (rlen: usize) : Core.Result.t_Result Prims.unit u8 =
  if rlen <. sz 32 || rlen >. sz 33
  then
    Core.Result.Result_Err Bertie.Tls13utils.v_INVALID_SIGNATURE
    <:
    Core.Result.t_Result Prims.unit u8
  else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_TryFrom t_AlertLevel u8 =
  {
    f_Error = u8;
    f_try_from
    =
    fun (value: u8) ->
      match value with
      | 1uy ->
        Core.Result.Result_Ok (AlertLevel_Warning <: t_AlertLevel)
        <:
        Core.Result.t_Result t_AlertLevel u8
      | 2uy ->
        Core.Result.Result_Ok (AlertLevel_Fatal <: t_AlertLevel)
        <:
        Core.Result.t_Result t_AlertLevel u8
      | _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_TryFrom t_AlertDescription u8 =
  {
    f_Error = u8;
    f_try_from
    =
    fun (value: u8) ->
      match value with
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
      | _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
  }

let impl__ContentType__try_from_u8 (t: u8) : Core.Result.t_Result t_ContentType u8 =
  match t with
  | 20uy ->
    Core.Result.Result_Ok (ContentType_ChangeCipherSpec <: t_ContentType)
    <:
    Core.Result.t_Result t_ContentType u8
  | 21uy ->
    Core.Result.Result_Ok (ContentType_Alert <: t_ContentType)
    <:
    Core.Result.t_Result t_ContentType u8
  | 22uy ->
    Core.Result.Result_Ok (ContentType_Handshake <: t_ContentType)
    <:
    Core.Result.t_Result t_ContentType u8
  | 23uy ->
    Core.Result.Result_Ok (ContentType_ApplicationData <: t_ContentType)
    <:
    Core.Result.t_Result t_ContentType u8
  | _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)

let invalid_compression_method_alert (_: Prims.unit) : Core.Result.t_Result Prims.unit u8 =
  Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_DECODE_ERROR

let merge_opts
      (#v_T: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Marker.t_Sized v_T)
      (o1 o2: Core.Option.t_Option v_T)
    : Core.Result.t_Result (Core.Option.t_Option v_T) u8 =
  match o1, o2 <: (Core.Option.t_Option v_T & Core.Option.t_Option v_T) with
  | Core.Option.Option_None , Core.Option.Option_Some o ->
    Core.Result.Result_Ok (Core.Option.Option_Some o <: Core.Option.t_Option v_T)
    <:
    Core.Result.t_Result (Core.Option.t_Option v_T) u8
  | Core.Option.Option_Some o, Core.Option.Option_None  ->
    Core.Result.Result_Ok (Core.Option.Option_Some o <: Core.Option.t_Option v_T)
    <:
    Core.Result.t_Result (Core.Option.t_Option v_T) u8
  | Core.Option.Option_None , Core.Option.Option_None  ->
    Core.Result.Result_Ok (Core.Option.Option_None <: Core.Option.t_Option v_T)
    <:
    Core.Result.t_Result (Core.Option.t_Option v_T) u8
  | _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)

let unsupported_cipher_alert (_: Prims.unit) : Core.Result.t_Result Prims.unit u8 =
  Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let build_server_name__PREFIX1: t_Array Bertie.Tls13utils.t_U8 (sz 2) =
  let list =
    [
      Bertie.Tls13utils.U8 0uy <: Bertie.Tls13utils.t_U8;
      Bertie.Tls13utils.U8 0uy <: Bertie.Tls13utils.t_U8
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list list

let build_server_name__PREFIX2: t_Array Bertie.Tls13utils.t_U8 (sz 1) =
  let list = [Bertie.Tls13utils.U8 0uy <: Bertie.Tls13utils.t_U8] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
  Rust_primitives.Hax.array_of_list list

let key_shares__PREFIX: t_Array Bertie.Tls13utils.t_U8 (sz 2) =
  let list =
    [
      Bertie.Tls13utils.U8 0uy <: Bertie.Tls13utils.t_U8;
      Bertie.Tls13utils.U8 51uy <: Bertie.Tls13utils.t_U8
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list list

let psk_key_exchange_modes__PSK_MODE_PREFIX: t_Array Bertie.Tls13utils.t_U8 (sz 2) =
  let list =
    [
      Bertie.Tls13utils.U8 0uy <: Bertie.Tls13utils.t_U8;
      Bertie.Tls13utils.U8 45uy <: Bertie.Tls13utils.t_U8
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list list

let server_supported_version__SUPPORTED_VERSION_PREFIX: t_Array Bertie.Tls13utils.t_U8 (sz 2) =
  let list =
    [
      Bertie.Tls13utils.U8 0uy <: Bertie.Tls13utils.t_U8;
      Bertie.Tls13utils.U8 43uy <: Bertie.Tls13utils.t_U8
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list list

let supported_groups__SUPPORTED_GROUPS_PREFIX: t_Array Bertie.Tls13utils.t_U8 (sz 2) =
  let list =
    [
      Bertie.Tls13utils.U8 0uy <: Bertie.Tls13utils.t_U8;
      Bertie.Tls13utils.U8 10uy <: Bertie.Tls13utils.t_U8
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list list

let check_server_psk_shared_key
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (b: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result Prims.unit u8 =
  Bertie.Tls13utils.check_eq_slice (Rust_primitives.unsize (let list =
            [
              Bertie.Tls13utils.U8 0uy <: Bertie.Tls13utils.t_U8;
              Bertie.Tls13utils.U8 0uy <: Bertie.Tls13utils.t_U8
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list list)
      <:
      t_Slice Bertie.Tls13utils.t_U8)
    b

let check_server_supported_version
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (b: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result Prims.unit u8 =
  Bertie.Tls13utils.check_eq_slice (Rust_primitives.unsize (let list =
            [
              Bertie.Tls13utils.U8 3uy <: Bertie.Tls13utils.t_U8;
              Bertie.Tls13utils.U8 4uy <: Bertie.Tls13utils.t_U8
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list list)
      <:
      t_Slice Bertie.Tls13utils.t_U8)
    b

let check_psk_key_exchange_modes (client_hello: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u8_slice client_hello
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist13:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist13)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13utils.check_eq_slice (Rust_primitives.unsize (let list =
                  [Bertie.Tls13utils.U8 1uy <: Bertie.Tls13utils.t_U8]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list list)
            <:
            t_Slice Bertie.Tls13utils.t_U8)
          (client_hello.[ { Core.Ops.Range.f_start = sz 1; Core.Ops.Range.f_end = sz 2 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice Bertie.Tls13utils.t_U8))
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

let check_psk_shared_key
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len_id:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u16_encoded ch
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist14:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist14)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) usize
      in
      let* len_tkt:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u16_encoded (ch.[ {
                      Core.Ops.Range.f_start = sz 2;
                      Core.Ops.Range.f_end = sz 2 +! len_id <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist15:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist15)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) usize
      in
      if len_id =. (len_tkt +! sz 6 <: usize)
      then
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u16_slice (ch.[ {
                        Core.Ops.Range.f_start = sz 2 +! len_id <: usize;
                        Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist16:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Prims.unit u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist16)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u8_slice (ch.[ {
                        Core.Ops.Range.f_start = sz 4 +! len_id <: usize;
                        Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist17:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Prims.unit u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist17)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (if (((Core.Slice.impl__len ch <: usize) -! sz 6 <: usize) -! len_id <: usize) <>. sz 32
          then Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
          else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
          (Core.Result.t_Result Prims.unit u8)
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8))
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
          (Core.Result.t_Result Prims.unit u8))

let check_supported_versions (client_hello: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u8_slice client_hello
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist18:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist18)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13utils.check_mem (Rust_primitives.unsize (let list =
                  [
                    Bertie.Tls13utils.U8 3uy <: Bertie.Tls13utils.t_U8;
                    Bertie.Tls13utils.U8 4uy <: Bertie.Tls13utils.t_U8
                  ]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list list)
            <:
            t_Slice Bertie.Tls13utils.t_U8)
          (client_hello.[ {
                Core.Ops.Range.f_start = sz 1;
                Core.Ops.Range.f_end = Core.Slice.impl__len client_hello <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice Bertie.Tls13utils.t_U8))
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

let check_server_name (extension: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u16_slice extension
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist34:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist34)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq_slice (Rust_primitives.unsize (let
                      list =
                        [Bertie.Tls13utils.U8 0uy <: Bertie.Tls13utils.t_U8]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list list)
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
                (extension.[ { Core.Ops.Range.f_start = sz 2; Core.Ops.Range.f_end = sz 3 }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist35:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist35)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u16_slice (extension.[
                    {
                      Core.Ops.Range.f_start = sz 3;
                      Core.Ops.Range.f_end = Core.Slice.impl__len extension <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist36:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist36)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (Core.Convert.f_into (extension.[ {
                  Core.Ops.Range.f_start = sz 5;
                  Core.Ops.Range.f_end = Core.Slice.impl__len extension <: usize
                }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice Bertie.Tls13utils.t_U8))
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let check_server_key_share
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (b: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist42:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist41:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist41)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist43:t_Slice Bertie.Tls13utils.t_U8 = Bertie.Tls13utils.impl__Bytes__as_raw hoist42 in
      let hoist44:Core.Result.t_Result Prims.unit u8 =
        Bertie.Tls13utils.check_eq_slice hoist43
          (b.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice Bertie.Tls13utils.t_U8)
      in
      let hoist45:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Prims.unit =
        Core.Ops.Try_trait.f_branch hoist44
      in
      let* _:Prims.unit =
        match hoist45 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist40:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist40)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u16_slice (b.[ {
                      Core.Ops.Range.f_start = sz 2;
                      Core.Ops.Range.f_end = Core.Slice.impl__len b <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist46:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist46)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (Core.Convert.f_from (b.[ {
                  Core.Ops.Range.f_start = sz 4;
                  Core.Ops.Range.f_end = Core.Slice.impl__len b <: usize
                }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice Bertie.Tls13utils.t_U8))
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let check_server_extension
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (b: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let l0:usize =
        cast (Bertie.Tls13utils.impl__U8__declassify (b.[ sz 0 ] <: Bertie.Tls13utils.t_U8) <: u8)
        <:
        usize
      in
      let l1:usize =
        cast (Bertie.Tls13utils.impl__U8__declassify (b.[ sz 1 ] <: Bertie.Tls13utils.t_U8) <: u8)
        <:
        usize
      in
      let* len:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u16_encoded (b.[ {
                      Core.Ops.Range.f_start = sz 2;
                      Core.Ops.Range.f_end = Core.Slice.impl__len b <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist47:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist47)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8) usize
      in
      let out:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
      in
      let* out:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match (cast (l0 <: usize) <: u8), (cast (l1 <: usize) <: u8) <: (u8 & u8) with
        | 0uy, 43uy ->
          (match
              Core.Ops.Try_trait.f_branch (check_server_supported_version algs
                    (b.[ {
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize ]
                      <:
                      t_Slice Bertie.Tls13utils.t_U8)
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist48:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
                  )
              in
              Core.Ops.Control_flow.ControlFlow_Continue out
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
                (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue out
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
                (Core.Option.t_Option Bertie.Tls13utils.t_Bytes))
        | 0uy, 51uy ->
          let* gx:Bertie.Tls13utils.t_Bytes =
            match
              Core.Ops.Try_trait.f_branch (check_server_key_share algs
                    (b.[ {
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize ]
                      <:
                      t_Slice Bertie.Tls13utils.t_U8)
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist49:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
                  )
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist49)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
                Bertie.Tls13utils.t_Bytes
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
                Bertie.Tls13utils.t_Bytes
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (Core.Option.Option_Some gx <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | 0uy, 41uy ->
          (match
              Core.Ops.Try_trait.f_branch (check_server_psk_shared_key algs
                    (b.[ {
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize ]
                      <:
                      t_Slice Bertie.Tls13utils.t_U8)
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist50:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
                  )
              in
              Core.Ops.Control_flow.ControlFlow_Continue out
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
                (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue out
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
                (Core.Option.t_Option Bertie.Tls13utils.t_Bytes))
        | _ ->
          Core.Ops.Control_flow.ControlFlow_Continue out
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (sz 4 +! len, out <: (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes))
        <:
        Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8))

let check_signature_algorithms
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u16_slice ch
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist51:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist51)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      let* hoist53:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist52:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist52)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist54:t_Slice Bertie.Tls13utils.t_U8 = Bertie.Tls13utils.impl__Bytes__as_raw hoist53 in
        Bertie.Tls13utils.check_mem hoist54
          (ch.[ {
                Core.Ops.Range.f_start = sz 2;
                Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice Bertie.Tls13utils.t_U8))
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

let check_supported_groups
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u16_slice ch
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist55:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist55)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      let* hoist57:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist56:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist56)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist58:t_Slice Bertie.Tls13utils.t_U8 = Bertie.Tls13utils.impl__Bytes__as_raw hoist57 in
        Bertie.Tls13utils.check_mem hoist58
          (ch.[ {
                Core.Ops.Range.f_start = sz 2;
                Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice Bertie.Tls13utils.t_U8))
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

let parse_ecdsa_signature (sig: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.impl__Bytes__len sig <: usize) <. sz 4 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      else
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 48uy
                    <:
                    Bertie.Tls13utils.t_Bytes)
                  (Bertie.Tls13utils.impl__Bytes__slice_range sig
                      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist129:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist129)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Prims.unit
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u8 (Bertie.Tls13utils.impl__Bytes__slice_range
                      sig
                      ({
                          Core.Ops.Range.f_start = sz 1;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sig <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist130:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist130)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Prims.unit
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 2uy
                    <:
                    Bertie.Tls13utils.t_Bytes)
                  (Bertie.Tls13utils.impl__Bytes__slice_range sig
                      ({ Core.Ops.Range.f_start = sz 2; Core.Ops.Range.f_end = sz 3 }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist131:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist131)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Prims.unit
        in
        let* rlen:usize =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u8_encoded (sig.[ {
                        Core.Ops.Range.f_start = sz 3;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sig <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result usize u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist132:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist132)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              usize
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              usize
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_r_len rlen <: Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist133:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist133)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Prims.unit
        in
        let r:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__slice sig
            ((sz 4 +! rlen <: usize) -! sz 32 <: usize)
            (sz 32)
        in
        if
          (Bertie.Tls13utils.impl__Bytes__len sig <: usize) <.
          ((sz 6 +! rlen <: usize) +! sz 32 <: usize)
        then
          Core.Ops.Control_flow.ControlFlow_Continue
          (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_INVALID_SIGNATURE)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        else
          let* _:Prims.unit =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 2uy
                      <:
                      Bertie.Tls13utils.t_Bytes)
                    (Bertie.Tls13utils.impl__Bytes__slice_range sig
                        ({
                            Core.Ops.Range.f_start = sz 4 +! rlen <: usize;
                            Core.Ops.Range.f_end = sz 5 +! rlen <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize)
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist134:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist134)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Prims.unit
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Prims.unit
          in
          let* _:Prims.unit =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u8 (Bertie.Tls13utils.impl__Bytes__slice_range
                        sig
                        ({
                            Core.Ops.Range.f_start = sz 5 +! rlen <: usize;
                            Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sig <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize)
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist135:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist135)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Prims.unit
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Prims.unit
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let s:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__slice sig
                ((Bertie.Tls13utils.impl__Bytes__len sig <: usize) -! sz 32 <: usize)
                (sz 32)
            in
            Core.Result.Result_Ok (Bertie.Tls13utils.impl__Bytes__concat r s)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let build_server_name (name: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist139:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 (Core.Clone.f_clone name
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist138:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist138)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist140:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__prefix hoist139
          (Rust_primitives.unsize build_server_name__PREFIX2 <: t_Slice Bertie.Tls13utils.t_U8)
      in
      let hoist141:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist140
      in
      let hoist142:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist141
      in
      let* hoist143:Bertie.Tls13utils.t_Bytes =
        match hoist142 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist137:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist137)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist144:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist143
      in
      let hoist145:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist144
      in
      let* hoist146:Bertie.Tls13utils.t_Bytes =
        match hoist145 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist136:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist136)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist147:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__prefix hoist146
            (Rust_primitives.unsize build_server_name__PREFIX1 <: t_Slice Bertie.Tls13utils.t_U8)
        in
        Core.Result.Result_Ok hoist147 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist151:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist148:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist148)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* hoist150:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 gx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist149:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist149)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let ks:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat hoist151 hoist150 in
      let* hoist154:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 ks
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist153:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist153)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist155:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist154
      in
      let hoist156:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist155
      in
      let* hoist157:Bertie.Tls13utils.t_Bytes =
        match hoist156 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist152:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist152)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist158:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__prefix hoist157
            (Rust_primitives.unsize key_shares__PREFIX <: t_Slice Bertie.Tls13utils.t_U8)
        in
        Core.Result.Result_Ok hoist158 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let server_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist162:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist159:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist159)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* hoist161:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 gx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist160:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist160)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let ks:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat hoist162 hoist161 in
      let* hoist164:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 ks
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist163:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist163)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist165:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 51uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist164
        in
        Core.Result.Result_Ok hoist165 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let server_pre_shared_key (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist167:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.bytes2
                    0uy
                    0uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist166:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist166)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist168:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 41uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist167
        in
        Core.Result.Result_Ok hoist168 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let server_supported_version (v__algorithms: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist170:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.bytes2
                    3uy
                    4uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist169:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist169)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist171:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__prefix hoist170
            (Rust_primitives.unsize server_supported_version__SUPPORTED_VERSION_PREFIX
              <:
              t_Slice Bertie.Tls13utils.t_U8)
        in
        Core.Result.Result_Ok hoist171 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist175:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist174:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist174)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist176:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist175
      in
      let hoist177:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist176
      in
      let* hoist178:Bertie.Tls13utils.t_Bytes =
        match hoist177 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist173:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist173)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist179:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist178
      in
      let hoist180:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist179
      in
      let* hoist181:Bertie.Tls13utils.t_Bytes =
        match hoist180 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist172:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist172)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist182:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 13uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist181
        in
        Core.Result.Result_Ok hoist182 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let supported_groups (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist186:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist185:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist185)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist187:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist186
      in
      let hoist188:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist187
      in
      let* hoist189:Bertie.Tls13utils.t_Bytes =
        match hoist188 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist184:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist184)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist190:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist189
      in
      let hoist191:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist190
      in
      let* hoist192:Bertie.Tls13utils.t_Bytes =
        match hoist191 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist183:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist183)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist193:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__prefix hoist192
            (Rust_primitives.unsize supported_groups__SUPPORTED_GROUPS_PREFIX
              <:
              t_Slice Bertie.Tls13utils.t_U8)
        in
        Core.Result.Result_Ok hoist193 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let ecdsa_signature (sv: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.impl__Bytes__len sv <: usize) <>. sz 64 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      else
        let b0:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 0uy in
        let b1:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 48uy in
        let b2:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 2uy in
        let (r: Bertie.Tls13utils.t_Bytes):Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__slice sv (sz 0) (sz 32)
        in
        let (s: Bertie.Tls13utils.t_Bytes):Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__slice sv (sz 32) (sz 32)
        in
        let r:Bertie.Tls13utils.t_Bytes =
          if
            (Bertie.Tls13utils.impl__U8__declassify (r.[ sz 0 ] <: Bertie.Tls13utils.t_U8) <: u8) >=.
            128uy
          then
            let r:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__concat (Core.Clone.f_clone b0
                  <:
                  Bertie.Tls13utils.t_Bytes)
                r
            in
            r
          else r
        in
        let s:Bertie.Tls13utils.t_Bytes =
          if
            (Bertie.Tls13utils.impl__U8__declassify (s.[ sz 0 ] <: Bertie.Tls13utils.t_U8) <: u8) >=.
            128uy
          then
            let s:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat b0 s in
            s
          else s
        in
        let* hoist196:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw
                      r
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist195:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist195)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
        in
        let hoist197:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Core.Clone.f_clone b2 <: Bertie.Tls13utils.t_Bytes)
            hoist196
        in
        let hoist200:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat hoist197 b2
        in
        let* hoist199:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw
                      s
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist198:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist198)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
        in
        let hoist201:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat hoist200 hoist199
        in
        let hoist202:t_Slice Bertie.Tls13utils.t_U8 =
          Bertie.Tls13utils.impl__Bytes__as_raw hoist201
        in
        let hoist203:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
          Bertie.Tls13utils.encode_length_u8 hoist202
        in
        let hoist204:Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
          Core.Ops.Try_trait.f_branch hoist203
        in
        let* hoist205:Bertie.Tls13utils.t_Bytes =
          match hoist204 with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist194:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist194)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let hoist206:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__concat b1 hoist205
          in
          Core.Result.Result_Ok hoist206 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let pre_shared_key
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (session_ticket: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist209:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 (Core.Clone.f_clone session_ticket

                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist208:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist208)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
      in
      let hoist210:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat_array (sz 4)
          hoist209
          (Bertie.Tls13utils.u32_as_be_bytes (Bertie.Tls13utils.U32 4294967295ul
                <:
                Bertie.Tls13utils.t_U32)
            <:
            t_Array Bertie.Tls13utils.t_U8 (sz 4))
      in
      let hoist211:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist210
      in
      let hoist212:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist211
      in
      let* identities:Bertie.Tls13utils.t_Bytes =
        match hoist212 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist207:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist207)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
      in
      let* hoist215:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw
                    (Bertie.Tls13crypto.zero_key (Bertie.Tls13crypto.impl__Algorithms__hash algs
                          <:
                          Bertie.Tls13crypto.t_HashAlgorithm)
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist214:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist214)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
      in
      let hoist216:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist215
      in
      let hoist217:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist216
      in
      let* binders:Bertie.Tls13utils.t_Bytes =
        match hoist217 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist213:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist213)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
      in
      let binders_len:usize = Bertie.Tls13utils.impl__Bytes__len binders in
      let* hoist219:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl__Bytes__concat
                    identities
                    binders
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist218:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist218)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let ext:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 41uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist219
        in
        Core.Result.Result_Ok (ext, binders_len <: (Bertie.Tls13utils.t_Bytes & usize))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8))

let psk_key_exchange_modes (_: Prims.unit) : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist222:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u8 (Rust_primitives.unsize (let
                      list =
                        [Bertie.Tls13utils.U8 1uy <: Bertie.Tls13utils.t_U8]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list list)
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist221:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist221)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist223:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist222
      in
      let hoist224:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist223
      in
      let* hoist225:Bertie.Tls13utils.t_Bytes =
        match hoist224 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist220:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist220)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist226:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__prefix hoist225
            (Rust_primitives.unsize psk_key_exchange_modes__PSK_MODE_PREFIX
              <:
              t_Slice Bertie.Tls13utils.t_U8)
        in
        Core.Result.Result_Ok hoist226 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let supported_versions (_: Prims.unit) : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist229:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u8 (Rust_primitives.unsize (let
                      list =
                        [
                          Bertie.Tls13utils.U8 3uy <: Bertie.Tls13utils.t_U8;
                          Bertie.Tls13utils.U8 4uy <: Bertie.Tls13utils.t_U8
                        ]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                      Rust_primitives.Hax.array_of_list list)
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist228:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist228)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist230:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist229
      in
      let hoist231:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist230
      in
      let* hoist232:Bertie.Tls13utils.t_Bytes =
        match hoist231 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist227:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist227)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist233:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Core.Convert.f_from (let list = [0uy; 43uy] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                  Rust_primitives.Hax.array_of_list list)
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist232
        in
        Core.Result.Result_Ok hoist233 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

type t_Extensions = {
  f_sni:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_key_share:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_ticket:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_binder:Core.Option.t_Option Bertie.Tls13utils.t_Bytes
}

let impl__Extensions__merge (self e2: t_Extensions) : Core.Result.t_Result t_Extensions u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist294:Core.Option.t_Option
      Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts self.f_sni e2.f_sni
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist287:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_Extensions u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist287)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      let* hoist293:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts self.f_key_share e2.f_key_share
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist288:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_Extensions u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist288)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      let* hoist292:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts self.f_ticket e2.f_ticket
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist289:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_Extensions u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist289)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      let* hoist291:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts self.f_binder e2.f_binder
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist290:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_Extensions u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist290)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist295:t_Extensions =
          { f_sni = hoist294; f_key_share = hoist293; f_ticket = hoist292; f_binder = hoist291 }
          <:
          t_Extensions
        in
        Core.Result.Result_Ok hoist295 <: Core.Result.t_Result t_Extensions u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
        (Core.Result.t_Result t_Extensions u8))

let certificate_verify (algs: Bertie.Tls13crypto.t_Algorithms) (cv: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* sv:Bertie.Tls13utils.t_Bytes =
        match algs.Bertie.Tls13crypto.f_signature with
        | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
          Core.Ops.Control_flow.ControlFlow_Continue (Core.Clone.f_clone cv)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
          if (Bertie.Tls13utils.impl__Bytes__len cv <: usize) <>. sz 64
          then
            let* hoist310:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed
                        ()
                      <:
                      u8)
                  <:
                  Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist310)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
              Bertie.Tls13utils.t_Bytes
          else
            (match
                Core.Ops.Try_trait.f_branch (ecdsa_signature cv
                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              with
              | Core.Ops.Control_flow.ControlFlow_Break residual ->
                let* hoist311:Rust_primitives.Hax.t_Never =
                  Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                      <:
                      Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
                in
                Core.Ops.Control_flow.ControlFlow_Continue
                (Rust_primitives.Hax.never_to_any hoist311)
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
                  Bertie.Tls13utils.t_Bytes
              | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                Core.Ops.Control_flow.ControlFlow_Continue v_val
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
                  Bertie.Tls13utils.t_Bytes)
        | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
                <:
                Rust_primitives.Hax.t_Never))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* hoist315:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist312:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist312)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* hoist314:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 sv
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist313:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist313)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let sig:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat hoist315 hoist314
        in
        Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_CertificateVerify
            <:
            Bertie.Tls13formats.Handshake_data.t_HandshakeType)
          sig)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8))

let check_handshake_record (p: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.impl__Bytes__len p <: usize) <. sz 5 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
          <:
          Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
          (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
      else
        let ty:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.bytes1 (cast (Bertie.Tls13formats.ContentType.Handshake.anon_const +!
                  0uy
                  <:
                  u8)
              <:
              u8)
        in
        let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
        let* _:Prims.unit =
          match
            Bertie.Tls13utils.check_eq ty
              (Bertie.Tls13utils.impl__Bytes__slice_range p
                  ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Bertie.Tls13utils.t_Bytes)
          with
          | Core.Result.Result_Ok _ ->
            Core.Ops.Control_flow.ControlFlow_Continue (() <: Prims.unit)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
              Prims.unit
          | Core.Result.Result_Err _ ->
            match
              Core.Ops.Try_trait.f_branch (application_data_instead_of_handshake ()
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist316:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist316)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
                    u8) Prims.unit
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
                    u8) Prims.unit
        in
        let* _:Prims.unit =
          match
            Bertie.Tls13utils.check_eq ver
              (Bertie.Tls13utils.impl__Bytes__slice_range p
                  ({ Core.Ops.Range.f_start = sz 1; Core.Ops.Range.f_end = sz 3 }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Bertie.Tls13utils.t_Bytes)
          with
          | Core.Result.Result_Ok _ ->
            Core.Ops.Control_flow.ControlFlow_Continue (() <: Prims.unit)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
              Prims.unit
          | Core.Result.Result_Err _ ->
            match
              Core.Ops.Try_trait.f_branch (protocol_version_alert ()
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist317:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist317)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
                    u8) Prims.unit
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
                    u8) Prims.unit
        in
        let* len:usize =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u16_encoded (p.[ {
                        Core.Ops.Range.f_start = sz 3;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len p <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result usize u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist318:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
                    u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist318)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
              usize
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
              usize
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok
          ((Bertie.Tls13formats.Handshake_data.HandshakeData
              (Bertie.Tls13utils.impl__Bytes__slice_range p
                  ({ Core.Ops.Range.f_start = sz 5; Core.Ops.Range.f_end = sz 5 +! len <: usize }
                    <:
                    Core.Ops.Range.t_Range usize))
              <:
              Bertie.Tls13formats.Handshake_data.t_HandshakeData),
            sz 5 +! len
            <:
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize))
          <:
          Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
          (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8))

let check_server_extensions
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (b: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len, out:(usize &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (check_server_extension algs b
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist319:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist319)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
            (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
            (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      if len =. (Core.Slice.impl__len b <: usize)
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok out
          <:
          Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
      else
        let* out_rest:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (check_server_extensions algs
                  (b.[ {
                        Core.Ops.Range.f_start = len;
                        Core.Ops.Range.f_end = Core.Slice.impl__len b <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist320:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist320)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
              (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
              (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        in
        Core.Ops.Control_flow.ControlFlow_Continue (merge_opts out out_rest)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8))

let client_hello
      (algorithms: Bertie.Tls13crypto.t_Algorithms)
      (client_random kem_pk server_name: Bertie.Tls13utils.t_Bytes)
      (session_ticket: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let version:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes2 3uy 3uy
      in
      let compression_methods:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 1uy 0uy in
      let* legacy_session_id:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u8 (Rust_primitives.unsize (Rust_primitives.Hax.repeat
                        (Bertie.Tls13utils.U8 0uy <: Bertie.Tls13utils.t_U8)
                        (sz 32)
                      <:
                      t_Array Bertie.Tls13utils.t_U8 (sz 32))
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist321:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist321)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* hoist324:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__ciphersuite algorithms
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist323:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist323)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist325:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist324
      in
      let hoist326:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist325
      in
      let* cipher_suites:Bertie.Tls13utils.t_Bytes =
        match hoist326 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist322:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist322)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* server_name:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (build_server_name server_name
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist327:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist327)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* supported_versions:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_versions ()
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist328:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist328)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* supported_groups:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_groups algorithms
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist329:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist329)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* signature_algorithms:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (signature_algorithms algorithms
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist330:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist330)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* key_shares:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (key_shares algorithms
                (Core.Clone.f_clone kem_pk <: Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist331:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist331)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let len:usize =
        (Bertie.Tls13utils.impl__Bytes__len server_name <: usize) +!
        (Bertie.Tls13utils.impl__Bytes__len supported_versions <: usize)
      in
      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len supported_groups <: usize) in
      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len signature_algorithms <: usize) in
      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len key_shares <: usize) in
      let out:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__new_alloc len in
      let out:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__append out server_name in
      let out:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__append out supported_versions
      in
      let out:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__append out supported_groups
      in
      let out:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__append out signature_algorithms
      in
      let out:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__append out key_shares in
      let extensions:Bertie.Tls13utils.t_Bytes = out in
      let trunc_len:usize = sz 0 in
      let* extensions, trunc_len:(Bertie.Tls13utils.t_Bytes & usize) =
        match
          Bertie.Tls13crypto.impl__Algorithms__psk_mode algorithms, session_ticket
          <:
          (bool & Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        with
        | true, Core.Option.Option_Some session_ticket ->
          let* pskm:Bertie.Tls13utils.t_Bytes =
            match
              Core.Ops.Try_trait.f_branch (psk_key_exchange_modes ()
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist332:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist332)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
                    u8) Bertie.Tls13utils.t_Bytes
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
                    u8) Bertie.Tls13utils.t_Bytes
          in
          let* psk, len:(Bertie.Tls13utils.t_Bytes & usize) =
            match
              Core.Ops.Try_trait.f_branch (pre_shared_key algorithms session_ticket
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist333:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist333)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
                    u8) (Bertie.Tls13utils.t_Bytes & usize)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
                    u8) (Bertie.Tls13utils.t_Bytes & usize)
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let extensions:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat extensions
                    pskm
                  <:
                  Bertie.Tls13utils.t_Bytes)
                psk
            in
            let trunc_len:usize = len in
            extensions, trunc_len <: (Bertie.Tls13utils.t_Bytes & usize))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            (Bertie.Tls13utils.t_Bytes & usize)
        | false, Core.Option.Option_None  ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (extensions, trunc_len <: (Bertie.Tls13utils.t_Bytes & usize))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            (Bertie.Tls13utils.t_Bytes & usize)
        | _ ->
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_PSK_MODE_MISMATCH

                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist334:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
                    u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue
            (extensions, trunc_len <: (Bertie.Tls13utils.t_Bytes & usize))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
              (Bertie.Tls13utils.t_Bytes & usize)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue
            (extensions, trunc_len <: (Bertie.Tls13utils.t_Bytes & usize))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
              (Bertie.Tls13utils.t_Bytes & usize)
      in
      let* encoded_extensions:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 extensions
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist335:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist335)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let len:usize =
        (Bertie.Tls13utils.impl__Bytes__len version <: usize) +!
        (Bertie.Tls13utils.impl__Bytes__len client_random <: usize)
      in
      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len legacy_session_id <: usize) in
      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len cipher_suites <: usize) in
      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len compression_methods <: usize) in
      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len encoded_extensions <: usize) in
      let out:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__new_alloc len in
      let out:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__append out version in
      let out:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__append out client_random in
      let out:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__append out legacy_session_id
      in
      let out:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__append out cipher_suites in
      let out:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__append out compression_methods
      in
      let out:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__append out encoded_extensions
      in
      let handshake_bytes:Bertie.Tls13utils.t_Bytes = out in
      let* client_hello:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes
                (Bertie.Tls13formats.Handshake_data.HandshakeType_ClientHello
                  <:
                  Bertie.Tls13formats.Handshake_data.t_HandshakeType)
                handshake_bytes
              <:
              Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist336:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist336)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (client_hello, trunc_len <: (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize))
        <:
        Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
        (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8))

let encrypted_extensions (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let handshake_type:Bertie.Tls13utils.t_Bytes
      =
        Bertie.Tls13utils.bytes1 (cast (Bertie.Tls13formats.Handshake_data.HandshakeType.EncryptedExtensions.anon_const +!
                0uy
                <:
                u8)
            <:
            u8)
      in
      let* hoist339:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl__Bytes__new
                    ()
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist338:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist338)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist340:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u24 hoist339
      in
      let hoist341:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist340
      in
      let* hoist342:Bertie.Tls13utils.t_Bytes =
        match hoist341 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist337:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist337)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist343:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat handshake_type hoist342
        in
        let hoist344:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
          Bertie.Tls13formats.Handshake_data.HandshakeData hoist343
          <:
          Bertie.Tls13formats.Handshake_data.t_HandshakeData
        in
        Core.Result.Result_Ok hoist344
        <:
        Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8))

let find_key_share (g: Bertie.Tls13utils.t_Bytes) (ch: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Core.Slice.impl__len ch <: usize) <. sz 4 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      else
        if
          Bertie.Tls13utils.eq_slice (Bertie.Tls13utils.impl__Bytes__as_raw g
              <:
              t_Slice Bertie.Tls13utils.t_U8)
            (ch.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice Bertie.Tls13utils.t_U8)
          <:
          bool
        then
          let* len:usize =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u16_encoded_slice (ch.[ {
                          Core.Ops.Range.f_start = sz 2;
                          Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize ]
                      <:
                      t_Slice Bertie.Tls13utils.t_U8)
                  <:
                  Core.Result.t_Result usize u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist345:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist345)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) usize
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) usize
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (Core.Result.Result_Ok
            (Core.Convert.f_into (ch.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice Bertie.Tls13utils.t_U8))
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        else
          let* len:usize =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u16_encoded_slice (ch.[ {
                          Core.Ops.Range.f_start = sz 2;
                          Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize ]
                      <:
                      t_Slice Bertie.Tls13utils.t_U8)
                  <:
                  Core.Result.t_Result usize u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist346:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist346)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) usize
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) usize
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (find_key_share g
              (ch.[ {
                    Core.Ops.Range.f_start = sz 4 +! len <: usize;
                    Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice Bertie.Tls13utils.t_U8))
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let check_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u16_slice ch
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist347:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist347)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
      in
      let* hoist349:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist348:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist348)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (find_key_share hoist349
          (ch.[ {
                Core.Ops.Range.f_start = sz 2;
                Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice Bertie.Tls13utils.t_U8))
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let check_extension (algs: Bertie.Tls13crypto.t_Algorithms) (bytes: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result (usize & t_Extensions) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let l0:usize =
        cast (Bertie.Tls13utils.impl__U8__declassify (bytes.[ sz 0 ] <: Bertie.Tls13utils.t_U8)
            <:
            u8)
        <:
        usize
      in
      let l1:usize =
        cast (Bertie.Tls13utils.impl__U8__declassify (bytes.[ sz 1 ] <: Bertie.Tls13utils.t_U8)
            <:
            u8)
        <:
        usize
      in
      let* len:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u16_encoded_slice (bytes.[ {
                      Core.Ops.Range.f_start = sz 2;
                      Core.Ops.Range.f_end = Core.Slice.impl__len bytes <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist350:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (usize & t_Extensions) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist350)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8) usize
      in
      let out:t_Extensions =
        {
          f_sni = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
          f_key_share = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
          f_ticket = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
          f_binder = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
        }
        <:
        t_Extensions
      in
      match (cast (l0 <: usize) <: u8), (cast (l1 <: usize) <: u8) <: (u8 & u8) with
      | 0uy, 0uy ->
        let* hoist352:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (check_server_name (bytes.[ {
                        Core.Ops.Range.f_start = sz 4;
                        Core.Ops.Range.f_end = sz 4 +! len <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist351:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_Extensions) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist351)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
              Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
              Bertie.Tls13utils.t_Bytes
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let hoist353:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
            Core.Option.Option_Some hoist352 <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
          in
          let hoist354:t_Extensions =
            {
              f_sni = hoist353;
              f_key_share
              =
              Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
              f_ticket = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
              f_binder = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
            }
            <:
            t_Extensions
          in
          let hoist355:(usize & t_Extensions) = sz 4 +! len, hoist354 <: (usize & t_Extensions) in
          Core.Result.Result_Ok hoist355 <: Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
          (Core.Result.t_Result (usize & t_Extensions) u8)
      | 0uy, 45uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_psk_key_exchange_modes (bytes.[ {
                        Core.Ops.Range.f_start = sz 4;
                        Core.Ops.Range.f_end = sz 4 +! len <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist356:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_Extensions) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist356)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
              Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
          (Core.Result.t_Result (usize & t_Extensions) u8)
      | 0uy, 43uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_supported_versions (bytes.[ {
                        Core.Ops.Range.f_start = sz 4;
                        Core.Ops.Range.f_end = sz 4 +! len <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist357:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_Extensions) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist357)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
              Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
          (Core.Result.t_Result (usize & t_Extensions) u8)
      | 0uy, 10uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_supported_groups algs
                  (bytes.[ {
                        Core.Ops.Range.f_start = sz 4;
                        Core.Ops.Range.f_end = sz 4 +! len <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist358:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_Extensions) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist358)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
              Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
          (Core.Result.t_Result (usize & t_Extensions) u8)
      | 0uy, 13uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_signature_algorithms algs
                  (bytes.[ {
                        Core.Ops.Range.f_start = sz 4;
                        Core.Ops.Range.f_end = sz 4 +! len <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist359:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_Extensions) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist359)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
              Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
          (Core.Result.t_Result (usize & t_Extensions) u8)
      | 0uy, 51uy ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (match
            check_key_shares algs
              (bytes.[ {
                    Core.Ops.Range.f_start = sz 4;
                    Core.Ops.Range.f_end = sz 4 +! len <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice Bertie.Tls13utils.t_U8)
          with
          | Core.Result.Result_Ok gx ->
            Core.Result.Result_Ok
            (sz 4 +! len,
              ({
                  f_sni = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
                  f_key_share
                  =
                  Core.Option.Option_Some gx <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
                  f_ticket
                  =
                  Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
                  f_binder
                  =
                  Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
                }
                <:
                t_Extensions)
              <:
              (usize & t_Extensions))
            <:
            Core.Result.t_Result (usize & t_Extensions) u8
          | Core.Result.Result_Err _ ->
            Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_MISSING_KEY_SHARE)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
          (Core.Result.t_Result (usize & t_Extensions) u8)
      | 0uy, 41uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_psk_shared_key algs
                  (bytes.[ {
                        Core.Ops.Range.f_start = sz 4;
                        Core.Ops.Range.f_end = sz 4 +! len <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist360:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_Extensions) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist360)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
              Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
          (Core.Result.t_Result (usize & t_Extensions) u8)
      | _ ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
          (Core.Result.t_Result (usize & t_Extensions) u8))

let finished (vd: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
  Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_Finished
      <:
      Bertie.Tls13formats.Handshake_data.t_HandshakeType)
    vd

let get_handshake_record (p: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hd, len:(Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        usize) =
        match
          Core.Ops.Try_trait.f_branch (check_handshake_record p
              <:
              Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist361:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist361)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (if len =. (Bertie.Tls13utils.impl__Bytes__len p <: usize)
        then
          Core.Result.Result_Ok hd
          <:
          Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
        else Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8))

let handshake_record (p: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ty:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes1 (cast (Bertie.Tls13formats.ContentType.Handshake.anon_const +! 0uy
                <:
                u8)
            <:
            u8)
      in
      let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
      let* hoist363:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 p
                  .Bertie.Tls13formats.Handshake_data._0
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist362:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist362)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist364:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat ty ver
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist363
        in
        Core.Result.Result_Ok hoist364 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let parse_certificate_verify
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (certificate_verify: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let*
      Bertie.Tls13formats.Handshake_data.HandshakeData cv:Bertie.Tls13formats.Handshake_data.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message
                certificate_verify
                (Bertie.Tls13formats.Handshake_data.HandshakeType_CertificateVerify
                  <:
                  Bertie.Tls13formats.Handshake_data.t_HandshakeType)
              <:
              Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist365:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist365)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
      in
      let sa:Bertie.Tls13crypto.t_SignatureScheme =
        Bertie.Tls13crypto.impl__Algorithms__signature algs
      in
      let* hoist368:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist367:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist367)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist369:Core.Result.t_Result Prims.unit u8 =
        Bertie.Tls13utils.check_eq hoist368
          (Bertie.Tls13utils.impl__Bytes__slice_range cv
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Bertie.Tls13utils.t_Bytes)
      in
      let hoist370:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Prims.unit =
        Core.Ops.Try_trait.f_branch hoist369
      in
      let* _:Prims.unit =
        match hoist370 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist366:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist366)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u16 (Bertie.Tls13utils.impl__Bytes__slice_range
                    cv
                    ({
                        Core.Ops.Range.f_start = sz 2;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len cv <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist371:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist371)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (match sa with
        | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
          parse_ecdsa_signature (Bertie.Tls13utils.impl__Bytes__slice_range cv
                ({
                    Core.Ops.Range.f_start = sz 4;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len cv <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Bertie.Tls13utils.t_Bytes)
        | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
          Core.Result.Result_Ok
          (Bertie.Tls13utils.impl__Bytes__slice_range cv
              ({
                  Core.Ops.Range.f_start = sz 4;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len cv <: usize
                }
                <:
                Core.Ops.Range.t_Range usize))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
          if ((Bertie.Tls13utils.impl__Bytes__len cv <: usize) -! sz 4 <: usize) =. sz 64
          then
            Core.Result.Result_Ok
            (Bertie.Tls13utils.impl__Bytes__slice_range cv
                ({
                    Core.Ops.Range.f_start = sz 8;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len cv <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize))
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          else Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_INVALID_SIGNATURE)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let parse_encrypted_extensions
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (encrypted_extensions: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      Bertie.Tls13formats.Handshake_data.HandshakeData encrypted_extension_bytes:Bertie.Tls13formats.Handshake_data.t_HandshakeData
      =
        encrypted_extensions
      in
      let expected_handshake_type:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes1 (cast (Bertie.Tls13formats.Handshake_data.HandshakeType.EncryptedExtensions.anon_const +!
                0uy
                <:
                u8)
            <:
            u8)
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq expected_handshake_type
                (Bertie.Tls13utils.impl__Bytes__slice_range encrypted_extension_bytes
                    ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist372:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist372)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13utils.check_length_encoding_u24 (Bertie.Tls13utils.impl__Bytes__raw_slice encrypted_extension_bytes
              ({
                  Core.Ops.Range.f_start = sz 1;
                  Core.Ops.Range.f_end
                  =
                  Bertie.Tls13utils.impl__Bytes__len encrypted_extension_bytes <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            t_Slice Bertie.Tls13utils.t_U8))
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

let parse_finished (finished: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let*
      Bertie.Tls13formats.Handshake_data.HandshakeData fin:Bertie.Tls13formats.Handshake_data.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message
                finished
                (Bertie.Tls13formats.Handshake_data.HandshakeType_Finished
                  <:
                  Bertie.Tls13formats.Handshake_data.t_HandshakeType)
              <:
              Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist373:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist373)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok fin <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let parse_server_certificate (certificate: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let*
      Bertie.Tls13formats.Handshake_data.HandshakeData sc:Bertie.Tls13formats.Handshake_data.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message
                certificate
                (Bertie.Tls13formats.Handshake_data.HandshakeType_Certificate
                  <:
                  Bertie.Tls13formats.Handshake_data.t_HandshakeType)
              <:
              Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist374:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist374)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
      in
      let next:usize = sz 0 in
      let* creqlen:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u8_encoded (sc.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist375:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist375)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            usize
      in
      let next:usize = (next +! sz 1 <: usize) +! creqlen in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u24 (Bertie.Tls13utils.impl__Bytes__raw_slice
                    sc
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist376:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist376)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
      in
      let next:usize = next +! sz 3 in
      let* crtlen:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u24_encoded (Bertie.Tls13utils.impl__Bytes__raw_slice
                    sc
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist377:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist377)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            usize
      in
      let next:usize = next +! sz 3 in
      let crt:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range sc
          ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! crtlen <: usize }
            <:
            Core.Ops.Range.t_Range usize)
      in
      let next:usize = next +! crtlen in
      let* v__extlen:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u16_encoded (sc.[ {
                      Core.Ops.Range.f_start = next;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist378:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist378)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            usize
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok crt <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let parse_server_hello
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (server_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let*
      Bertie.Tls13formats.Handshake_data.HandshakeData server_hello:Bertie.Tls13formats.Handshake_data.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message
                server_hello
                (Bertie.Tls13formats.Handshake_data.HandshakeType_ServerHello
                  <:
                  Bertie.Tls13formats.Handshake_data.t_HandshakeType)
              <:
              Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist379:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist379)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
      in
      let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
      let* cip:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__ciphersuite algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist380:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist380)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 0uy in
      let next:usize = sz 0 in
      let* _:Prims.unit =
        match
          Bertie.Tls13utils.check_eq ver
            (Bertie.Tls13utils.impl__Bytes__slice_range server_hello
                ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 2 <: usize }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Bertie.Tls13utils.t_Bytes)
        with
        | Core.Result.Result_Ok _ ->
          Core.Ops.Control_flow.ControlFlow_Continue (() <: Prims.unit)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Prims.unit
        | Core.Result.Result_Err _ ->
          match
            Core.Ops.Try_trait.f_branch (protocol_version_alert ()
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist381:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist381)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
              Prims.unit
      in
      let next:usize = next +! sz 2 in
      let srand:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range server_hello
          ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 32 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
      in
      let next:usize = next +! sz 32 in
      let* sidlen:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u8_encoded (server_hello.[ {
                      Core.Ops.Range.f_start = next;
                      Core.Ops.Range.f_end
                      =
                      Bertie.Tls13utils.impl__Bytes__len server_hello <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist382:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist382)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8) usize
      in
      let next:usize = (next +! sz 1 <: usize) +! sidlen in
      let* _:Prims.unit =
        match
          Bertie.Tls13utils.check_eq cip
            (Bertie.Tls13utils.impl__Bytes__slice_range server_hello
                ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 2 <: usize }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Bertie.Tls13utils.t_Bytes)
        with
        | Core.Result.Result_Ok _ ->
          Core.Ops.Control_flow.ControlFlow_Continue (() <: Prims.unit)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Prims.unit
        | Core.Result.Result_Err _ ->
          match
            Core.Ops.Try_trait.f_branch (unsupported_cipher_alert ()
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist383:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist383)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
              Prims.unit
      in
      let next:usize = next +! sz 2 in
      let* _:Prims.unit =
        match
          Bertie.Tls13utils.check_eq comp
            (Bertie.Tls13utils.impl__Bytes__slice_range server_hello
                ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 1 <: usize }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Bertie.Tls13utils.t_Bytes)
        with
        | Core.Result.Result_Ok _ ->
          Core.Ops.Control_flow.ControlFlow_Continue (() <: Prims.unit)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Prims.unit
        | Core.Result.Result_Err _ ->
          match
            Core.Ops.Try_trait.f_branch (invalid_compression_method_alert ()
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist384:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist384)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
              Prims.unit
      in
      let next:usize = next +! sz 1 in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u16 (Bertie.Tls13utils.impl__Bytes__slice_range
                    server_hello
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end
                        =
                        Bertie.Tls13utils.impl__Bytes__len server_hello <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist385:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist385)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Prims.unit
      in
      let next:usize = next +! sz 2 in
      let* gy:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (check_server_extensions algs
                (server_hello.[ {
                      Core.Ops.Range.f_start = next;
                      Core.Ops.Range.f_end
                      =
                      Bertie.Tls13utils.impl__Bytes__len server_hello <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist386:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist386)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (match gy with
        | Core.Option.Option_Some gy ->
          Core.Result.Result_Ok
          (srand, gy <: (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8
        | _ ->
          Core.Result.Result_Err Bertie.Tls13utils.v_MISSING_KEY_SHARE
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8))

let server_certificate (v__algs: Bertie.Tls13crypto.t_Algorithms) (cert: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* creq:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u8 (Rust_primitives.unsize (let
                      list =
                        []
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 0);
                      Rust_primitives.Hax.array_of_list list)
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist387:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist387)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* crt:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u24 cert
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist388:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist388)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* ext:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl__Bytes__new
                    ()
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist389:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist389)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* crts:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u24 (Bertie.Tls13utils.impl__Bytes__concat
                    crt
                    ext
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist390:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist390)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_Certificate
            <:
            Bertie.Tls13formats.Handshake_data.t_HandshakeType)
          (Bertie.Tls13utils.impl__Bytes__concat creq crts <: Bertie.Tls13utils.t_Bytes))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8))

let server_hello (algs: Bertie.Tls13crypto.t_Algorithms) (sr sid gy: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ver:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes2 3uy 3uy
      in
      let* sid:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw
                    sid
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist391:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist391)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* cip:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__ciphersuite algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist392:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist392)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 0uy in
      let* ks:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (server_key_shares algs
                (Core.Clone.f_clone gy <: Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist393:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist393)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* sv:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (server_supported_version algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist394:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist394)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      let exts:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat ks sv in
      let* exts:Bertie.Tls13utils.t_Bytes =
        match Bertie.Tls13crypto.impl__Algorithms__psk_mode algs with
        | true ->
          let* hoist396:Bertie.Tls13utils.t_Bytes =
            match
              Core.Ops.Try_trait.f_branch (server_pre_shared_key algs
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist395:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist395)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
                Bertie.Tls13utils.t_Bytes
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
                Bertie.Tls13utils.t_Bytes
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist397:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__concat exts hoist396
            in
            hoist397)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | false ->
          Core.Ops.Control_flow.ControlFlow_Continue exts
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* encoded_extensions:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u16 exts
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist398:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist398)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      let len:usize =
        (Bertie.Tls13utils.impl__Bytes__len ver <: usize) +!
        (Bertie.Tls13utils.impl__Bytes__len sr <: usize)
      in
      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len sid <: usize) in
      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len cip <: usize) in
      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len comp <: usize) in
      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len encoded_extensions <: usize) in
      let out:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__new_alloc len in
      let out:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__append out ver in
      let out:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__append out sr in
      let out:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__append out sid in
      let out:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__append out cip in
      let out:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__append out comp in
      let out:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__append out encoded_extensions
      in
      let hoist400:Bertie.Tls13utils.t_Bytes = out in
      let hoist401:Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
        Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_ServerHello
            <:
            Bertie.Tls13formats.Handshake_data.t_HandshakeType)
          hoist400
      in
      let hoist402:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8)
        Bertie.Tls13formats.Handshake_data.t_HandshakeData =
        Core.Ops.Try_trait.f_branch hoist401
      in
      let* sh:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
        match hoist402 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist399:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist399)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok sh
        <:
        Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8))

let set_client_hello_binder
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (binder: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (client_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: Core.Option.t_Option usize)
    : Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
  let Bertie.Tls13formats.Handshake_data.HandshakeData ch:Bertie.Tls13formats.Handshake_data.t_HandshakeData
  =
    client_hello
  in
  let chlen:usize = Bertie.Tls13utils.impl__Bytes__len ch in
  let hlen:usize =
    Bertie.Tls13crypto.impl__HashAlgorithm__hash_len (Bertie.Tls13crypto.impl__Algorithms__hash ciphersuite

        <:
        Bertie.Tls13crypto.t_HashAlgorithm)
  in
  match
    binder, trunc_len
    <:
    (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & Core.Option.t_Option usize)
  with
  | Core.Option.Option_Some m, Core.Option.Option_Some trunc_len ->
    if (chlen -! hlen <: usize) =. trunc_len
    then
      Core.Result.Result_Ok
      (Bertie.Tls13formats.Handshake_data.HandshakeData
        (Bertie.Tls13utils.impl__Bytes__update_slice ch trunc_len m (sz 0) hlen)
        <:
        Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      <:
      Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
    else Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
  | Core.Option.Option_None , Core.Option.Option_None  ->
    Core.Result.Result_Ok
    (Bertie.Tls13formats.Handshake_data.HandshakeData ch
      <:
      Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  | _, _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)

type t_Transcript = {
  f_hash_algorithm:Bertie.Tls13crypto.t_HashAlgorithm;
  f_transcript:Bertie.Tls13formats.Handshake_data.t_HandshakeData
}

let impl__Transcript__add
      (self: t_Transcript)
      (msg: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : t_Transcript =
  let self:t_Transcript =
    {
      self with
      f_transcript
      =
      Bertie.Tls13formats.Handshake_data.impl__HandshakeData__concat self.f_transcript msg
    }
    <:
    t_Transcript
  in
  self

let impl__Transcript__new (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm) : t_Transcript =
  {
    f_hash_algorithm = hash_algorithm;
    f_transcript
    =
    Bertie.Tls13formats.Handshake_data.HandshakeData (Bertie.Tls13utils.impl__Bytes__new ())
    <:
    Bertie.Tls13formats.Handshake_data.t_HandshakeData
  }
  <:
  t_Transcript

let impl__Transcript__transcript_hash (self: t_Transcript)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__HashAlgorithm__hash self
                  .f_hash_algorithm
                self.f_transcript.Bertie.Tls13formats.Handshake_data._0
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist403:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist403)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok th <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let impl__Transcript__transcript_hash_without_client_hello
      (self: t_Transcript)
      (client_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: usize)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  let Bertie.Tls13formats.Handshake_data.HandshakeData ch:Bertie.Tls13formats.Handshake_data.t_HandshakeData
  =
    client_hello
  in
  Bertie.Tls13crypto.impl__HashAlgorithm__hash self.f_hash_algorithm
    (Bertie.Tls13utils.impl__Bytes__concat (Core.Clone.f_clone self.f_transcript
              .Bertie.Tls13formats.Handshake_data._0
          <:
          Bertie.Tls13utils.t_Bytes)
        (Bertie.Tls13utils.impl__Bytes__slice_range client_hello
              .Bertie.Tls13formats.Handshake_data._0
            ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = trunc_len }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Bertie.Tls13utils.t_Bytes)
      <:
      Bertie.Tls13utils.t_Bytes)

let check_extensions_slice
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (b: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result t_Extensions u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len, out:(usize & t_Extensions) =
        match
          Core.Ops.Try_trait.f_branch (check_extension algs b
              <:
              Core.Result.t_Result (usize & t_Extensions) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist404:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_Extensions u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist404)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (usize & t_Extensions)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (usize & t_Extensions)
      in
      if len =. (Core.Slice.impl__len b <: usize)
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok out <: Core.Result.t_Result t_Extensions u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
          (Core.Result.t_Result t_Extensions u8)
      else
        let* out_rest:t_Extensions =
          match
            Core.Ops.Try_trait.f_branch (check_extensions_slice algs
                  (b.[ {
                        Core.Ops.Range.f_start = len;
                        Core.Ops.Range.f_end = Core.Slice.impl__len b <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result t_Extensions u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist405:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_Extensions u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist405)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8) t_Extensions
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8) t_Extensions
        in
        Core.Ops.Control_flow.ControlFlow_Continue (impl__Extensions__merge out out_rest)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
          (Core.Result.t_Result t_Extensions u8))

let check_extensions (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result t_Extensions u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len, out:(usize & t_Extensions) =
        match
          Core.Ops.Try_trait.f_branch (check_extension algs
                (Bertie.Tls13utils.impl__Bytes__as_raw b <: t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result (usize & t_Extensions) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist406:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_Extensions u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist406)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (usize & t_Extensions)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (usize & t_Extensions)
      in
      if len =. (Bertie.Tls13utils.impl__Bytes__len b <: usize)
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok out <: Core.Result.t_Result t_Extensions u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
          (Core.Result.t_Result t_Extensions u8)
      else
        let* out_rest:t_Extensions =
          match
            Core.Ops.Try_trait.f_branch (check_extensions_slice algs
                  (Bertie.Tls13utils.impl__Bytes__raw_slice b
                      ({
                          Core.Ops.Range.f_start = len;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    t_Slice Bertie.Tls13utils.t_U8)
                <:
                Core.Result.t_Result t_Extensions u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist407:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_Extensions u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist407)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8) t_Extensions
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8) t_Extensions
        in
        Core.Ops.Control_flow.ControlFlow_Continue (impl__Extensions__merge out out_rest)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
          (Core.Result.t_Result t_Extensions u8))

let parse_client_hello
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (client_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let*
      Bertie.Tls13formats.Handshake_data.HandshakeData ch:Bertie.Tls13formats.Handshake_data.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message
                client_hello
                (Bertie.Tls13formats.Handshake_data.HandshakeType_ClientHello
                  <:
                  Bertie.Tls13formats.Handshake_data.t_HandshakeType)
              <:
              Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist408:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist408)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) Bertie.Tls13formats.Handshake_data.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) Bertie.Tls13formats.Handshake_data.t_HandshakeData
      in
      let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
      let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 1uy 0uy in
      let next:usize = sz 0 in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq ver
                (Bertie.Tls13utils.impl__Bytes__slice_range ch
                    ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 2 <: usize }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist409:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist409)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) Prims.unit
      in
      let next:usize = next +! sz 2 in
      let crand:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range ch
          ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 32 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
      in
      let next:usize = next +! sz 32 in
      let* sidlen:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u8_encoded (ch.[ {
                      Core.Ops.Range.f_start = next;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist410:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist410)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) usize
      in
      let sid:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range ch
          ({
              Core.Ops.Range.f_start = next +! sz 1 <: usize;
              Core.Ops.Range.f_end = (next +! sz 1 <: usize) +! sidlen <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
      in
      let next:usize = (next +! sz 1 <: usize) +! sidlen in
      let* cslen:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__check ciphersuite
                (Bertie.Tls13utils.impl__Bytes__raw_slice ch
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist411:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist411)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) usize
      in
      let next:usize = next +! cslen in
      let* _:Prims.unit =
        match
          Bertie.Tls13utils.check_eq comp
            (Bertie.Tls13utils.impl__Bytes__slice_range ch
                ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 2 <: usize }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Bertie.Tls13utils.t_Bytes)
        with
        | Core.Result.Result_Ok _ ->
          Core.Ops.Control_flow.ControlFlow_Continue (() <: Prims.unit)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) Prims.unit
        | Core.Result.Result_Err _ ->
          match
            Core.Ops.Try_trait.f_branch (invalid_compression_list ()
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist412:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                      Bertie.Tls13utils.t_Bytes &
                      Bertie.Tls13utils.t_Bytes &
                      Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                      Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                      usize) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist412)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8) Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8) Prims.unit
      in
      let next:usize = next +! sz 2 in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_length_encoding_u16 (Bertie.Tls13utils.impl__Bytes__slice_range
                    ch
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist413:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist413)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) Prims.unit
      in
      let next:usize = next +! sz 2 in
      let* exts:t_Extensions =
        match
          Core.Ops.Try_trait.f_branch (check_extensions ciphersuite
                (Bertie.Tls13utils.impl__Bytes__slice_range ch
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result t_Extensions u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist414:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist414)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) t_Extensions
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) t_Extensions
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let trunc_len:usize =
          ((Bertie.Tls13utils.impl__Bytes__len ch <: usize) -!
            (Bertie.Tls13crypto.impl__HashAlgorithm__hash_len (Bertie.Tls13crypto.impl__Algorithms__hash
                    ciphersuite
                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
              <:
              usize)
            <:
            usize) -!
          sz 3
        in
        match
          Bertie.Tls13crypto.impl__Algorithms__psk_mode ciphersuite, exts <: (bool & t_Extensions)
        with
        | _, { f_sni = _ ; f_key_share = Core.Option.Option_None  ; f_ticket = _ ; f_binder = _ } ->
          Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_MISSING_KEY_SHARE
        | true,
        { f_sni = Core.Option.Option_Some sn ;
          f_key_share = Core.Option.Option_Some gx ;
          f_ticket = Core.Option.Option_Some tkt ;
          f_binder = Core.Option.Option_Some binder } ->
          Core.Result.Result_Ok
          (crand,
            sid,
            sn,
            gx,
            (Core.Option.Option_Some tkt <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
            (Core.Option.Option_Some binder <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
            trunc_len
            <:
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize) u8
        | true,
        { f_sni = Core.Option.Option_None  ;
          f_key_share = Core.Option.Option_Some gx ;
          f_ticket = Core.Option.Option_Some tkt ;
          f_binder = Core.Option.Option_Some binder } ->
          Core.Result.Result_Ok
          (crand,
            sid,
            Bertie.Tls13utils.impl__Bytes__new (),
            gx,
            (Core.Option.Option_Some tkt <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
            (Core.Option.Option_Some binder <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
            trunc_len
            <:
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize) u8
        | false,
        { f_sni = Core.Option.Option_Some sn ;
          f_key_share = Core.Option.Option_Some gx ;
          f_ticket = Core.Option.Option_None  ;
          f_binder = Core.Option.Option_None  } ->
          Core.Result.Result_Ok
          (crand,
            sid,
            sn,
            gx,
            (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
            (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
            sz 0
            <:
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize) u8
        | false,
        { f_sni = Core.Option.Option_None  ;
          f_key_share = Core.Option.Option_Some gx ;
          f_ticket = Core.Option.Option_None  ;
          f_binder = Core.Option.Option_None  } ->
          Core.Result.Result_Ok
          (crand,
            sid,
            Bertie.Tls13utils.impl__Bytes__new (),
            gx,
            (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
            (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
            sz 0
            <:
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize) u8
        | _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize) u8)
        (Core.Result.t_Result
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize) u8))
