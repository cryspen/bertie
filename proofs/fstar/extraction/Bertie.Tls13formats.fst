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

let build_server_name__PREFIX1: t_Array u8 (sz 2) =
  let list = [Bertie.Tls13utils.v_U8 0uy; Bertie.Tls13utils.v_U8 0uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list list

let build_server_name__PREFIX2: t_Array u8 (sz 1) =
  let list = [Bertie.Tls13utils.v_U8 0uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
  Rust_primitives.Hax.array_of_list list

let key_shares__PREFIX: t_Array u8 (sz 2) =
  let list = [Bertie.Tls13utils.v_U8 0uy; Bertie.Tls13utils.v_U8 51uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list list

let psk_key_exchange_modes__PSK_MODE_PREFIX: t_Array u8 (sz 2) =
  let list = [Bertie.Tls13utils.v_U8 0uy; Bertie.Tls13utils.v_U8 45uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list list

let server_supported_version__SUPPORTED_VERSION_PREFIX: t_Array u8 (sz 2) =
  let list = [Bertie.Tls13utils.v_U8 0uy; Bertie.Tls13utils.v_U8 43uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list list

let supported_groups__SUPPORTED_GROUPS_PREFIX: t_Array u8 (sz 2) =
  let list = [Bertie.Tls13utils.v_U8 0uy; Bertie.Tls13utils.v_U8 10uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
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

let check_psk_key_exchange_modes (client_hello: t_Slice u8) : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u8_slice client_hello
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Bertie.Tls13utils.check_eq_slice (Rust_primitives.unsize (let list =
                  [Bertie.Tls13utils.v_U8 1uy <: u8]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list list)
            <:
            t_Slice u8)
          (client_hello.[ { Core.Ops.Range.f_start = sz 1; Core.Ops.Range.f_end = sz 2 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8))
      <:
      Core.Result.t_Result (Core.Result.t_Result Prims.unit u8) u8)

let check_supported_versions (client_hello: t_Slice u8) : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u8_slice client_hello
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Bertie.Tls13utils.check_mem (Rust_primitives.unsize (let list =
                  [Bertie.Tls13utils.v_U8 3uy <: u8; Bertie.Tls13utils.v_U8 4uy <: u8]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list list)
            <:
            t_Slice u8)
          (client_hello.[ {
                Core.Ops.Range.f_start = sz 1;
                Core.Ops.Range.f_end = Core.Slice.impl__len client_hello <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8))
      <:
      Core.Result.t_Result (Core.Result.t_Result Prims.unit u8) u8)

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

let check_psk_shared_key (v__algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| len_id:usize =
        Core.Result.impl__map_err (Bertie.Tls13utils.length_u16_encoded ch
            <:
            Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| len_tkt:usize =
        Core.Result.impl__map_err (Bertie.Tls13utils.length_u16_encoded (ch.[ {
                    Core.Ops.Range.f_start = sz 2;
                    Core.Ops.Range.f_end = sz 2 +! len_id <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      if len_id =. (len_tkt +! sz 6 <: usize)
      then
        let| _:Prims.unit =
          Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u16_slice (ch.[ {
                      Core.Ops.Range.f_start = sz 2 +! len_id <: usize;
                      Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| _:Prims.unit =
          Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u8_slice (ch.[ {
                      Core.Ops.Range.f_start = sz 4 +! len_id <: usize;
                      Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (if (((Core.Slice.impl__len ch <: usize) -! sz 6 <: usize) -! len_id <: usize) <>. sz 32
          then Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
          else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result Prims.unit u8) u8
      else
        Core.Result.Result_Ok (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8))
        <:
        Core.Result.t_Result (Core.Result.t_Result Prims.unit u8) u8)

let check_server_psk_shared_key (v__algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Core.Result.t_Result Prims.unit u8 =
  Bertie.Tls13utils.check_eq_slice (Rust_primitives.unsize (let list =
            [Bertie.Tls13utils.v_U8 0uy <: u8; Bertie.Tls13utils.v_U8 0uy <: u8]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list list)
      <:
      t_Slice u8)
    b

let check_server_supported_version (v__algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Core.Result.t_Result Prims.unit u8 =
  Bertie.Tls13utils.check_eq_slice (Rust_primitives.unsize (let list =
            [Bertie.Tls13utils.v_U8 3uy <: u8; Bertie.Tls13utils.v_U8 4uy <: u8]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list list)
      <:
      t_Slice u8)
    b

let check_server_name (extension: t_Slice u8) : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u16_slice extension
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_eq_slice (Rust_primitives.unsize (let
                    list =
                      [Bertie.Tls13utils.v_U8 0uy <: u8]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list list)
                <:
                t_Slice u8)
              (extension.[ { Core.Ops.Range.f_start = sz 2; Core.Ops.Range.f_end = sz 3 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u16_slice (extension.[ {
                    Core.Ops.Range.f_start = sz 3;
                    Core.Ops.Range.f_end = Core.Slice.impl__len extension <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
        (Core.Convert.f_into (extension.[ {
                  Core.Ops.Range.f_start = sz 5;
                  Core.Ops.Range.f_end = Core.Slice.impl__len extension <: usize
                }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8))
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let check_server_key_share (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist21:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let hoist22:t_Slice u8 = Bertie.Tls13utils.impl__Bytes__as_raw hoist21 in
      let hoist23:Core.Result.t_Result Prims.unit u8 =
        Bertie.Tls13utils.check_eq_slice hoist22
          (b.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      in
      let hoist24:Core.Result.t_Result Prims.unit u8 =
        Core.Result.impl__map_err hoist23 (Core.Convert.f_from <: u8 -> u8)
      in
      let| _:Prims.unit = hoist24 in
      let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u16_slice (b.[ {
                    Core.Ops.Range.f_start = sz 2;
                    Core.Ops.Range.f_end = Core.Slice.impl__len b <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
        (Core.Convert.f_from (b.[ {
                  Core.Ops.Range.f_start = sz 4;
                  Core.Ops.Range.f_end = Core.Slice.impl__len b <: usize
                }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8))
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let check_server_extension (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let l0:usize =
        cast (Bertie.Tls13utils.f_declassify (b.[ sz 0 ] <: u8) <: u8) <: usize
      in
      let l1:usize = cast (Bertie.Tls13utils.f_declassify (b.[ sz 1 ] <: u8) <: u8) <: usize in
      let| len:usize =
        Core.Result.impl__map_err (Bertie.Tls13utils.length_u16_encoded (b.[ {
                    Core.Ops.Range.f_start = sz 2;
                    Core.Ops.Range.f_end = Core.Slice.impl__len b <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let out:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
      in
      let| out:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match (cast (l0 <: usize) <: u8), (cast (l1 <: usize) <: u8) <: (u8 & u8) with
        | 0uy, 43uy ->
          let| _:Prims.unit =
            Core.Result.impl__map_err (check_server_supported_version algs
                  (b.[ {
                        Core.Ops.Range.f_start = sz 4;
                        Core.Ops.Range.f_end = sz 4 +! len <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                Core.Result.t_Result Prims.unit u8)
              (Core.Convert.f_from <: u8 -> u8)
          in
          Core.Result.Result_Ok out
          <:
          Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
        | 0uy, 51uy ->
          let| gx:Bertie.Tls13utils.t_Bytes =
            Core.Result.impl__map_err (check_server_key_share algs
                  (b.[ {
                        Core.Ops.Range.f_start = sz 4;
                        Core.Ops.Range.f_end = sz 4 +! len <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              (Core.Convert.f_from <: u8 -> u8)
          in
          Core.Result.Result_Ok
          (Core.Option.Option_Some gx <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
          <:
          Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
        | 0uy, 41uy ->
          let| _:Prims.unit =
            Core.Result.impl__map_err (check_server_psk_shared_key algs
                  (b.[ {
                        Core.Ops.Range.f_start = sz 4;
                        Core.Ops.Range.f_end = sz 4 +! len <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                Core.Result.t_Result Prims.unit u8)
              (Core.Convert.f_from <: u8 -> u8)
          in
          Core.Result.Result_Ok out
          <:
          Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
        | _ ->
          Core.Result.Result_Ok out
          <:
          Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
        (sz 4 +! len, out <: (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes))
        <:
        Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8) u8)

let check_signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u16_slice ch
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist25:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let hoist26:t_Slice u8 = Bertie.Tls13utils.impl__Bytes__as_raw hoist25 in
        Bertie.Tls13utils.check_mem hoist26
          (ch.[ {
                Core.Ops.Range.f_start = sz 2;
                Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8))
      <:
      Core.Result.t_Result (Core.Result.t_Result Prims.unit u8) u8)

let check_supported_groups (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u16_slice ch
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist27:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let hoist28:t_Slice u8 = Bertie.Tls13utils.impl__Bytes__as_raw hoist27 in
        Bertie.Tls13utils.check_mem hoist28
          (ch.[ {
                Core.Ops.Range.f_start = sz 2;
                Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8))
      <:
      Core.Result.t_Result (Core.Result.t_Result Prims.unit u8) u8)

let parse_ecdsa_signature (sig: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (if
        (Bertie.Tls13utils.impl__Bytes__len sig <: usize) <. sz 4 <: bool
      then
        Core.Result.Result_Ok
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8
      else
        let| _:Prims.unit =
          Core.Result.impl__map_err (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 48uy
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
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| _:Prims.unit =
          Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u8 (Bertie.Tls13utils.impl__Bytes__slice_range
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
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| _:Prims.unit =
          Core.Result.impl__map_err (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 2uy
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
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| rlen:usize =
          Core.Result.impl__map_err (Bertie.Tls13utils.length_u8_encoded (sig.[ {
                      Core.Ops.Range.f_start = sz 3;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sig <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result usize u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| _:Prims.unit =
          Core.Result.impl__map_err (check_r_len rlen <: Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
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
          Core.Result.Result_Ok (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_INVALID_SIGNATURE)
          <:
          Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8
        else
          let| _:Prims.unit =
            Core.Result.impl__map_err (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 2uy
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
              (Core.Convert.f_from <: u8 -> u8)
          in
          let| _:Prims.unit =
            Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u8 (Bertie.Tls13utils.impl__Bytes__slice_range
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
              (Core.Convert.f_from <: u8 -> u8)
          in
          Core.Result.Result_Ok
          (let s:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__slice sig
                ((Bertie.Tls13utils.impl__Bytes__len sig <: usize) -! sz 32 <: usize)
                (sz 32)
            in
            Core.Result.Result_Ok (Bertie.Tls13utils.impl__Bytes__concat r s)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          <:
          Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let build_server_name (name: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist58:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 (Core.Clone.f_clone name
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let hoist59:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__prefix hoist58
          (Rust_primitives.unsize build_server_name__PREFIX2 <: t_Slice u8)
      in
      let hoist60:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist59
      in
      let hoist61:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Core.Result.impl__map_err hoist60 (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist62:Bertie.Tls13utils.t_Bytes = hoist61 in
      let hoist63:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist62
      in
      let hoist64:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Core.Result.impl__map_err hoist63 (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist65:Bertie.Tls13utils.t_Bytes = hoist64 in
      Core.Result.Result_Ok
      (let hoist66:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__prefix hoist65
            (Rust_primitives.unsize build_server_name__PREFIX1 <: t_Slice u8)
        in
        Core.Result.Result_Ok hoist66 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist68:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist67:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 gx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let ks:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat hoist68 hoist67 in
      let| hoist69:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 ks
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let hoist70:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist69
      in
      let hoist71:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Core.Result.impl__map_err hoist70 (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist72:Bertie.Tls13utils.t_Bytes = hoist71 in
      Core.Result.Result_Ok
      (let hoist73:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__prefix hoist72
            (Rust_primitives.unsize key_shares__PREFIX <: t_Slice u8)
        in
        Core.Result.Result_Ok hoist73 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let server_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist75:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist74:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 gx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let ks:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat hoist75 hoist74 in
      let| hoist76:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 ks
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let hoist77:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 51uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist76
        in
        Core.Result.Result_Ok hoist77 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let server_pre_shared_key (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist78:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.bytes2 0uy
                  0uy
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let hoist79:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 41uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist78
        in
        Core.Result.Result_Ok hoist79 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let server_supported_version (v__algorithms: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist80:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.bytes2 3uy
                  4uy
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let hoist81:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__prefix hoist80
            (Rust_primitives.unsize server_supported_version__SUPPORTED_VERSION_PREFIX <: t_Slice u8
            )
        in
        Core.Result.Result_Ok hoist81 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist82:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let hoist83:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist82
      in
      let hoist84:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Core.Result.impl__map_err hoist83 (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist85:Bertie.Tls13utils.t_Bytes = hoist84 in
      let hoist86:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist85
      in
      let hoist87:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Core.Result.impl__map_err hoist86 (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist88:Bertie.Tls13utils.t_Bytes = hoist87 in
      Core.Result.Result_Ok
      (let hoist89:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 13uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist88
        in
        Core.Result.Result_Ok hoist89 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let supported_groups (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist90:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let hoist91:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist90
      in
      let hoist92:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Core.Result.impl__map_err hoist91 (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist93:Bertie.Tls13utils.t_Bytes = hoist92 in
      let hoist94:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist93
      in
      let hoist95:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Core.Result.impl__map_err hoist94 (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist96:Bertie.Tls13utils.t_Bytes = hoist95 in
      Core.Result.Result_Ok
      (let hoist97:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__prefix hoist96
            (Rust_primitives.unsize supported_groups__SUPPORTED_GROUPS_PREFIX <: t_Slice u8)
        in
        Core.Result.Result_Ok hoist97 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let ecdsa_signature (sv: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (if
        (Bertie.Tls13utils.impl__Bytes__len sv <: usize) <>. sz 64 <: bool
      then
        Core.Result.Result_Ok
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8
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
          if (Bertie.Tls13utils.f_declassify (r.[ sz 0 ] <: u8) <: u8) >=. 128uy
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
          if (Bertie.Tls13utils.f_declassify (s.[ sz 0 ] <: u8) <: u8) >=. 128uy
          then
            let s:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat b0 s in
            s
          else s
        in
        let| hoist98:Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw
                    r
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let hoist99:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Core.Clone.f_clone b2 <: Bertie.Tls13utils.t_Bytes)
            hoist98
        in
        let hoist101:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat hoist99 b2 in
        let| hoist100:Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw
                    s
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let hoist102:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat hoist101 hoist100
        in
        let hoist103:t_Slice u8 = Bertie.Tls13utils.impl__Bytes__as_raw hoist102 in
        let hoist104:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
          Bertie.Tls13utils.encode_length_u8 hoist103
        in
        let hoist105:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
          Core.Result.impl__map_err hoist104 (Core.Convert.f_from <: u8 -> u8)
        in
        let| hoist106:Bertie.Tls13utils.t_Bytes = hoist105 in
        Core.Result.Result_Ok
        (let hoist107:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__concat b1 hoist106
          in
          Core.Result.Result_Ok hoist107 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let pre_shared_key
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (session_ticket: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist108:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 (Core.Clone.f_clone session_ticket

                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let hoist109:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat_array (sz 4)
          hoist108
          (Bertie.Tls13utils.u32_as_be_bytes (Bertie.Tls13utils.v_U32 4294967295ul <: u32)
            <:
            t_Array u8 (sz 4))
      in
      let hoist110:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist109
      in
      let hoist111:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Core.Result.impl__map_err hoist110 (Core.Convert.f_from <: u8 -> u8)
      in
      let| identities:Bertie.Tls13utils.t_Bytes = hoist111 in
      let| hoist112:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw
                  (Bertie.Tls13crypto.zero_key (Bertie.Tls13crypto.impl__Algorithms__hash algs
                        <:
                        Bertie.Tls13crypto.t_HashAlgorithm)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let hoist113:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist112
      in
      let hoist114:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Core.Result.impl__map_err hoist113 (Core.Convert.f_from <: u8 -> u8)
      in
      let| binders:Bertie.Tls13utils.t_Bytes = hoist114 in
      let binders_len:usize = Bertie.Tls13utils.impl__Bytes__len binders in
      let| hoist115:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl__Bytes__concat
                  identities
                  binders
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let ext:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 41uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist115
        in
        Core.Result.Result_Ok (ext, binders_len <: (Bertie.Tls13utils.t_Bytes & usize))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) u8)

let psk_key_exchange_modes (_: Prims.unit) : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist116:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u8 (Rust_primitives.unsize (let
                    list =
                      [Bertie.Tls13utils.v_U8 1uy <: u8]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list list)
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let hoist117:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist116
      in
      let hoist118:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Core.Result.impl__map_err hoist117 (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist119:Bertie.Tls13utils.t_Bytes = hoist118 in
      Core.Result.Result_Ok
      (let hoist120:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__prefix hoist119
            (Rust_primitives.unsize psk_key_exchange_modes__PSK_MODE_PREFIX <: t_Slice u8)
        in
        Core.Result.Result_Ok hoist120 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let supported_versions (_: Prims.unit) : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist121:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u8 (Rust_primitives.unsize (let
                    list =
                      [Bertie.Tls13utils.v_U8 3uy <: u8; Bertie.Tls13utils.v_U8 4uy <: u8]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                    Rust_primitives.Hax.array_of_list list)
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let hoist122:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist121
      in
      let hoist123:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Core.Result.impl__map_err hoist122 (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist124:Bertie.Tls13utils.t_Bytes = hoist123 in
      Core.Result.Result_Ok
      (let hoist125:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Core.Convert.f_from (let list = [0uy; 43uy] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                  Rust_primitives.Hax.array_of_list list)
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist124
        in
        Core.Result.Result_Ok hoist125 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

type t_Extensions = {
  f_sni:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_key_share:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_ticket:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_binder:Core.Option.t_Option Bertie.Tls13utils.t_Bytes
}

let impl__Extensions__merge (self e2: t_Extensions) : Core.Result.t_Result t_Extensions u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist156:Core.Option.t_Option
      Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (merge_opts self.f_sni e2.f_sni
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist155:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (merge_opts self.f_key_share e2.f_key_share
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist154:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (merge_opts self.f_ticket e2.f_ticket
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist153:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (merge_opts self.f_binder e2.f_binder
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let hoist157:t_Extensions =
          { f_sni = hoist156; f_key_share = hoist155; f_ticket = hoist154; f_binder = hoist153 }
          <:
          t_Extensions
        in
        Core.Result.Result_Ok hoist157 <: Core.Result.t_Result t_Extensions u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result t_Extensions u8) u8)

let certificate_verify (algs: Bertie.Tls13crypto.t_Algorithms) (cv: Bertie.Tls13utils.t_Bytes)
    : Core.Ops.Control_flow.t_ControlFlow
      (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      (Core.Result.t_Result
          (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8) u8) =
  let! sv:Bertie.Tls13utils.t_Bytes =
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
        let! hoist161:Rust_primitives.Hax.t_Never =
          Core.Ops.Control_flow.ControlFlow.v_Break (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed
                    ()
                  <:
                  u8)
              <:
              Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        in
        Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist161)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          Bertie.Tls13utils.t_Bytes
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.impl__map_err (ecdsa_signature cv
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8))
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
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
  Core.Ops.Control_flow.ControlFlow_Continue
  (let| hoist163:Bertie.Tls13utils.t_Bytes =
      Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Convert.f_from <: u8 -> u8)
    in
    let| hoist162:Bertie.Tls13utils.t_Bytes =
      Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 sv
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Convert.f_from <: u8 -> u8)
    in
    Core.Result.Result_Ok
    (let sig:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat hoist163 hoist162 in
      Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_CertificateVerify
          <:
          Bertie.Tls13formats.Handshake_data.t_HandshakeType)
        sig)
    <:
    Core.Result.t_Result
      (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8) u8)
  <:
  Core.Ops.Control_flow.t_ControlFlow
    (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
    (Core.Result.t_Result
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8) u8)

let check_handshake_record (p: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (if
        (Bertie.Tls13utils.impl__Bytes__len p <: usize) <. sz 5 <: bool
      then
        Core.Result.Result_Ok
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
          <:
          Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
        <:
        Core.Result.t_Result
          (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8) u8
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
        let| _:Prims.unit =
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
            Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
          | Core.Result.Result_Err _ ->
            Core.Result.impl__map_err (application_data_instead_of_handshake ()
                <:
                Core.Result.t_Result Prims.unit u8)
              (Core.Convert.f_from <: u8 -> u8)
        in
        let| _:Prims.unit =
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
            Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
          | Core.Result.Result_Err _ ->
            Core.Result.impl__map_err (protocol_version_alert ()
                <:
                Core.Result.t_Result Prims.unit u8)
              (Core.Convert.f_from <: u8 -> u8)
        in
        let| len:usize =
          Core.Result.impl__map_err (Bertie.Tls13utils.length_u16_encoded (p.[ {
                      Core.Ops.Range.f_start = sz 3;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len p <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result usize u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
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
        Core.Result.t_Result
          (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8) u8)

let check_server_extensions (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| len, out:(usize &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes) =
        Core.Result.impl__map_err (check_server_extension algs b
            <:
            Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      if len =. (Core.Slice.impl__len b <: usize)
      then
        Core.Result.Result_Ok
        (Core.Result.Result_Ok out
          <:
          Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        <:
        Core.Result.t_Result
          (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8) u8
      else
        let| out_rest:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (check_server_extensions algs
                (b.[ {
                      Core.Ops.Range.f_start = len;
                      Core.Ops.Range.f_end = Core.Slice.impl__len b <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok (merge_opts out out_rest)
        <:
        Core.Result.t_Result
          (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8) u8)

let client_hello
      (algorithms: Bertie.Tls13crypto.t_Algorithms)
      (client_random kem_pk server_name: Bertie.Tls13utils.t_Bytes)
      (session_ticket: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let version:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes2 3uy 3uy
      in
      let compression_methods:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 1uy 0uy in
      let| legacy_session_id:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u8 (Rust_primitives.unsize (Rust_primitives.Hax.repeat
                      (Bertie.Tls13utils.v_U8 0uy <: u8)
                      (sz 32)
                    <:
                    t_Array u8 (sz 32))
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist164:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__ciphersuite algorithms
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let hoist165:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u16 hoist164
      in
      let hoist166:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Core.Result.impl__map_err hoist165 (Core.Convert.f_from <: u8 -> u8)
      in
      let| cipher_suites:Bertie.Tls13utils.t_Bytes = hoist166 in
      let| server_name:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (build_server_name server_name
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| supported_versions:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (supported_versions ()
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| supported_groups:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (supported_groups algorithms
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| signature_algorithms:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (signature_algorithms algorithms
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| key_shares:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (key_shares algorithms
              (Core.Clone.f_clone kem_pk <: Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
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
      let| extensions, trunc_len:(Bertie.Tls13utils.t_Bytes & usize) =
        match
          Bertie.Tls13crypto.impl__Algorithms__psk_mode algorithms, session_ticket
          <:
          (bool & Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        with
        | true, Core.Option.Option_Some session_ticket ->
          let| pskm:Bertie.Tls13utils.t_Bytes =
            Core.Result.impl__map_err (psk_key_exchange_modes ()
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              (Core.Convert.f_from <: u8 -> u8)
          in
          let| psk, len:(Bertie.Tls13utils.t_Bytes & usize) =
            Core.Result.impl__map_err (pre_shared_key algorithms session_ticket
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
              (Core.Convert.f_from <: u8 -> u8)
          in
          Core.Result.Result_Ok
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
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8
        | false, Core.Option.Option_None  ->
          Core.Result.Result_Ok (extensions, trunc_len <: (Bertie.Tls13utils.t_Bytes & usize))
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8
        | _ ->
          let| _:Prims.unit =
            Core.Result.impl__map_err (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_PSK_MODE_MISMATCH

                <:
                Core.Result.t_Result Prims.unit u8)
              (Core.Convert.f_from <: u8 -> u8)
          in
          Core.Result.Result_Ok (extensions, trunc_len <: (Bertie.Tls13utils.t_Bytes & usize))
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8
      in
      let| encoded_extensions:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 extensions
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
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
      let| client_hello:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
        Core.Result.impl__map_err (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes
              (Bertie.Tls13formats.Handshake_data.HandshakeType_ClientHello
                <:
                Bertie.Tls13formats.Handshake_data.t_HandshakeType)
              handshake_bytes
            <:
            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
        (client_hello, trunc_len <: (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize))
        <:
        Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8) u8)

let encrypted_extensions (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let handshake_type:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes1 (cast (Bertie.Tls13formats.Handshake_data.HandshakeType.EncryptedExtensions.anon_const +!
                0uy
                <:
                u8)
            <:
            u8)
      in
      let| hoist167:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl__Bytes__new
                  ()
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let hoist168:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_length_u24 hoist167
      in
      let hoist169:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Core.Result.impl__map_err hoist168 (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist170:Bertie.Tls13utils.t_Bytes = hoist169 in
      Core.Result.Result_Ok
      (let hoist171:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat handshake_type hoist170
        in
        let hoist172:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
          Bertie.Tls13formats.Handshake_data.HandshakeData hoist171
          <:
          Bertie.Tls13formats.Handshake_data.t_HandshakeData
        in
        Core.Result.Result_Ok hoist172
        <:
        Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8) u8)

let find_key_share (g: Bertie.Tls13utils.t_Bytes) (ch: t_Slice u8)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (if
        (Core.Slice.impl__len ch <: usize) <. sz 4 <: bool
      then
        Core.Result.Result_Ok
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8
      else
        if
          Bertie.Tls13utils.eq_slice (Bertie.Tls13utils.impl__Bytes__as_raw g <: t_Slice u8)
            (ch.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
          <:
          bool
        then
          let| len:usize =
            Core.Result.impl__map_err (Bertie.Tls13utils.length_u16_encoded_slice (ch.[ {
                        Core.Ops.Range.f_start = sz 2;
                        Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                Core.Result.t_Result usize u8)
              (Core.Convert.f_from <: u8 -> u8)
          in
          Core.Result.Result_Ok
          (Core.Result.Result_Ok
            (Core.Convert.f_into (ch.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8))
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          <:
          Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8
        else
          let| len:usize =
            Core.Result.impl__map_err (Bertie.Tls13utils.length_u16_encoded_slice (ch.[ {
                        Core.Ops.Range.f_start = sz 2;
                        Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                Core.Result.t_Result usize u8)
              (Core.Convert.f_from <: u8 -> u8)
          in
          Core.Result.Result_Ok
          (find_key_share g
              (ch.[ {
                    Core.Ops.Range.f_start = sz 4 +! len <: usize;
                    Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8))
          <:
          Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let check_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u16_slice ch
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist173:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (find_key_share hoist173
          (ch.[ {
                Core.Ops.Range.f_start = sz 2;
                Core.Ops.Range.f_end = Core.Slice.impl__len ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8))
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let check_extension (algs: Bertie.Tls13crypto.t_Algorithms) (bytes: t_Slice u8)
    : Core.Result.t_Result (usize & t_Extensions) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let l0:usize =
        cast (Bertie.Tls13utils.f_declassify (bytes.[ sz 0 ] <: u8) <: u8) <: usize
      in
      let l1:usize = cast (Bertie.Tls13utils.f_declassify (bytes.[ sz 1 ] <: u8) <: u8) <: usize in
      let| len:usize =
        Core.Result.impl__map_err (Bertie.Tls13utils.length_u16_encoded_slice (bytes.[ {
                    Core.Ops.Range.f_start = sz 2;
                    Core.Ops.Range.f_end = Core.Slice.impl__len bytes <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
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
        let| hoist174:Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (check_server_name (bytes.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (let hoist175:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
            Core.Option.Option_Some hoist174 <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
          in
          let hoist176:t_Extensions =
            {
              f_sni = hoist175;
              f_key_share
              =
              Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
              f_ticket = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
              f_binder = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
            }
            <:
            t_Extensions
          in
          let hoist177:(usize & t_Extensions) = sz 4 +! len, hoist176 <: (usize & t_Extensions) in
          Core.Result.Result_Ok hoist177 <: Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result (usize & t_Extensions) u8) u8
      | 0uy, 45uy ->
        let| _:Prims.unit =
          Core.Result.impl__map_err (check_psk_key_exchange_modes (bytes.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result (usize & t_Extensions) u8) u8
      | 0uy, 43uy ->
        let| _:Prims.unit =
          Core.Result.impl__map_err (check_supported_versions (bytes.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result (usize & t_Extensions) u8) u8
      | 0uy, 10uy ->
        let| _:Prims.unit =
          Core.Result.impl__map_err (check_supported_groups algs
                (bytes.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result (usize & t_Extensions) u8) u8
      | 0uy, 13uy ->
        let| _:Prims.unit =
          Core.Result.impl__map_err (check_signature_algorithms algs
                (bytes.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result (usize & t_Extensions) u8) u8
      | 0uy, 51uy ->
        Core.Result.Result_Ok
        (match
            check_key_shares algs
              (bytes.[ {
                    Core.Ops.Range.f_start = sz 4;
                    Core.Ops.Range.f_end = sz 4 +! len <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
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
        Core.Result.t_Result (Core.Result.t_Result (usize & t_Extensions) u8) u8
      | 0uy, 41uy ->
        let| _:Prims.unit =
          Core.Result.impl__map_err (check_psk_shared_key algs
                (bytes.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result (usize & t_Extensions) u8) u8
      | _ ->
        Core.Result.Result_Ok
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result (usize & t_Extensions) u8) u8)

let finished (vd: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
  Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_Finished
      <:
      Bertie.Tls13formats.Handshake_data.t_HandshakeType)
    vd

let get_handshake_record (p: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hd, len:(Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        usize) =
        Core.Result.impl__map_err (check_handshake_record p
            <:
            Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (if len =. (Bertie.Tls13utils.impl__Bytes__len p <: usize)
        then
          Core.Result.Result_Ok hd
          <:
          Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
        else Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8))
      <:
      Core.Result.t_Result
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8) u8)

let handshake_record (p: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let ty:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes1 (cast (Bertie.Tls13formats.ContentType.Handshake.anon_const +! 0uy
                <:
                u8)
            <:
            u8)
      in
      let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
      let| hoist178:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 p
                .Bertie.Tls13formats.Handshake_data._0
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let hoist179:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat ty ver
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist178
        in
        Core.Result.Result_Ok hoist179 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let parse_certificate_verify
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (certificate_verify: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let|
      Bertie.Tls13formats.Handshake_data.HandshakeData cv:Bertie.Tls13formats.Handshake_data.t_HandshakeData
      =
        Core.Result.impl__map_err (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message
              certificate_verify
              (Bertie.Tls13formats.Handshake_data.HandshakeType_CertificateVerify
                <:
                Bertie.Tls13formats.Handshake_data.t_HandshakeType)
            <:
            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let sa:Bertie.Tls13crypto.t_SignatureScheme =
        Bertie.Tls13crypto.impl__Algorithms__signature algs
      in
      let| hoist180:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let hoist181:Core.Result.t_Result Prims.unit u8 =
        Bertie.Tls13utils.check_eq hoist180
          (Bertie.Tls13utils.impl__Bytes__slice_range cv
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Bertie.Tls13utils.t_Bytes)
      in
      let hoist182:Core.Result.t_Result Prims.unit u8 =
        Core.Result.impl__map_err hoist181 (Core.Convert.f_from <: u8 -> u8)
      in
      let| _:Prims.unit = hoist182 in
      let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u16 (Bertie.Tls13utils.impl__Bytes__slice_range
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
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
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
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let parse_encrypted_extensions
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (encrypted_extensions: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let
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
      let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_eq expected_handshake_type
              (Bertie.Tls13utils.impl__Bytes__slice_range encrypted_extension_bytes
                  ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
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
            t_Slice u8))
      <:
      Core.Result.t_Result (Core.Result.t_Result Prims.unit u8) u8)

let parse_finished (finished: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let|
      Bertie.Tls13formats.Handshake_data.HandshakeData fin:Bertie.Tls13formats.Handshake_data.t_HandshakeData
      =
        Core.Result.impl__map_err (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message
              finished
              (Bertie.Tls13formats.Handshake_data.HandshakeType_Finished
                <:
                Bertie.Tls13formats.Handshake_data.t_HandshakeType)
            <:
            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok fin <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let parse_server_certificate (certificate: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let|
      Bertie.Tls13formats.Handshake_data.HandshakeData sc:Bertie.Tls13formats.Handshake_data.t_HandshakeData
      =
        Core.Result.impl__map_err (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message
              certificate
              (Bertie.Tls13formats.Handshake_data.HandshakeType_Certificate
                <:
                Bertie.Tls13formats.Handshake_data.t_HandshakeType)
            <:
            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let next:usize = sz 0 in
      let| creqlen:usize =
        Core.Result.impl__map_err (Bertie.Tls13utils.length_u8_encoded (sc.[ {
                    Core.Ops.Range.f_start = sz 4;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let next:usize = (next +! sz 1 <: usize) +! creqlen in
      let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u24 (Bertie.Tls13utils.impl__Bytes__raw_slice
                  sc
                  ({
                      Core.Ops.Range.f_start = next;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let next:usize = next +! sz 3 in
      let| crtlen:usize =
        Core.Result.impl__map_err (Bertie.Tls13utils.length_u24_encoded (Bertie.Tls13utils.impl__Bytes__raw_slice
                  sc
                  ({
                      Core.Ops.Range.f_start = next;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let next:usize = next +! sz 3 in
      let crt:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range sc
          ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! crtlen <: usize }
            <:
            Core.Ops.Range.t_Range usize)
      in
      let next:usize = next +! crtlen in
      let| v__extlen:usize =
        Core.Result.impl__map_err (Bertie.Tls13utils.length_u16_encoded (sc.[ {
                    Core.Ops.Range.f_start = next;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok crt <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let parse_server_hello
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (server_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let|
      Bertie.Tls13formats.Handshake_data.HandshakeData server_hello:Bertie.Tls13formats.Handshake_data.t_HandshakeData
      =
        Core.Result.impl__map_err (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message
              server_hello
              (Bertie.Tls13formats.Handshake_data.HandshakeType_ServerHello
                <:
                Bertie.Tls13formats.Handshake_data.t_HandshakeType)
            <:
            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
      let| cip:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__ciphersuite algs
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 0uy in
      let next:usize = sz 0 in
      let| _:Prims.unit =
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
          Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
        | Core.Result.Result_Err _ ->
          Core.Result.impl__map_err (protocol_version_alert () <: Core.Result.t_Result Prims.unit u8
            )
            (Core.Convert.f_from <: u8 -> u8)
      in
      let next:usize = next +! sz 2 in
      let srand:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range server_hello
          ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 32 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
      in
      let next:usize = next +! sz 32 in
      let| sidlen:usize =
        Core.Result.impl__map_err (Bertie.Tls13utils.length_u8_encoded (server_hello.[ {
                    Core.Ops.Range.f_start = next;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len server_hello <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let next:usize = (next +! sz 1 <: usize) +! sidlen in
      let| _:Prims.unit =
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
          Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
        | Core.Result.Result_Err _ ->
          Core.Result.impl__map_err (unsupported_cipher_alert ()
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
      in
      let next:usize = next +! sz 2 in
      let| _:Prims.unit =
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
          Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
        | Core.Result.Result_Err _ ->
          Core.Result.impl__map_err (invalid_compression_method_alert ()
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
      in
      let next:usize = next +! sz 1 in
      let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u16 (Bertie.Tls13utils.impl__Bytes__slice_range
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
          (Core.Convert.f_from <: u8 -> u8)
      in
      let next:usize = next +! sz 2 in
      let| gy:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (check_server_extensions algs
              (server_hello.[ {
                    Core.Ops.Range.f_start = next;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len server_hello <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
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
      Core.Result.t_Result
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8) u8)

let server_certificate (v__algs: Bertie.Tls13crypto.t_Algorithms) (cert: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| creq:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u8 (Rust_primitives.unsize (let
                    list =
                      []
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 0);
                    Rust_primitives.Hax.array_of_list list)
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| crt:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u24 cert
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| ext:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl__Bytes__new
                  ()
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| crts:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u24 (Bertie.Tls13utils.impl__Bytes__concat
                  crt
                  ext
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_Certificate
            <:
            Bertie.Tls13formats.Handshake_data.t_HandshakeType)
          (Bertie.Tls13utils.impl__Bytes__concat creq crts <: Bertie.Tls13utils.t_Bytes))
      <:
      Core.Result.t_Result
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8) u8)

let server_hello (algs: Bertie.Tls13crypto.t_Algorithms) (sr sid gy: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let ver:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes2 3uy 3uy
      in
      let| sid:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw
                  sid
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| cip:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__ciphersuite algs
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 0uy in
      let| ks:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (server_key_shares algs
              (Core.Clone.f_clone gy <: Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| sv:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (server_supported_version algs
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let exts:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat ks sv in
      let| exts:Bertie.Tls13utils.t_Bytes =
        match Bertie.Tls13crypto.impl__Algorithms__psk_mode algs with
        | true ->
          let| hoist183:Bertie.Tls13utils.t_Bytes =
            Core.Result.impl__map_err (server_pre_shared_key algs
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              (Core.Convert.f_from <: u8 -> u8)
          in
          Core.Result.Result_Ok
          (let hoist184:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__concat exts hoist183
            in
            hoist184)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | false -> Core.Result.Result_Ok exts <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      in
      let| encoded_extensions:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u16 exts
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
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
      let hoist185:Bertie.Tls13utils.t_Bytes = out in
      let hoist186:Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
        Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_ServerHello
            <:
            Bertie.Tls13formats.Handshake_data.t_HandshakeType)
          hoist185
      in
      let hoist187:Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8 =
        Core.Result.impl__map_err hoist186 (Core.Convert.f_from <: u8 -> u8)
      in
      let| sh:Bertie.Tls13formats.Handshake_data.t_HandshakeData = hoist187 in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok sh
        <:
        Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8) u8)

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
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| th:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__HashAlgorithm__hash self
                .f_hash_algorithm
              self.f_transcript.Bertie.Tls13formats.Handshake_data._0
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok th <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

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

let check_extensions_slice (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8)
    : Core.Result.t_Result t_Extensions u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| len, out:(usize & t_Extensions) =
        Core.Result.impl__map_err (check_extension algs b
            <:
            Core.Result.t_Result (usize & t_Extensions) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      if len =. (Core.Slice.impl__len b <: usize)
      then
        Core.Result.Result_Ok (Core.Result.Result_Ok out <: Core.Result.t_Result t_Extensions u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result t_Extensions u8) u8
      else
        let| out_rest:t_Extensions =
          Core.Result.impl__map_err (check_extensions_slice algs
                (b.[ {
                      Core.Ops.Range.f_start = len;
                      Core.Ops.Range.f_end = Core.Slice.impl__len b <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result t_Extensions u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok (impl__Extensions__merge out out_rest)
        <:
        Core.Result.t_Result (Core.Result.t_Result t_Extensions u8) u8)

let check_extensions (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result t_Extensions u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| len, out:(usize & t_Extensions) =
        Core.Result.impl__map_err (check_extension algs
              (Bertie.Tls13utils.impl__Bytes__as_raw b <: t_Slice u8)
            <:
            Core.Result.t_Result (usize & t_Extensions) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      if len =. (Bertie.Tls13utils.impl__Bytes__len b <: usize)
      then
        Core.Result.Result_Ok (Core.Result.Result_Ok out <: Core.Result.t_Result t_Extensions u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result t_Extensions u8) u8
      else
        let| out_rest:t_Extensions =
          Core.Result.impl__map_err (check_extensions_slice algs
                (Bertie.Tls13utils.impl__Bytes__raw_slice b
                    ({
                        Core.Ops.Range.f_start = len;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result t_Extensions u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok (impl__Extensions__merge out out_rest)
        <:
        Core.Result.t_Result (Core.Result.t_Result t_Extensions u8) u8)

let parse_client_hello
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (client_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let|
      Bertie.Tls13formats.Handshake_data.HandshakeData ch:Bertie.Tls13formats.Handshake_data.t_HandshakeData
      =
        Core.Result.impl__map_err (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message
              client_hello
              (Bertie.Tls13formats.Handshake_data.HandshakeType_ClientHello
                <:
                Bertie.Tls13formats.Handshake_data.t_HandshakeType)
            <:
            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
      let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 1uy 0uy in
      let next:usize = sz 0 in
      let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_eq ver
              (Bertie.Tls13utils.impl__Bytes__slice_range ch
                  ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 2 <: usize }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let next:usize = next +! sz 2 in
      let crand:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range ch
          ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 32 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
      in
      let next:usize = next +! sz 32 in
      let| sidlen:usize =
        Core.Result.impl__map_err (Bertie.Tls13utils.length_u8_encoded (ch.[ {
                    Core.Ops.Range.f_start = next;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
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
      let| cslen:usize =
        Core.Result.impl__map_err (Bertie.Tls13crypto.impl__Algorithms__check ciphersuite
              (Bertie.Tls13utils.impl__Bytes__raw_slice ch
                  ({
                      Core.Ops.Range.f_start = next;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let next:usize = next +! cslen in
      let| _:Prims.unit =
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
          Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
        | Core.Result.Result_Err _ ->
          Core.Result.impl__map_err (invalid_compression_list ()
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
      in
      let next:usize = next +! sz 2 in
      let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_length_encoding_u16 (Bertie.Tls13utils.impl__Bytes__slice_range
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
          (Core.Convert.f_from <: u8 -> u8)
      in
      let next:usize = next +! sz 2 in
      let| exts:t_Extensions =
        Core.Result.impl__map_err (check_extensions ciphersuite
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
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
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
      Core.Result.t_Result
        (Core.Result.t_Result
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize) u8) u8)
