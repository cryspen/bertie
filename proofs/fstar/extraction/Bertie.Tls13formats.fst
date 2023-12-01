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

let impl__ContentType__as_u8 (self: t_ContentType) : u8 =
  match self with
  | ContentType_Invalid  -> 0uy
  | ContentType_ChangeCipherSpec  -> 20uy
  | ContentType_Alert  -> 21uy
  | ContentType_Handshake  -> 22uy
  | ContentType_ApplicationData  -> 23uy

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

let v_LABEL_EXT_BINDER: t_Array u8 (sz 10) =
  let list = [101uy; 120uy; 116uy; 32uy; 98uy; 105uy; 110uy; 100uy; 101uy; 114uy] in
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

let alert_description (t: t_AlertDescription) : u8 =
  match t with
  | AlertDescription_CloseNotify  -> 0uy
  | AlertDescription_UnexpectedMessage  -> 10uy
  | AlertDescription_BadRecordMac  -> 20uy
  | AlertDescription_RecordOverflow  -> 22uy
  | AlertDescription_HandshakeFailure  -> 40uy
  | AlertDescription_BadCertificate  -> 42uy
  | AlertDescription_UnsupportedCertificate  -> 43uy
  | AlertDescription_CertificateRevoked  -> 44uy
  | AlertDescription_CertificateExpired  -> 45uy
  | AlertDescription_CertificateUnknown  -> 46uy
  | AlertDescription_IllegalParameter  -> 47uy
  | AlertDescription_UnknownCa  -> 48uy
  | AlertDescription_AccessDenied  -> 49uy
  | AlertDescription_DecodeError  -> 50uy
  | AlertDescription_DecryptError  -> 51uy
  | AlertDescription_ProtocolVersion  -> 70uy
  | AlertDescription_InsufficientSecurity  -> 71uy
  | AlertDescription_InternalError  -> 80uy
  | AlertDescription_InappropriateFallback  -> 86uy
  | AlertDescription_UserCanceled  -> 90uy
  | AlertDescription_MissingExtension  -> 109uy
  | AlertDescription_UnsupportedExtension  -> 110uy
  | AlertDescription_UnrecognizedName  -> 112uy
  | AlertDescription_BadCertificateStatusResponse  -> 113uy
  | AlertDescription_UnknownPskIdentity  -> 115uy
  | AlertDescription_CertificateRequired  -> 116uy
  | AlertDescription_NoApplicationProtocol  -> 120uy

let alert_level (t: t_AlertLevel) : u8 =
  match t with
  | AlertLevel_Warning  -> 1uy
  | AlertLevel_Fatal  -> 2uy

let hs_type (t: t_HandshakeType) : u8 =
  match t with
  | HandshakeType_ClientHello  -> 1uy
  | HandshakeType_ServerHello  -> 2uy
  | HandshakeType_NewSessionTicket  -> 4uy
  | HandshakeType_EndOfEarlyData  -> 5uy
  | HandshakeType_EncryptedExtensions  -> 8uy
  | HandshakeType_Certificate  -> 11uy
  | HandshakeType_CertificateRequest  -> 13uy
  | HandshakeType_CertificateVerify  -> 15uy
  | HandshakeType_Finished  -> 20uy
  | HandshakeType_KeyUpdate  -> 24uy
  | HandshakeType_MessageHash  -> 254uy

let application_data_instead_of_handshake: Core.Result.t_Result Prims.unit u8 =
  Core.Result.Result_Err Bertie.Tls13utils.v_APPLICATION_DATA_INSTEAD_OF_HANDSHAKE
  <:
  Core.Result.t_Result Prims.unit u8

let invalid_compression_list: Core.Result.t_Result Prims.unit u8 =
  Core.Result.Result_Err Bertie.Tls13utils.v_INVALID_COMPRESSION_LIST
  <:
  Core.Result.t_Result Prims.unit u8

let protocol_version_alert: Core.Result.t_Result Prims.unit u8 =
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

let impl__ContentType__try_from_u8 (t: u8) : Core.Result.t_Result t_ContentType u8 =
  match t with
  | 0uy -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)
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
  | _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)

let get_alert_description (t: u8) : Core.Result.t_Result t_AlertDescription u8 =
  match t with
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
  | _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)

let get_alert_level (t: u8) : Core.Result.t_Result t_AlertLevel u8 =
  match t with
  | 1uy ->
    Core.Result.Result_Ok (AlertLevel_Warning <: t_AlertLevel)
    <:
    Core.Result.t_Result t_AlertLevel u8
  | 2uy ->
    Core.Result.Result_Ok (AlertLevel_Fatal <: t_AlertLevel) <: Core.Result.t_Result t_AlertLevel u8
  | _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)

let get_hs_type (t: u8) : Core.Result.t_Result t_HandshakeType u8 =
  match t with
  | 1uy ->
    Core.Result.Result_Ok (HandshakeType_ClientHello <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 2uy ->
    Core.Result.Result_Ok (HandshakeType_ServerHello <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 4uy ->
    Core.Result.Result_Ok (HandshakeType_NewSessionTicket <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 5uy ->
    Core.Result.Result_Ok (HandshakeType_EndOfEarlyData <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 8uy ->
    Core.Result.Result_Ok (HandshakeType_EncryptedExtensions <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 11uy ->
    Core.Result.Result_Ok (HandshakeType_Certificate <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 13uy ->
    Core.Result.Result_Ok (HandshakeType_CertificateRequest <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 15uy ->
    Core.Result.Result_Ok (HandshakeType_CertificateVerify <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 20uy ->
    Core.Result.Result_Ok (HandshakeType_Finished <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 24uy ->
    Core.Result.Result_Ok (HandshakeType_KeyUpdate <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 254uy ->
    Core.Result.Result_Ok (HandshakeType_MessageHash <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)

let invalid_compression_method_alert: Core.Result.t_Result Prims.unit u8 =
  Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_DECODE_ERROR

let merge_opts
      (#v_T: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized v_T)
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
  | _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)

let unsupported_cipher_alert: Core.Result.t_Result Prims.unit u8 =
  Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let check_psk_shared_key (v__algs: Bertie.Tls13crypto.t_Algorithms) (ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len_id:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 ch
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist111:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist111)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) usize
      in
      let* len_tkt:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                    ch
                    ({
                        Core.Ops.Range.f_start = sz 2;
                        Core.Ops.Range.f_end = sz 2 +! len_id <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist112:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist112)
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
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
                      ch
                      ({
                          Core.Ops.Range.f_start = sz 2 +! len_id <: usize;
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
            let* hoist113:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Prims.unit u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist113)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_u8_encoded_full (Bertie.Tls13utils.impl__Bytes__slice_range
                      ch
                      ({
                          Core.Ops.Range.f_start = sz 4 +! len_id <: usize;
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
            let* hoist114:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Prims.unit u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist114)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (if
            (((Bertie.Tls13utils.impl__Bytes__len ch <: usize) -! sz 6 <: usize) -! len_id <: usize) <>.
            sz 32
          then Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)
          else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
          (Core.Result.t_Result Prims.unit u8)
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8))
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
          (Core.Result.t_Result Prims.unit u8))

let key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist118:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist115:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist115)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* hoist117:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 gx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist116:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist116)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let ks:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat hoist118 hoist117 in
      let* hoist121:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 ks
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist120:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist120)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist122:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_u16 hoist121
      in
      let hoist123:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist122
      in
      let* hoist124:Bertie.Tls13utils.t_Bytes =
        match hoist123 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist119:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist119)
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
      (let hoist125:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 51uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist124
        in
        Core.Result.Result_Ok hoist125 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let server_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist129:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist126:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist126)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* hoist128:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 gx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist127:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist127)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let ks:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat hoist129 hoist128 in
      let* hoist131:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 ks
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
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
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist132:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 51uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist131
        in
        Core.Result.Result_Ok hoist132 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let server_name (sn: Bertie.Tls13utils.t_Bytes) : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist136:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 sn
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist135:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist135)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist137:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat (Core.Convert.f_from (let list = [0uy] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list list)
            <:
            Bertie.Tls13utils.t_Bytes)
          hoist136
      in
      let hoist138:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_u16 hoist137
      in
      let hoist139:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist138
      in
      let* hoist140:Bertie.Tls13utils.t_Bytes =
        match hoist139 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist134:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist134)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist141:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_u16 hoist140
      in
      let hoist142:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist141
      in
      let* hoist143:Bertie.Tls13utils.t_Bytes =
        match hoist142 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist133:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist133)
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
      (let hoist144:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Core.Convert.f_from (let list = [0uy; 0uy] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                  Rust_primitives.Hax.array_of_list list)
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist143
        in
        Core.Result.Result_Ok hoist144 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let server_pre_shared_key (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist146:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 (Bertie.Tls13utils.bytes2 0uy
                    0uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist145:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist145)
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
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 41uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist146
        in
        Core.Result.Result_Ok hoist147 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let server_supported_version (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist149:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 (Bertie.Tls13utils.bytes2 3uy
                    4uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
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
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist150:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 43uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist149
        in
        Core.Result.Result_Ok hoist150 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist154:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
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
        Bertie.Tls13utils.encode_u16 hoist154
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
      let hoist158:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_u16 hoist157
      in
      let hoist159:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist158
      in
      let* hoist160:Bertie.Tls13utils.t_Bytes =
        match hoist159 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist151:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist151)
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
      (let hoist161:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 13uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist160
        in
        Core.Result.Result_Ok hoist161 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let supported_groups (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist165:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist164:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist164)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist166:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_u16 hoist165
      in
      let hoist167:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist166
      in
      let* hoist168:Bertie.Tls13utils.t_Bytes =
        match hoist167 with
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
      let hoist169:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_u16 hoist168
      in
      let hoist170:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist169
      in
      let* hoist171:Bertie.Tls13utils.t_Bytes =
        match hoist170 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist162:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist162)
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
      (let hoist172:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 10uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist171
        in
        Core.Result.Result_Ok hoist172 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let ecdsa_signature (sv: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.impl__Bytes__len sv <: usize) <>. sz 64 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)
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
            let r:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat b0 r in
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
        let* hoist175:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u8 r
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
        let hoist176:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat b2 hoist175
        in
        let hoist179:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat hoist176 b2
        in
        let* hoist178:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u8 s
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist177:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist177)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
        in
        let hoist180:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat hoist179 hoist178
        in
        let hoist181:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
          Bertie.Tls13utils.encode_u8 hoist180
        in
        let hoist182:Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
          Core.Ops.Try_trait.f_branch hoist181
        in
        let* hoist183:Bertie.Tls13utils.t_Bytes =
          match hoist182 with
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
        Core.Ops.Control_flow.ControlFlow_Continue
        (let hoist184:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__concat b1 hoist183
          in
          Core.Result.Result_Ok hoist184 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let pre_shared_key
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (session_ticket: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist187:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 session_ticket
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist186:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist186)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
      in
      let hoist188:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat hoist187
          (Bertie.Tls13utils.impl__U32__to_be_bytes (Core.Convert.f_from 4294967295ul
                <:
                Bertie.Tls13utils.t_U32)
            <:
            Bertie.Tls13utils.t_Bytes)
      in
      let hoist189:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_u16 hoist188
      in
      let hoist190:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist189
      in
      let* identities:Bertie.Tls13utils.t_Bytes =
        match hoist190 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist185:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist185)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
      in
      let* hoist193:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u8 (Bertie.Tls13crypto.zero_key (Bertie.Tls13crypto.impl__Algorithms__hash
                        algs
                      <:
                      Bertie.Tls13crypto.t_HashAlgorithm)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist192:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist192)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
      in
      let hoist194:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_u16 hoist193
      in
      let hoist195:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist194
      in
      let* binders:Bertie.Tls13utils.t_Bytes =
        match hoist195 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist191:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist191)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
      in
      let* hoist197:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 (Bertie.Tls13utils.impl__Bytes__concat
                    identities
                    binders
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist196:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist196)
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
            hoist197
        in
        Core.Result.Result_Ok
        (ext, Bertie.Tls13utils.impl__Bytes__len binders <: (Bertie.Tls13utils.t_Bytes & usize))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8))

let psk_key_exchange_modes: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist200:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u8 (Bertie.Tls13utils.bytes1 1uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist199:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist199)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist201:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_u16 hoist200
      in
      let hoist202:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist201
      in
      let* hoist203:Bertie.Tls13utils.t_Bytes =
        match hoist202 with
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
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist204:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 45uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist203
        in
        Core.Result.Result_Ok hoist204 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let supported_versions: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist207:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u8 (Core.Convert.f_from (let list =
                        [3uy; 4uy]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                      Rust_primitives.Hax.array_of_list list)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist206:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist206)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist208:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_u16 hoist207
      in
      let hoist209:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist208
      in
      let* hoist210:Bertie.Tls13utils.t_Bytes =
        match hoist209 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist205:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist205)
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
      (let hoist211:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Core.Convert.f_from (let list = [0uy; 43uy] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                  Rust_primitives.Hax.array_of_list list)
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist210
        in
        Core.Result.Result_Ok hoist211 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let check_psk_key_exchange_modes (client_hello: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_u8_encoded_full client_hello
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist223:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist223)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 1uy <: Bertie.Tls13utils.t_Bytes)
          (Bertie.Tls13utils.impl__Bytes__slice_range client_hello
              ({ Core.Ops.Range.f_start = sz 1; Core.Ops.Range.f_end = sz 2 }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Bertie.Tls13utils.t_Bytes))
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

let check_server_key_share (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist226:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist225:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist225)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist227:Core.Result.t_Result Prims.unit u8 =
        Bertie.Tls13utils.check_eq hoist226
          (Bertie.Tls13utils.impl__Bytes__slice_range b
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Bertie.Tls13utils.t_Bytes)
      in
      let hoist228:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Prims.unit =
        Core.Ops.Try_trait.f_branch hoist227
      in
      let* _:Prims.unit =
        match hoist228 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist224:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist224)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
                    b
                    ({
                        Core.Ops.Range.f_start = sz 2;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist229:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist229)
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
        (Bertie.Tls13utils.impl__Bytes__slice_range b
            ({
                Core.Ops.Range.f_start = sz 4;
                Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
              }
              <:
              Core.Ops.Range.t_Range usize))
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let check_server_name (ext: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full ext
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist230:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist230)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 0uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
                (Bertie.Tls13utils.impl__Bytes__slice_range ext
                    ({ Core.Ops.Range.f_start = sz 2; Core.Ops.Range.f_end = sz 3 }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist231:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist231)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
                    ext
                    ({
                        Core.Ops.Range.f_start = sz 3;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ext <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist232:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist232)
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
        (Bertie.Tls13utils.impl__Bytes__slice_range ext
            ({
                Core.Ops.Range.f_start = sz 5;
                Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ext <: usize
              }
              <:
              Core.Ops.Range.t_Range usize))
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let check_server_psk_shared_key
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes2 0uy 0uy <: Bertie.Tls13utils.t_Bytes) b

let check_server_supported_version
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes2 3uy 4uy <: Bertie.Tls13utils.t_Bytes) b

let check_server_extension (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                    b
                    ({
                        Core.Ops.Range.f_start = sz 2;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist233:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist233)
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
                    (Bertie.Tls13utils.impl__Bytes__slice_range b
                        ({
                            Core.Ops.Range.f_start = sz 4;
                            Core.Ops.Range.f_end = sz 4 +! len <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize)
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist234:Rust_primitives.Hax.t_Never =
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
                    (Bertie.Tls13utils.impl__Bytes__slice_range b
                        ({
                            Core.Ops.Range.f_start = sz 4;
                            Core.Ops.Range.f_end = sz 4 +! len <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize)
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist235:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
                  )
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist235)
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
                    (Bertie.Tls13utils.impl__Bytes__slice_range b
                        ({
                            Core.Ops.Range.f_start = sz 4;
                            Core.Ops.Range.f_end = sz 4 +! len <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize)
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist236:Rust_primitives.Hax.t_Never =
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

let parse_ecdsa_signature (sig: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.impl__Bytes__len sig <: usize) <. sz 4 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)
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
            let* hoist237:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist237)
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
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_u8_encoded_full (Bertie.Tls13utils.impl__Bytes__slice_range
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
            let* hoist238:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist238)
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
            let* hoist239:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist239)
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
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.decode_u8_length (Bertie.Tls13utils.impl__Bytes__slice_range
                      sig
                      ({
                          Core.Ops.Range.f_start = sz 3;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sig <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result usize u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist240:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist240)
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
            let* hoist241:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist241)
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
              let* hoist242:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist242)
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
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_u8_encoded_full (Bertie.Tls13utils.impl__Bytes__slice_range
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
              let* hoist243:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist243)
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

let check_signature_algorithms
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full ch
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist247:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist247)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      let* hoist249:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist248:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist248)
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
      (Bertie.Tls13utils.check_mem hoist249
          (Bertie.Tls13utils.impl__Bytes__slice_range ch
              ({
                  Core.Ops.Range.f_start = sz 2;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Bertie.Tls13utils.t_Bytes))
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

let check_supported_groups (algs: Bertie.Tls13crypto.t_Algorithms) (ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full ch
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist250:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist250)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      let* hoist252:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist251:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist251)
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
      (Bertie.Tls13utils.check_mem hoist252
          (Bertie.Tls13utils.impl__Bytes__slice_range ch
              ({
                  Core.Ops.Range.f_start = sz 2;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Bertie.Tls13utils.t_Bytes))
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

let check_supported_versions (client_hello: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_u8_encoded_full client_hello
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist253:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist253)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13utils.check_mem (Core.Convert.f_into (let list = [3uy; 4uy] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list list)
            <:
            Bertie.Tls13utils.t_Bytes)
          (Bertie.Tls13utils.impl__Bytes__slice_range client_hello
              ({
                  Core.Ops.Range.f_start = sz 1;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len client_hello <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Bertie.Tls13utils.t_Bytes))
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

type t_Extensions = {
  f_sni:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_key_share:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_ticket:Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
  f_binder:Core.Option.t_Option Bertie.Tls13utils.t_Bytes
}

let check_server_extensions (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len, out:(usize &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (check_server_extension algs b
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist296:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist296)
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
      if len =. (Bertie.Tls13utils.impl__Bytes__len b <: usize)
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
                  (Bertie.Tls13utils.impl__Bytes__slice_range b
                      ({
                          Core.Ops.Range.f_start = len;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist297:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist297)
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

let find_key_share (g ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.impl__Bytes__len ch <: usize) <. sz 4 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      else
        if
          Bertie.Tls13utils.eq g
            (Bertie.Tls13utils.impl__Bytes__slice_range ch
                ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Bertie.Tls13utils.t_Bytes)
          <:
          bool
        then
          let* len:usize =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                        ch
                        ({
                            Core.Ops.Range.f_start = sz 2;
                            Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize)
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result usize u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist298:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist298)
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
            (Bertie.Tls13utils.impl__Bytes__slice_range ch
                ({ Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 4 +! len <: usize }
                  <:
                  Core.Ops.Range.t_Range usize))
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        else
          let* len:usize =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                        ch
                        ({
                            Core.Ops.Range.f_start = sz 2;
                            Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize)
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result usize u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist299:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist299)
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
              (Bertie.Tls13utils.impl__Bytes__slice_range ch
                  ({
                      Core.Ops.Range.f_start = sz 4 +! len <: usize;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Bertie.Tls13utils.t_Bytes))
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let check_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full ch
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist300:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist300)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
      in
      let* hoist302:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist301:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist301)
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
      (find_key_share hoist302
          (Bertie.Tls13utils.impl__Bytes__slice_range ch
              ({
                  Core.Ops.Range.f_start = sz 2;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Bertie.Tls13utils.t_Bytes))
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let check_extension (algs: Bertie.Tls13crypto.t_Algorithms) (bytes: Bertie.Tls13utils.t_Bytes)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                    bytes
                    ({
                        Core.Ops.Range.f_start = sz 2;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len bytes <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist303:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (usize & t_Extensions) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist303)
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
        let* hoist305:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (check_server_name (Bertie.Tls13utils.impl__Bytes__slice_range
                      bytes
                      ({
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist304:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_Extensions) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist304)
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
        (let hoist306:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
            Core.Option.Option_Some hoist305 <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
          in
          let hoist307:t_Extensions =
            {
              f_sni = hoist306;
              f_key_share
              =
              Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
              f_ticket = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
              f_binder = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
            }
            <:
            t_Extensions
          in
          let hoist308:(usize & t_Extensions) = sz 4 +! len, hoist307 <: (usize & t_Extensions) in
          Core.Result.Result_Ok hoist308 <: Core.Result.t_Result (usize & t_Extensions) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_Extensions) u8)
          (Core.Result.t_Result (usize & t_Extensions) u8)
      | 0uy, 45uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_psk_key_exchange_modes (Bertie.Tls13utils.impl__Bytes__slice_range
                      bytes
                      ({
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist309:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_Extensions) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist309)
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
            Core.Ops.Try_trait.f_branch (check_supported_versions (Bertie.Tls13utils.impl__Bytes__slice_range
                      bytes
                      ({
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist310:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_Extensions) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist310)
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
                  (Bertie.Tls13utils.impl__Bytes__slice_range bytes
                      ({
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist311:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_Extensions) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist311)
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
                  (Bertie.Tls13utils.impl__Bytes__slice_range bytes
                      ({
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist312:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_Extensions) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist312)
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
              (Bertie.Tls13utils.impl__Bytes__slice_range bytes
                  ({ Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 4 +! len <: usize }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Bertie.Tls13utils.t_Bytes)
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
                  (Bertie.Tls13utils.impl__Bytes__slice_range bytes
                      ({
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist313:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_Extensions) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist313)
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

let merge_extensions (e1 e2: t_Extensions) : Core.Result.t_Result t_Extensions u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist321:Core.Option.t_Option
      Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts e1.f_sni e2.f_sni
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist314:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_Extensions u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist314)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      let* hoist320:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts e1.f_key_share e2.f_key_share
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist315:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_Extensions u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist315)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      let* hoist319:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts e1.f_ticket e2.f_ticket
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist316:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_Extensions u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist316)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      let* hoist318:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts e1.f_binder e2.f_binder
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist317:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_Extensions u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist317)
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
      (let hoist322:t_Extensions =
          { f_sni = hoist321; f_key_share = hoist320; f_ticket = hoist319; f_binder = hoist318 }
          <:
          t_Extensions
        in
        Core.Result.Result_Ok hoist322 <: Core.Result.t_Result t_Extensions u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
        (Core.Result.t_Result t_Extensions u8))

let check_handshake_record (p: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.impl__Bytes__len p <: usize) <. sz 5 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
      else
        let ty:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.bytes1 (impl__ContentType__as_u8 (ContentType_Handshake <: t_ContentType
                )
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
              (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8) Prims.unit
          | Core.Result.Result_Err _ ->
            match
              Core.Ops.Try_trait.f_branch (application_data_instead_of_handshake
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist323:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist323)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8) Prims.unit
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8) Prims.unit
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
              (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8) Prims.unit
          | Core.Result.Result_Err _ ->
            match
              Core.Ops.Try_trait.f_branch (protocol_version_alert
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist324:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist324)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8) Prims.unit
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8) Prims.unit
        in
        let* len:usize =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                      p
                      ({
                          Core.Ops.Range.f_start = sz 3;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len p <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result usize u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist325:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist325)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8) usize
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8) usize
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok
          ((Bertie.Tls13utils.HandshakeData
              (Bertie.Tls13utils.impl__Bytes__slice_range p
                  ({ Core.Ops.Range.f_start = sz 5; Core.Ops.Range.f_end = sz 5 +! len <: usize }
                    <:
                    Core.Ops.Range.t_Range usize))
              <:
              Bertie.Tls13utils.t_HandshakeData),
            sz 5 +! len
            <:
            (Bertie.Tls13utils.t_HandshakeData & usize))
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8))

let encrypted_extensions (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ty:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes1 (hs_type (HandshakeType_EncryptedExtensions <: t_HandshakeType)
            <:
            u8)
      in
      let* hoist328:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 (Bertie.Tls13utils.impl__Bytes__new
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist327:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist327)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let hoist329:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes3 hoist328
      in
      let hoist330:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist329
      in
      let* hoist331:Bertie.Tls13utils.t_Bytes =
        match hoist330 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist326:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist326)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist332:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat ty hoist331 in
        let hoist333:Bertie.Tls13utils.t_HandshakeData =
          Bertie.Tls13utils.HandshakeData hoist332 <: Bertie.Tls13utils.t_HandshakeData
        in
        Core.Result.Result_Ok hoist333 <: Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8))

let get_first_handshake_message (p: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
      u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.impl__Bytes__len p.Bertie.Tls13utils._0 <: usize) <. sz 4 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
      else
        let* len:usize =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes3 (Bertie.Tls13utils.impl__Bytes__slice_range
                      p.Bertie.Tls13utils._0
                      ({
                          Core.Ops.Range.f_start = sz 1;
                          Core.Ops.Range.f_end
                          =
                          Bertie.Tls13utils.impl__Bytes__len p.Bertie.Tls13utils._0 <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result usize u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist334:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist334)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8) usize
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8) usize
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let msg:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__slice_range p.Bertie.Tls13utils._0
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 4 +! len <: usize }
                <:
                Core.Ops.Range.t_Range usize)
          in
          let rest:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__slice_range p.Bertie.Tls13utils._0
              ({
                  Core.Ops.Range.f_start = sz 4 +! len <: usize;
                  Core.Ops.Range.f_end
                  =
                  Bertie.Tls13utils.impl__Bytes__len p.Bertie.Tls13utils._0 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
          in
          Core.Result.Result_Ok
          ((Bertie.Tls13utils.HandshakeData msg <: Bertie.Tls13utils.t_HandshakeData),
            (Bertie.Tls13utils.HandshakeData rest <: Bertie.Tls13utils.t_HandshakeData)
            <:
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8))

let get_handshake_record (p: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hd, len:(Bertie.Tls13utils.t_HandshakeData &
        usize) =
        match
          Core.Ops.Try_trait.f_branch (check_handshake_record p
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist335:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist335)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            (Bertie.Tls13utils.t_HandshakeData & usize)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            (Bertie.Tls13utils.t_HandshakeData & usize)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (if len =. (Bertie.Tls13utils.impl__Bytes__len p <: usize)
        then Core.Result.Result_Ok hd <: Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8
        else Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8))

let handshake_record (p: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let Bertie.Tls13utils.HandshakeData p:Bertie.Tls13utils.t_HandshakeData
      =
        p
      in
      let ty:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes1 (impl__ContentType__as_u8 (ContentType_Handshake <: t_ContentType)
            <:
            u8)
      in
      let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
      let* hoist337:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 p
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist336:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist336)
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
      (let hoist338:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat ty ver
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist337
        in
        Core.Result.Result_Ok hoist338 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let parse_encrypted_extensions
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (ee: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let Bertie.Tls13utils.HandshakeData ee:Bertie.Tls13utils.t_HandshakeData
      =
        ee
      in
      let ty:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes1 (hs_type (HandshakeType_EncryptedExtensions <: t_HandshakeType)
            <:
            u8)
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq ty
                (Bertie.Tls13utils.impl__Bytes__slice_range ee
                    ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist339:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist339)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13utils.check_lbytes3_full (Bertie.Tls13utils.impl__Bytes__slice_range ee
              ({
                  Core.Ops.Range.f_start = sz 1;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ee <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Bertie.Tls13utils.t_Bytes))
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

let set_client_hello_binder
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (binder: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (client_hello: Bertie.Tls13utils.t_HandshakeData)
      (trunc_len: Core.Option.t_Option usize)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  let Bertie.Tls13utils.HandshakeData ch:Bertie.Tls13utils.t_HandshakeData = client_hello in
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
      (Bertie.Tls13utils.HandshakeData
        (Bertie.Tls13utils.impl__Bytes__update_slice ch trunc_len m (sz 0) hlen)
        <:
        Bertie.Tls13utils.t_HandshakeData)
      <:
      Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8
    else Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)
  | Core.Option.Option_None , Core.Option.Option_None  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.HandshakeData ch <: Bertie.Tls13utils.t_HandshakeData)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8
  | _, _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)

let handshake_message (ty: t_HandshakeType) (v_by: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist341:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes3 v_by
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist340:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist340)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist342:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes1 (hs_type ty <: u8)
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist341
        in
        let hoist343:Bertie.Tls13utils.t_HandshakeData =
          Bertie.Tls13utils.handshake_data hoist342
        in
        Core.Result.Result_Ok hoist343 <: Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8))

let certificate_verify (algs: Bertie.Tls13crypto.t_Algorithms) (cv: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* sv:Bertie.Tls13utils.t_Bytes =
        match algs.Bertie.Tls13crypto.f_signature with
        | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
          Core.Ops.Control_flow.ControlFlow_Continue (Core.Clone.f_clone cv)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
          if (Bertie.Tls13utils.impl__Bytes__len cv <: usize) <>. sz 64
          then
            let* hoist344:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed
                      <:
                      u8)
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist344)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
          else
            (match
                Core.Ops.Try_trait.f_branch (ecdsa_signature cv
                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              with
              | Core.Ops.Control_flow.ControlFlow_Break residual ->
                let* hoist345:Rust_primitives.Hax.t_Never =
                  Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                      <:
                      Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
                in
                Core.Ops.Control_flow.ControlFlow_Continue
                (Rust_primitives.Hax.never_to_any hoist345)
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
                  Bertie.Tls13utils.t_Bytes
              | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                Core.Ops.Control_flow.ControlFlow_Continue v_val
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
                  Bertie.Tls13utils.t_Bytes)
        | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
                <:
                Rust_primitives.Hax.t_Never))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* hoist349:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist346:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist346)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* hoist348:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 sv
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist347:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist347)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let sig:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat hoist349 hoist348
        in
        handshake_message (HandshakeType_CertificateVerify <: t_HandshakeType) sig)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8))

let client_hello
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (cr gx sn: Bertie.Tls13utils.t_Bytes)
      (session_ticket: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ver:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes2 3uy 3uy
      in
      let* sid:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u8 (Bertie.Tls13utils.impl__Bytes__zeroes
                    (sz 32)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist350:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist350)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* hoist353:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__ciphersuite algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist352:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist352)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist354:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.encode_u16 hoist353
      in
      let hoist355:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist354
      in
      let* cip:Bertie.Tls13utils.t_Bytes =
        match hoist355 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist351:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist351)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 1uy 0uy in
      let* sn:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (server_name sn
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist356:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist356)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* sv:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_versions
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist357:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist357)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* sg:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_groups algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist358:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist358)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* sa:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (signature_algorithms algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist359:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist359)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* ks:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (key_shares algs gx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist360:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist360)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let exts:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat
                  (Bertie.Tls13utils.impl__Bytes__concat sn sv <: Bertie.Tls13utils.t_Bytes)
                  sg
                <:
                Bertie.Tls13utils.t_Bytes)
              sa
            <:
            Bertie.Tls13utils.t_Bytes)
          ks
      in
      let trunc_len:usize = sz 0 in
      let* exts, trunc_len:(Bertie.Tls13utils.t_Bytes & usize) =
        match
          Bertie.Tls13crypto.impl__Algorithms__psk_mode algs, session_ticket
          <:
          (bool & Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        with
        | true, Core.Option.Option_Some session_ticket ->
          let* pskm:Bertie.Tls13utils.t_Bytes =
            match
              Core.Ops.Try_trait.f_branch (psk_key_exchange_modes
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist361:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist361)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
                Bertie.Tls13utils.t_Bytes
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
                Bertie.Tls13utils.t_Bytes
          in
          let* psk, len:(Bertie.Tls13utils.t_Bytes & usize) =
            match
              Core.Ops.Try_trait.f_branch (pre_shared_key algs session_ticket
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist362:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist362)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
                (Bertie.Tls13utils.t_Bytes & usize)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
                (Bertie.Tls13utils.t_Bytes & usize)
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let exts:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat exts pskm
                  <:
                  Bertie.Tls13utils.t_Bytes)
                psk
            in
            let trunc_len:usize = len in
            exts, trunc_len <: (Bertie.Tls13utils.t_Bytes & usize))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            (Bertie.Tls13utils.t_Bytes & usize)
        | false, Core.Option.Option_None  ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (exts, trunc_len <: (Bertie.Tls13utils.t_Bytes & usize))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            (Bertie.Tls13utils.t_Bytes & usize)
        | _ ->
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_PSK_MODE_MISMATCH

                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist363:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue
            (exts, trunc_len <: (Bertie.Tls13utils.t_Bytes & usize))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              (Bertie.Tls13utils.t_Bytes & usize)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue
            (exts, trunc_len <: (Bertie.Tls13utils.t_Bytes & usize))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              (Bertie.Tls13utils.t_Bytes & usize)
      in
      let* hoist366:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 exts
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist365:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist365)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist367:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat
                  (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat ver
                          cr
                        <:
                        Bertie.Tls13utils.t_Bytes)
                      sid
                    <:
                    Bertie.Tls13utils.t_Bytes)
                  cip
                <:
                Bertie.Tls13utils.t_Bytes)
              comp
            <:
            Bertie.Tls13utils.t_Bytes)
          hoist366
      in
      let hoist368:Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
        handshake_message (HandshakeType_ClientHello <: t_HandshakeType) hoist367
      in
      let hoist369:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_HandshakeData =
        Core.Ops.Try_trait.f_branch hoist368
      in
      let* ch:Bertie.Tls13utils.t_HandshakeData =
        match hoist369 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist364:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist364)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            Bertie.Tls13utils.t_HandshakeData
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok (ch, trunc_len <: (Bertie.Tls13utils.t_HandshakeData & usize))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8))

let finished (v__algs: Bertie.Tls13crypto.t_Algorithms) (vd: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  handshake_message (HandshakeType_Finished <: t_HandshakeType) vd

let server_certificate (v__algs: Bertie.Tls13crypto.t_Algorithms) (cert: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* creq:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u8 (Bertie.Tls13utils.impl__Bytes__new
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist370:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist370)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* crt:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes3 cert
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist371:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist371)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* ext:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 (Bertie.Tls13utils.impl__Bytes__new
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist372:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist372)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* crts:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes3 (Bertie.Tls13utils.impl__Bytes__concat
                    crt
                    ext
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist373:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist373)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (handshake_message (HandshakeType_Certificate <: t_HandshakeType)
          (Bertie.Tls13utils.impl__Bytes__concat creq crts <: Bertie.Tls13utils.t_Bytes))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8))

let server_hello (algs: Bertie.Tls13crypto.t_Algorithms) (sr sid gy: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ver:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes2 3uy 3uy
      in
      let* sid:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u8 sid
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist374:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist374)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* cip:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__ciphersuite algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist375:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist375)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 0uy in
      let* ks:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (server_key_shares algs gy
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist376:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist376)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* sv:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (server_supported_version algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist377:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist377)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let exts:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat ks sv in
      let* exts:Bertie.Tls13utils.t_Bytes =
        match Bertie.Tls13crypto.impl__Algorithms__psk_mode algs with
        | true ->
          let* hoist379:Bertie.Tls13utils.t_Bytes =
            match
              Core.Ops.Try_trait.f_branch (server_pre_shared_key algs
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist378:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist378)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
                Bertie.Tls13utils.t_Bytes
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
                Bertie.Tls13utils.t_Bytes
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist380:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__concat exts hoist379
            in
            hoist380)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | false ->
          Core.Ops.Control_flow.ControlFlow_Continue exts
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* hoist383:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 exts
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist382:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist382)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let hoist384:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat
                  (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat ver
                          sr
                        <:
                        Bertie.Tls13utils.t_Bytes)
                      sid
                    <:
                    Bertie.Tls13utils.t_Bytes)
                  cip
                <:
                Bertie.Tls13utils.t_Bytes)
              comp
            <:
            Bertie.Tls13utils.t_Bytes)
          hoist383
      in
      let hoist385:Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
        handshake_message (HandshakeType_ServerHello <: t_HandshakeType) hoist384
      in
      let hoist386:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_HandshakeData =
        Core.Ops.Try_trait.f_branch hoist385
      in
      let* sh:Bertie.Tls13utils.t_HandshakeData =
        match hoist386 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist381:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist381)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            Bertie.Tls13utils.t_HandshakeData
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok sh <: Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8))

let session_ticket (v__algs: Bertie.Tls13crypto.t_Algorithms) (tkt: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let lifetime:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__U32__to_be_bytes (Core.Convert.f_from 172800ul
            <:
            Bertie.Tls13utils.t_U32)
      in
      let age:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__U32__to_be_bytes (Core.Convert.f_from 9999ul
            <:
            Bertie.Tls13utils.t_U32)
      in
      let* nonce:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u8 (Bertie.Tls13utils.bytes1 1uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist387:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist387)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* stkt:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 tkt
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist388:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist388)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* hoist390:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 (Bertie.Tls13utils.impl__Bytes__new
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist389:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist389)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let grease_ext:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 90uy 90uy
            <:
            Bertie.Tls13utils.t_Bytes)
          hoist390
      in
      let* ext:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u16 grease_ext
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist391:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist391)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (handshake_message (HandshakeType_NewSessionTicket <: t_HandshakeType)
          (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat
                      (Bertie.Tls13utils.impl__Bytes__concat lifetime age
                        <:
                        Bertie.Tls13utils.t_Bytes)
                      nonce
                    <:
                    Bertie.Tls13utils.t_Bytes)
                  stkt
                <:
                Bertie.Tls13utils.t_Bytes)
              ext
            <:
            Bertie.Tls13utils.t_Bytes))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8))

let get_handshake_message (p: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* m1, p:(Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist392:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist392)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (if (Bertie.Tls13utils.handshake_data_len p <: usize) <>. sz 0
        then Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)
        else Core.Result.Result_Ok m1 <: Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8))

let get_handshake_message_ty (ty: t_HandshakeType) (p: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData m:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message p
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist393:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist393)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            Bertie.Tls13utils.t_HandshakeData
      in
      let tyb:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 (hs_type ty <: u8) in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq tyb
                (Bertie.Tls13utils.impl__Bytes__slice_range m
                    ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist394:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist394)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (Bertie.Tls13utils.HandshakeData
          (Bertie.Tls13utils.impl__Bytes__slice_range m
              ({
                  Core.Ops.Range.f_start = sz 4;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len m <: usize
                }
                <:
                Core.Ops.Range.t_Range usize))
          <:
          Bertie.Tls13utils.t_HandshakeData)
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8))

let get_handshake_messages2 (p: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
      u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* m1, p:(Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist395:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist395)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
      in
      let* m2, p:(Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist396:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist396)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (if (Bertie.Tls13utils.handshake_data_len p <: usize) <>. sz 0
        then Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)
        else
          Core.Result.Result_Ok
          (m1, m2 <: (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        (Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8))

let get_handshake_messages4 (p: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13utils.t_HandshakeData) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* m1, p:(Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist397:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist397)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
      in
      let* m2, p:(Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist398:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist398)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
      in
      let* m3, p:(Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist399:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist399)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
      in
      let* m4, p:(Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist400:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist400)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (if (Bertie.Tls13utils.handshake_data_len p <: usize) <>. sz 0
        then Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8)
        else
          Core.Result.Result_Ok
          (m1, m2, m3, m4
            <:
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData) u8)
        (Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData) u8))

let parse_certificate_verify
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (cv: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData cv:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message_ty (HandshakeType_CertificateVerify
                  <:
                  t_HandshakeType)
                cv
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist401:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist401)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_HandshakeData
      in
      let sa:Bertie.Tls13crypto.t_SignatureScheme =
        Bertie.Tls13crypto.impl__Algorithms__signature algs
      in
      let* hoist404:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
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
      let hoist405:Core.Result.t_Result Prims.unit u8 =
        Bertie.Tls13utils.check_eq hoist404
          (Bertie.Tls13utils.impl__Bytes__slice_range cv
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Bertie.Tls13utils.t_Bytes)
      in
      let hoist406:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Prims.unit =
        Core.Ops.Try_trait.f_branch hoist405
      in
      let* _:Prims.unit =
        match hoist406 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist402:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist402)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
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
          let* hoist407:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist407)
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

let parse_finished
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (fin: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData fin:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message_ty (HandshakeType_Finished
                  <:
                  t_HandshakeType)
                fin
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist408:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist408)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_HandshakeData
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok fin <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let parse_server_certificate
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (sc: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData sc:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message_ty (HandshakeType_Certificate
                  <:
                  t_HandshakeType)
                sc
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist409:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist409)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_HandshakeData
      in
      let next:usize = sz 0 in
      let* creqlen:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.decode_u8_length (Bertie.Tls13utils.impl__Bytes__slice_range
                    sc
                    ({
                        Core.Ops.Range.f_start = sz 4;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist410:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist410)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes3_full (Bertie.Tls13utils.impl__Bytes__slice_range
                    sc
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist411:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist411)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes3 (Bertie.Tls13utils.impl__Bytes__slice_range
                    sc
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist412:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist412)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                    sc
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist413:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist413)
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
      (sh: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData sh:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message_ty (HandshakeType_ServerHello
                  <:
                  t_HandshakeType)
                sh
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist414:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist414)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_HandshakeData
      in
      let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
      let* cip:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__Algorithms__ciphersuite algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist415:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist415)
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
            (Bertie.Tls13utils.impl__Bytes__slice_range sh
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
            Core.Ops.Try_trait.f_branch (protocol_version_alert
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist416:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist416)
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
        Bertie.Tls13utils.impl__Bytes__slice_range sh
          ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 32 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
      in
      let next:usize = next +! sz 32 in
      let* sidlen:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.decode_u8_length (Bertie.Tls13utils.impl__Bytes__slice_range
                    sh
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sh <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist417:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist417)
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
            (Bertie.Tls13utils.impl__Bytes__slice_range sh
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
            Core.Ops.Try_trait.f_branch (unsupported_cipher_alert
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist418:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist418)
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
            (Bertie.Tls13utils.impl__Bytes__slice_range sh
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
            Core.Ops.Try_trait.f_branch (invalid_compression_method_alert
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist419:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist419)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
                    sh
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sh <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist420:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist420)
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
                (Bertie.Tls13utils.impl__Bytes__slice_range sh
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sh <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist421:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist421)
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

let parse_session_ticket
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (tkt: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData tkt:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message_ty (HandshakeType_NewSessionTicket
                  <:
                  t_HandshakeType)
                tkt
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist422:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist422)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_HandshakeData
      in
      let* lifetime:Bertie.Tls13utils.t_U32 =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__U32__from_be_bytes (Bertie.Tls13utils.impl__Bytes__slice_range
                    tkt
                    ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 4 }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_U32 u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist423:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist423)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_U32
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_U32
      in
      let* age:Bertie.Tls13utils.t_U32 =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__U32__from_be_bytes (Bertie.Tls13utils.impl__Bytes__slice_range
                    tkt
                    ({ Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 8 }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_U32 u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist424:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist424)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_U32
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_U32
      in
      let* nonce_len:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.decode_u8_length (Bertie.Tls13utils.impl__Bytes__slice_range
                    tkt
                    ({
                        Core.Ops.Range.f_start = sz 8;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len tkt <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist425:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist425)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8) usize
      in
      let* stkt_len:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                    tkt
                    ({
                        Core.Ops.Range.f_start = sz 9 +! nonce_len <: usize;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len tkt <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist426:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist426)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8) usize
      in
      let stkt:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range tkt
          ({
              Core.Ops.Range.f_start = sz 11 +! nonce_len <: usize;
              Core.Ops.Range.f_end = (sz 11 +! nonce_len <: usize) +! stkt_len <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
                    tkt
                    ({
                        Core.Ops.Range.f_start = (sz 11 +! nonce_len <: usize) +! stkt_len <: usize;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len tkt <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist427:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist427)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
            Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (lifetime +! age, stkt <: (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8))

type t_Transcript =
  | Transcript : Bertie.Tls13crypto.t_HashAlgorithm -> Bertie.Tls13utils.t_HandshakeData
    -> t_Transcript

let check_extensions (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result t_Extensions u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len, out:(usize & t_Extensions) =
        match
          Core.Ops.Try_trait.f_branch (check_extension algs b
              <:
              Core.Result.t_Result (usize & t_Extensions) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist428:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_Extensions u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist428)
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
            Core.Ops.Try_trait.f_branch (check_extensions algs
                  (Bertie.Tls13utils.impl__Bytes__slice_range b
                      ({
                          Core.Ops.Range.f_start = len;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result t_Extensions u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist429:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_Extensions u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist429)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8) t_Extensions
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8) t_Extensions
        in
        Core.Ops.Control_flow.ControlFlow_Continue (merge_extensions out out_rest)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_Extensions u8)
          (Core.Result.t_Result t_Extensions u8))

let find_handshake_message
      (ty: t_HandshakeType)
      (payload: Bertie.Tls13utils.t_HandshakeData)
      (start: usize)
    : bool =
  if
    (Bertie.Tls13utils.impl__Bytes__len payload.Bertie.Tls13utils._0 <: usize) <.
    (start +! sz 4 <: usize)
  then false
  else
    match
      Bertie.Tls13utils.check_lbytes3 (Bertie.Tls13utils.impl__Bytes__slice_range payload
              .Bertie.Tls13utils._0
            ({
                Core.Ops.Range.f_start = start +! sz 1 <: usize;
                Core.Ops.Range.f_end
                =
                Bertie.Tls13utils.impl__Bytes__len payload.Bertie.Tls13utils._0 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Bertie.Tls13utils.t_Bytes)
    with
    | Core.Result.Result_Err _ -> false
    | Core.Result.Result_Ok len ->
      if
        Bertie.Tls13utils.eq1 (payload.Bertie.Tls13utils._0.[ start ] <: Bertie.Tls13utils.t_U8)
          (Core.Convert.f_from (hs_type ty <: u8) <: Bertie.Tls13utils.t_U8)
      then true
      else find_handshake_message ty payload ((start +! sz 4 <: usize) +! len <: usize)

let get_transcript_hash (tx: t_Transcript) : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      Transcript ha (Bertie.Tls13utils.HandshakeData txby):t_Transcript =
        tx
      in
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.impl__HashAlgorithm__hash ha txby
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist430:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist430)
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

let get_transcript_hash_truncated_client_hello
      (tx: t_Transcript)
      (ch: Bertie.Tls13utils.t_HandshakeData)
      (trunc_len: usize)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  let Transcript ha (Bertie.Tls13utils.HandshakeData tx):t_Transcript = tx in
  let Bertie.Tls13utils.HandshakeData ch:Bertie.Tls13utils.t_HandshakeData = ch in
  Bertie.Tls13crypto.impl__HashAlgorithm__hash ha
    (Bertie.Tls13utils.impl__Bytes__concat tx
        (Bertie.Tls13utils.impl__Bytes__slice_range ch
            ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = trunc_len }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Bertie.Tls13utils.t_Bytes)
      <:
      Bertie.Tls13utils.t_Bytes)

let parse_client_hello
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (client_hello: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData ch:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message_ty (HandshakeType_ClientHello
                  <:
                  t_HandshakeType)
                client_hello
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist431:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist431)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) Bertie.Tls13utils.t_HandshakeData
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
          let* hoist432:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist432)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.decode_u8_length (Bertie.Tls13utils.impl__Bytes__slice_range
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
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist433:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist433)
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
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist434:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist434)
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
            Core.Ops.Try_trait.f_branch (invalid_compression_list
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist435:Rust_primitives.Hax.t_Never =
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
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist435)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
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
          let* hoist436:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist436)
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
          let* hoist437:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist437)
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
            Bertie.Tls13utils.impl__Bytes__new,
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
            Bertie.Tls13utils.impl__Bytes__new,
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
        | _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8))
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

let transcript_add1 (tx: t_Transcript) (msg: Bertie.Tls13utils.t_HandshakeData) : t_Transcript =
  let Transcript ha tx:t_Transcript = tx in
  Transcript ha (Bertie.Tls13utils.handshake_concat tx msg) <: t_Transcript

let transcript_empty (ha: Bertie.Tls13crypto.t_HashAlgorithm) : t_Transcript =
  Transcript ha
    (Bertie.Tls13utils.HandshakeData Bertie.Tls13utils.impl__Bytes__new
      <:
      Bertie.Tls13utils.t_HandshakeData)
  <:
  t_Transcript
