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

let content_type (t: t_ContentType) : u8 =
  match t with
  | ContentType_Invalid  -> 0uy
  | ContentType_ChangeCipherSpec  -> 20uy
  | ContentType_Alert  -> 21uy
  | ContentType_Handshake  -> 22uy
  | ContentType_ApplicationData  -> 23uy

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

let get_content_type (t: u8) : Core.Result.t_Result t_ContentType u8 =
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

let ciphersuite (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  match
    Bertie.Tls13crypto.hash_alg algs, Bertie.Tls13crypto.aead_alg algs
    <:
    (Bertie.Tls13crypto.t_HashAlgorithm & Bertie.Tls13crypto.t_AeadAlgorithm)
  with
  | Bertie.Tls13crypto.HashAlgorithm_SHA256 , Bertie.Tls13crypto.AeadAlgorithm_Aes128Gcm  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 19uy 1uy)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Bertie.Tls13crypto.HashAlgorithm_SHA384 , Bertie.Tls13crypto.AeadAlgorithm_Aes256Gcm  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 19uy 2uy)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Bertie.Tls13crypto.HashAlgorithm_SHA256 , Bertie.Tls13crypto.AeadAlgorithm_Chacha20Poly1305  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 19uy 3uy)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let signature_algorithm (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  match Bertie.Tls13crypto.sig_alg algs with
  | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 8uy 4uy)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 4uy 3uy)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
    Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let supported_group (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  match Bertie.Tls13crypto.kem_alg algs with
  | Bertie.Tls13crypto.KemScheme_X25519  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 0uy 29uy)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Bertie.Tls13crypto.KemScheme_Secp256r1  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 0uy 23uy)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Bertie.Tls13crypto.KemScheme_X448  ->
    Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
  | Bertie.Tls13crypto.KemScheme_Secp384r1  ->
    Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
  | Bertie.Tls13crypto.KemScheme_Secp521r1  ->
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
          let* hoist133:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist133)
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
          let* hoist134:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist134)
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
            let* hoist135:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Prims.unit u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist135)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1_full (Bertie.Tls13utils.impl__Bytes__slice_range
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
            let* hoist136:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Prims.unit u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist136)
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

let check_psk_key_exchange_modes
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1_full ch
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist144:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist144)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 1uy <: Bertie.Tls13utils.t_Bytes)
          (Bertie.Tls13utils.impl__Bytes__slice_range ch
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
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist147:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist146:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist146)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist148:Core.Result.t_Result Prims.unit u8 =
        Bertie.Tls13utils.check_eq hoist147
          (Bertie.Tls13utils.impl__Bytes__slice_range b
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Bertie.Tls13utils.t_Bytes)
      in
      let hoist149:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Prims.unit =
        Core.Ops.Try_trait.f_branch hoist148
      in
      let* _:Prims.unit =
        match hoist149 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist145:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist145)
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
          let* hoist150:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist150)
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
          let* hoist151:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist151)
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
          let* hoist152:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist152)
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
          let* hoist153:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist153)
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
          let* hoist154:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist154)
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
              let* hoist155:Rust_primitives.Hax.t_Never =
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
              let* hoist156:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
                  )
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist156)
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
              let* hoist157:Rust_primitives.Hax.t_Never =
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
            let* hoist158:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist158)
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
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1_full (Bertie.Tls13utils.impl__Bytes__slice_range
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
            let* hoist159:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist159)
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
            let* hoist160:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist160)
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
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1 (Bertie.Tls13utils.impl__Bytes__slice_range
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
            let* hoist161:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist161)
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
            let* hoist162:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist162)
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
              let* hoist163:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist163)
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
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1_full (Bertie.Tls13utils.impl__Bytes__slice_range
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
              let* hoist164:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist164)
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

let check_ciphersuites (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result usize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 b
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist165:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist165)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result usize u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result usize u8) usize
      in
      let* cs:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (ciphersuite algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist166:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist166)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result usize u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result usize u8)
            Bertie.Tls13utils.t_Bytes
      in
      let csl:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range b
          ({ Core.Ops.Range.f_start = sz 2; Core.Ops.Range.f_end = sz 2 +! len <: usize }
            <:
            Core.Ops.Range.t_Range usize)
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_mem cs csl
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist167:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist167)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result usize u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result usize u8) Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok (len +! sz 2) <: Core.Result.t_Result usize u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result usize u8)
        (Core.Result.t_Result usize u8))

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
          let* hoist168:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist168)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      let* hoist170:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (signature_algorithm algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist169:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist169)
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
      (Bertie.Tls13utils.check_mem hoist170
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
          let* hoist171:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist171)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      let* hoist173:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist172:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist172)
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
      (Bertie.Tls13utils.check_mem hoist173
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

let check_supported_versions
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1_full ch
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist174:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist174)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13utils.check_mem (Bertie.Tls13utils.bytes2 3uy 4uy <: Bertie.Tls13utils.t_Bytes)
          (Bertie.Tls13utils.impl__Bytes__slice_range ch
              ({
                  Core.Ops.Range.f_start = sz 1;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Bertie.Tls13utils.t_Bytes))
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

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
        let* hoist177:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 r
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist176:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist176)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
        in
        let hoist178:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat b2 hoist177
        in
        let hoist181:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat hoist178 b2
        in
        let* hoist180:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 s
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist179:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist179)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
        in
        let hoist182:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat hoist181 hoist180
        in
        let hoist183:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
          Bertie.Tls13utils.lbytes1 hoist182
        in
        let hoist184:Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
          Core.Ops.Try_trait.f_branch hoist183
        in
        let* hoist185:Bertie.Tls13utils.t_Bytes =
          match hoist184 with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist175:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist175)
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
        (let hoist186:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__concat b1 hoist185
          in
          Core.Result.Result_Ok hoist186 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist221:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist218:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist218)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* hoist220:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 gx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist219:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist219)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let ks:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat hoist221 hoist220 in
      let* hoist224:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 ks
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist223:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist223)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist225:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist224
      in
      let hoist226:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist225
      in
      let* hoist227:Bertie.Tls13utils.t_Bytes =
        match hoist226 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist222:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist222)
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
      (let hoist228:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 51uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist227
        in
        Core.Result.Result_Ok hoist228 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let pre_shared_key
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (session_ticket: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist231:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 session_ticket
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist230:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist230)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
      in
      let hoist232:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat hoist231
          (Bertie.Tls13utils.impl__U32__to_be_bytes (Core.Convert.f_from 4294967295ul
                <:
                Bertie.Tls13utils.t_U32)
            <:
            Bertie.Tls13utils.t_Bytes)
      in
      let hoist233:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist232
      in
      let hoist234:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist233
      in
      let* identities:Bertie.Tls13utils.t_Bytes =
        match hoist234 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist229:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist229)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
      in
      let* hoist237:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 (Bertie.Tls13crypto.zero_key (Bertie.Tls13crypto.hash_alg
                        algs
                      <:
                      Bertie.Tls13crypto.t_HashAlgorithm)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist236:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist236)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
      in
      let hoist238:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist237
      in
      let hoist239:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist238
      in
      let* binders:Bertie.Tls13utils.t_Bytes =
        match hoist239 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist235:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist235)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8) Bertie.Tls13utils.t_Bytes
      in
      let* hoist241:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 (Bertie.Tls13utils.impl__Bytes__concat
                    identities
                    binders
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist240:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist240)
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
            hoist241
        in
        Core.Result.Result_Ok
        (ext, Bertie.Tls13utils.impl__Bytes__len binders <: (Bertie.Tls13utils.t_Bytes & usize))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8))

let psk_key_exchange_modes (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist244:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 (Bertie.Tls13utils.bytes1 1uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist243:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist243)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist245:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist244
      in
      let hoist246:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist245
      in
      let* hoist247:Bertie.Tls13utils.t_Bytes =
        match hoist246 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist242:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist242)
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
      (let hoist248:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 45uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist247
        in
        Core.Result.Result_Ok hoist248 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let server_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist252:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist249:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist249)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* hoist251:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 gx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist250:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist250)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let ks:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat hoist252 hoist251 in
      let* hoist254:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 ks
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist253:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist253)
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
      (let hoist255:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 51uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist254
        in
        Core.Result.Result_Ok hoist255 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let server_name (sn: Bertie.Tls13utils.t_Bytes) : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist259:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 sn
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist258:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist258)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist260:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes1 0uy
            <:
            Bertie.Tls13utils.t_Bytes)
          hoist259
      in
      let hoist261:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist260
      in
      let hoist262:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist261
      in
      let* hoist263:Bertie.Tls13utils.t_Bytes =
        match hoist262 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist257:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist257)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist264:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist263
      in
      let hoist265:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist264
      in
      let* hoist266:Bertie.Tls13utils.t_Bytes =
        match hoist265 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist256:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist256)
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
      (let hoist267:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 0uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist266
        in
        Core.Result.Result_Ok hoist267 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let server_pre_shared_key (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist269:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 (Bertie.Tls13utils.bytes2 0uy 0uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist268:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist268)
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
      (let hoist270:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 41uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist269
        in
        Core.Result.Result_Ok hoist270 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let server_supported_version (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist272:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 (Bertie.Tls13utils.bytes2 3uy 4uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist271:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist271)
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
      (let hoist273:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 43uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist272
        in
        Core.Result.Result_Ok hoist273 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist277:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (signature_algorithm algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist276:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist276)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist278:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist277
      in
      let hoist279:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist278
      in
      let* hoist280:Bertie.Tls13utils.t_Bytes =
        match hoist279 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist275:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist275)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist281:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist280
      in
      let hoist282:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist281
      in
      let* hoist283:Bertie.Tls13utils.t_Bytes =
        match hoist282 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist274:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist274)
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
      (let hoist284:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 13uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist283
        in
        Core.Result.Result_Ok hoist284 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let supported_groups (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist288:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist287:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist287)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist289:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist288
      in
      let hoist290:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist289
      in
      let* hoist291:Bertie.Tls13utils.t_Bytes =
        match hoist290 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist286:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist286)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist292:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist291
      in
      let hoist293:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist292
      in
      let* hoist294:Bertie.Tls13utils.t_Bytes =
        match hoist293 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist285:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist285)
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
      (let hoist295:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 10uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist294
        in
        Core.Result.Result_Ok hoist295 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let supported_versions (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist298:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 (Bertie.Tls13utils.bytes2 3uy 4uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist297:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist297)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist299:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist298
      in
      let hoist300:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist299
      in
      let* hoist301:Bertie.Tls13utils.t_Bytes =
        match hoist300 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist296:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist296)
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
      (let hoist302:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 43uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist301
        in
        Core.Result.Result_Ok hoist302 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

type t_EXTS =
  | EXTS :
      Core.Option.t_Option Bertie.Tls13utils.t_Bytes ->
      Core.Option.t_Option Bertie.Tls13utils.t_Bytes ->
      Core.Option.t_Option Bertie.Tls13utils.t_Bytes ->
      Core.Option.t_Option Bertie.Tls13utils.t_Bytes
    -> t_EXTS

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
          let* hoist304:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist304)
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
            let* hoist305:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist305)
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
              let* hoist306:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist306)
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
              let* hoist307:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist307)
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
          let* hoist308:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist308)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Prims.unit
      in
      let* hoist310:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist309:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist309)
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
      (find_key_share hoist310
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

let check_extension (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (usize & t_EXTS) u8 =
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
          let* hoist311:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (usize & t_EXTS) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist311)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8) usize
      in
      let out:t_EXTS =
        EXTS (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
          (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
          (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
          (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        <:
        t_EXTS
      in
      match (cast (l0 <: usize) <: u8), (cast (l1 <: usize) <: u8) <: (u8 & u8) with
      | 0uy, 0uy ->
        let* hoist313:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (check_server_name (Bertie.Tls13utils.impl__Bytes__slice_range
                      b
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
            let* hoist312:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_EXTS) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist312)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
              Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
              Bertie.Tls13utils.t_Bytes
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let hoist314:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
            Core.Option.Option_Some hoist313 <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
          in
          let hoist315:t_EXTS =
            EXTS hoist314
              (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
              (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
              (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
            <:
            t_EXTS
          in
          let hoist316:(usize & t_EXTS) = sz 4 +! len, hoist315 <: (usize & t_EXTS) in
          Core.Result.Result_Ok hoist316 <: Core.Result.t_Result (usize & t_EXTS) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
          (Core.Result.t_Result (usize & t_EXTS) u8)
      | 0uy, 45uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_psk_key_exchange_modes algs
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
            let* hoist317:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_EXTS) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist317)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
              Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_EXTS))
          <:
          Core.Result.t_Result (usize & t_EXTS) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
          (Core.Result.t_Result (usize & t_EXTS) u8)
      | 0uy, 43uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_supported_versions algs
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
            let* hoist318:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_EXTS) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist318)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
              Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_EXTS))
          <:
          Core.Result.t_Result (usize & t_EXTS) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
          (Core.Result.t_Result (usize & t_EXTS) u8)
      | 0uy, 10uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_supported_groups algs
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
            let* hoist319:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_EXTS) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist319)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
              Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_EXTS))
          <:
          Core.Result.t_Result (usize & t_EXTS) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
          (Core.Result.t_Result (usize & t_EXTS) u8)
      | 0uy, 13uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_signature_algorithms algs
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
            let* hoist320:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_EXTS) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist320)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
              Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_EXTS))
          <:
          Core.Result.t_Result (usize & t_EXTS) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
          (Core.Result.t_Result (usize & t_EXTS) u8)
      | 0uy, 51uy ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (match
            check_key_shares algs
              (Bertie.Tls13utils.impl__Bytes__slice_range b
                  ({ Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 4 +! len <: usize }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Bertie.Tls13utils.t_Bytes)
          with
          | Core.Result.Result_Ok gx ->
            Core.Result.Result_Ok
            (sz 4 +! len,
              (EXTS (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
                  (Core.Option.Option_Some gx <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
                  (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
                  (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
                <:
                t_EXTS)
              <:
              (usize & t_EXTS))
            <:
            Core.Result.t_Result (usize & t_EXTS) u8
          | Core.Result.Result_Err _ ->
            Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_MISSING_KEY_SHARE)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
          (Core.Result.t_Result (usize & t_EXTS) u8)
      | 0uy, 41uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_psk_shared_key algs
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
            let* hoist321:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_EXTS) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist321)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
              Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_EXTS))
          <:
          Core.Result.t_Result (usize & t_EXTS) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
          (Core.Result.t_Result (usize & t_EXTS) u8)
      | _ ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_EXTS))
          <:
          Core.Result.t_Result (usize & t_EXTS) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (usize & t_EXTS) u8)
          (Core.Result.t_Result (usize & t_EXTS) u8))

let merge_exts (e1 e2: t_EXTS) : Core.Result.t_Result t_EXTS u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let EXTS sn1 ks1 tkt1 bd1:t_EXTS = e1 in
      let EXTS sn2 ks2 tkt2 bd2:t_EXTS = e2 in
      let* hoist329:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts sn1 sn2
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist322:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_EXTS u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist322)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      let* hoist328:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts ks1 ks2
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist323:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_EXTS u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist323)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      let* hoist327:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts tkt1 tkt2
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist324:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_EXTS u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist324)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      let* hoist326:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts bd1 bd2
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist325:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_EXTS u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist325)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8)
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist330:t_EXTS = EXTS hoist329 hoist328 hoist327 hoist326 <: t_EXTS in
        Core.Result.Result_Ok hoist330 <: Core.Result.t_Result t_EXTS u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8)
        (Core.Result.t_Result t_EXTS u8))

let missing_key_share: Core.Result.t_Result (usize & t_EXTS) u8 =
  Core.Result.Result_Err Bertie.Tls13utils.v_MISSING_KEY_SHARE
  <:
  Core.Result.t_Result (usize & t_EXTS) u8

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
          Bertie.Tls13utils.bytes1 (content_type (ContentType_Handshake <: t_ContentType) <: u8)
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
              let* hoist344:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist344)
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
              let* hoist345:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist345)
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
            let* hoist346:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist346)
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
      let* hoist349:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 (Bertie.Tls13utils.impl__Bytes__new
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist348:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist348)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let hoist350:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes3 hoist349
      in
      let hoist351:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist350
      in
      let* hoist352:Bertie.Tls13utils.t_Bytes =
        match hoist351 with
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
      (let hoist353:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat ty hoist352 in
        let hoist354:Bertie.Tls13utils.t_HandshakeData =
          Bertie.Tls13utils.HandshakeData hoist353 <: Bertie.Tls13utils.t_HandshakeData
        in
        Core.Result.Result_Ok hoist354 <: Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8))

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
          let* hoist355:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist355)
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
        Bertie.Tls13utils.bytes1 (content_type (ContentType_Handshake <: t_ContentType) <: u8)
      in
      let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
      let* hoist357:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 p
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist356:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist356)
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
      (let hoist358:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat ty ver
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist357
        in
        Core.Result.Result_Ok hoist358 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
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
          let* hoist359:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist359)
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
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (binder: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (ch: Bertie.Tls13utils.t_HandshakeData)
      (trunc_len: Core.Option.t_Option usize)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  let Bertie.Tls13utils.HandshakeData ch:Bertie.Tls13utils.t_HandshakeData = ch in
  let chlen:usize = Bertie.Tls13utils.impl__Bytes__len ch in
  let hlen:usize =
    Bertie.Tls13crypto.hash_len (Bertie.Tls13crypto.hash_alg algs
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
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist361:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes3 v_by
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist360:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist360)
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
      (let hoist362:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes1 (hs_type ty <: u8)
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist361
        in
        let hoist363:Bertie.Tls13utils.t_HandshakeData =
          Bertie.Tls13utils.handshake_data hoist362
        in
        Core.Result.Result_Ok hoist363 <: Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8))

let certificate_verify (algs: Bertie.Tls13crypto.t_Algorithms) (cv: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* sv:Bertie.Tls13utils.t_Bytes =
        match algs.Bertie.Tls13crypto._2 with
        | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
          Core.Ops.Control_flow.ControlFlow_Continue (Core.Clone.f_clone cv)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
          if (Bertie.Tls13utils.impl__Bytes__len cv <: usize) <>. sz 64
          then
            let* hoist364:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed
                      <:
                      u8)
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist364)
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
                let* hoist365:Rust_primitives.Hax.t_Never =
                  Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                      <:
                      Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
                in
                Core.Ops.Control_flow.ControlFlow_Continue
                (Rust_primitives.Hax.never_to_any hoist365)
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
      let* hoist369:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (signature_algorithm algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist366:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist366)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* hoist368:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 sv
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist367:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist367)
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
          Bertie.Tls13utils.impl__Bytes__concat hoist369 hoist368
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 (Bertie.Tls13utils.impl__Bytes__zeroes
                    (sz 32)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist370:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist370)
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
      let* hoist373:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (ciphersuite algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist372:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist372)
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
      let hoist374:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist373
      in
      let hoist375:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist374
      in
      let* cip:Bertie.Tls13utils.t_Bytes =
        match hoist375 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist371:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist371)
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
          let* hoist376:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist376)
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
          Core.Ops.Try_trait.f_branch (supported_versions algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist377:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist377)
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
          let* hoist378:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist378)
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
          let* hoist379:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist379)
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
          let* hoist380:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist380)
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
          Bertie.Tls13crypto.psk_mode algs, session_ticket
          <:
          (bool & Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        with
        | true, Core.Option.Option_Some session_ticket ->
          let* pskm:Bertie.Tls13utils.t_Bytes =
            match
              Core.Ops.Try_trait.f_branch (psk_key_exchange_modes algs
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist381:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist381)
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
              let* hoist382:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist382)
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
            let* hoist383:Rust_primitives.Hax.t_Never =
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
      let* hoist386:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 exts
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist385:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist385)
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
      let hoist387:Bertie.Tls13utils.t_Bytes =
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
          hoist386
      in
      let hoist388:Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
        handshake_message (HandshakeType_ClientHello <: t_HandshakeType) hoist387
      in
      let hoist389:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_HandshakeData =
        Core.Ops.Try_trait.f_branch hoist388
      in
      let* ch:Bertie.Tls13utils.t_HandshakeData =
        match hoist389 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist384:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist384)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 (Bertie.Tls13utils.impl__Bytes__new
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist390:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist390)
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
      let* ext:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 (Bertie.Tls13utils.impl__Bytes__new
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
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
          let* hoist393:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist393)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 sid
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
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
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* cip:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (ciphersuite algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist395:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist395)
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
          let* hoist396:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist396)
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
          let* hoist397:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist397)
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
        match Bertie.Tls13crypto.psk_mode algs with
        | true ->
          let* hoist399:Bertie.Tls13utils.t_Bytes =
            match
              Core.Ops.Try_trait.f_branch (server_pre_shared_key algs
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist398:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist398)
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
          (let hoist400:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__concat exts hoist399
            in
            hoist400)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | false ->
          Core.Ops.Control_flow.ControlFlow_Continue exts
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* hoist403:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 exts
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist402:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist402)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let hoist404:Bertie.Tls13utils.t_Bytes =
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
          hoist403
      in
      let hoist405:Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
        handshake_message (HandshakeType_ServerHello <: t_HandshakeType) hoist404
      in
      let hoist406:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_HandshakeData =
        Core.Ops.Try_trait.f_branch hoist405
      in
      let* sh:Bertie.Tls13utils.t_HandshakeData =
        match hoist406 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist401:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist401)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 (Bertie.Tls13utils.bytes1 1uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist407:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist407)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 tkt
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist408:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist408)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8) Bertie.Tls13utils.t_Bytes
      in
      let* hoist410:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 (Bertie.Tls13utils.impl__Bytes__new
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist409:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist409)
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
          hoist410
      in
      let* ext:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 grease_ext
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist411:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist411)
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

let get_first_handshake_message (p: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
      u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let p:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.handshake_data_bytes p
      in
      if (Bertie.Tls13utils.impl__Bytes__len p <: usize) <. sz 4
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed <: u8))
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
                      p
                      ({
                          Core.Ops.Range.f_start = sz 1;
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
            let* hoist414:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist414)
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
            Bertie.Tls13utils.impl__Bytes__slice_range p
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 4 +! len <: usize }
                <:
                Core.Ops.Range.t_Range usize)
          in
          let rest:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__slice_range p
              ({
                  Core.Ops.Range.f_start = sz 4 +! len <: usize;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len p <: usize
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
          let* hoist416:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist416)
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
          let* hoist417:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist417)
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
          let* hoist418:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist418)
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
          let* hoist419:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist419)
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
          let* hoist420:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist420)
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
          let* hoist421:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist421)
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
          let* hoist422:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist422)
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
          let* hoist423:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist423)
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
          let* hoist424:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist424)
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
          let* hoist425:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist425)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_HandshakeData
      in
      let sa:Bertie.Tls13crypto.t_SignatureScheme = Bertie.Tls13crypto.sig_alg algs in
      let* hoist428:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (signature_algorithm algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist427:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist427)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let hoist429:Core.Result.t_Result Prims.unit u8 =
        Bertie.Tls13utils.check_eq hoist428
          (Bertie.Tls13utils.impl__Bytes__slice_range cv
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Bertie.Tls13utils.t_Bytes)
      in
      let hoist430:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Prims.unit =
        Core.Ops.Try_trait.f_branch hoist429
      in
      let* _:Prims.unit =
        match hoist430 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist426:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist426)
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
          let* hoist431:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist431)
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
          let* hoist432:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist432)
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
          let* hoist433:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist433)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1 (Bertie.Tls13utils.impl__Bytes__slice_range
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
          let* hoist434:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist434)
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
          let* hoist435:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist435)
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
          let* hoist436:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist436)
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
          let* hoist437:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist437)
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
          let* hoist438:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist438)
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
          Core.Ops.Try_trait.f_branch (ciphersuite algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist439:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist439)
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
            let* hoist440:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist440)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1 (Bertie.Tls13utils.impl__Bytes__slice_range
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
          let* hoist441:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist441)
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
            let* hoist442:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist442)
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
            let* hoist443:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist443)
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
          let* hoist444:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist444)
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
          let* hoist445:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist445)
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
          let* hoist446:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist446)
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
          let* hoist447:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist447)
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
          let* hoist448:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist448)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1 (Bertie.Tls13utils.impl__Bytes__slice_range
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
          let* hoist449:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist449)
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
          let* hoist450:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist450)
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
          let* hoist451:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist451)
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
    : Core.Result.t_Result t_EXTS u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len, out:(usize & t_EXTS) =
        match
          Core.Ops.Try_trait.f_branch (check_extension algs b
              <:
              Core.Result.t_Result (usize & t_EXTS) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist452:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_EXTS u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist452)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8) (usize & t_EXTS)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8) (usize & t_EXTS)
      in
      if len =. (Bertie.Tls13utils.impl__Bytes__len b <: usize)
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok out <: Core.Result.t_Result t_EXTS u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8)
          (Core.Result.t_Result t_EXTS u8)
      else
        let* out_rest:t_EXTS =
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
                Core.Result.t_Result t_EXTS u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist453:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_EXTS u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist453)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8) t_EXTS
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8) t_EXTS
        in
        Core.Ops.Control_flow.ControlFlow_Continue (merge_exts out out_rest)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_EXTS u8)
          (Core.Result.t_Result t_EXTS u8))

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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hash ha txby
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist454:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist454)
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
  Bertie.Tls13crypto.hash ha
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
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_HandshakeData)
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
                ch
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist455:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist455)
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
          let* hoist456:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist456)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1 (Bertie.Tls13utils.impl__Bytes__slice_range
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
          let* hoist457:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist457)
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
          Core.Ops.Try_trait.f_branch (check_ciphersuites algs
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
          let* hoist458:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist458)
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
            let* hoist459:Rust_primitives.Hax.t_Never =
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
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist459)
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
          let* hoist460:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist460)
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
      let* exts:t_EXTS =
        match
          Core.Ops.Try_trait.f_branch (check_extensions algs
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
              Core.Result.t_Result t_EXTS u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist461:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist461)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) t_EXTS
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8) t_EXTS
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let trunc_len:usize =
          ((Bertie.Tls13utils.impl__Bytes__len ch <: usize) -!
            (Bertie.Tls13crypto.hash_len (Bertie.Tls13crypto.hash_alg algs
                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
              <:
              usize)
            <:
            usize) -!
          sz 3
        in
        match Bertie.Tls13crypto.psk_mode algs, exts <: (bool & t_EXTS) with
        | _, EXTS _ (Core.Option.Option_None ) _ _ ->
          Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_MISSING_KEY_SHARE
        | true,
        EXTS
          (Core.Option.Option_Some sn)
          (Core.Option.Option_Some gx)
          (Core.Option.Option_Some tkt)
          (Core.Option.Option_Some binder) ->
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
        EXTS
          (Core.Option.Option_None )
          (Core.Option.Option_Some gx)
          (Core.Option.Option_Some tkt)
          (Core.Option.Option_Some binder) ->
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
        EXTS
          (Core.Option.Option_Some sn)
          (Core.Option.Option_Some gx)
          (Core.Option.Option_None )
          (Core.Option.Option_None ) ->
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
        EXTS
          (Core.Option.Option_None )
          (Core.Option.Option_Some gx)
          (Core.Option.Option_None )
          (Core.Option.Option_None ) ->
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
