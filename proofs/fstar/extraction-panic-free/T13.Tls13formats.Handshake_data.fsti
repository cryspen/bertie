module t13.Tls13formats.Handshake_data
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let discriminant_HandshakeType_Certificate: u8 = 11uy

let discriminant_HandshakeType_CertificateRequest: u8 = 13uy

let discriminant_HandshakeType_CertificateVerify: u8 = 15uy

let discriminant_HandshakeType_ClientHello: u8 = 1uy

let discriminant_HandshakeType_EncryptedExtensions: u8 = 8uy

let discriminant_HandshakeType_EndOfEarlyData: u8 = 5uy

let discriminant_HandshakeType_Finished: u8 = 20uy

let discriminant_HandshakeType_KeyUpdate: u8 = 24uy

let discriminant_HandshakeType_MessageHash: u8 = 254uy

let discriminant_HandshakeType_NewSessionTicket: u8 = 4uy

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

let discriminant_HandshakeType_ServerHello: u8 = 2uy

val t_HandshakeType_cast_to_repr (x: t_HandshakeType)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val get_hs_type (t: u8)
    : Prims.Pure (Core.Result.t_Result t_HandshakeType u8) Prims.l_True (fun _ -> Prims.l_True)

type t_HandshakeData = | HandshakeData : t13.Tls13utils.t_Bytes -> t_HandshakeData

val impl__HandshakeData__len (self: t_HandshakeData)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl__HandshakeData__next_handshake_message (self: t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl__HandshakeData__as_handshake_message
      (self: t_HandshakeData)
      (expected_type: t_HandshakeType)
      : Prims.Pure (Core.Result.t_Result t_HandshakeData u8) Prims.l_True (fun _ -> Prims.l_True)

let impl__HandshakeData__to_bytes (self: t_HandshakeData) = self._0

val impl__HandshakeData__to_four (self: t_HandshakeData)
    : Prims.Pure
      (Core.Result.t_Result (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData)
          u8) Prims.l_True (fun _ -> Prims.l_True)

val impl__HandshakeData__to_two (self: t_HandshakeData)
    : Prims.Pure (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From t_HandshakeData t13.Tls13utils.t_Bytes =
  {
    f_from_pre = (fun (value: t13.Tls13utils.t_Bytes) -> true);
    f_from_post = (fun (value: t13.Tls13utils.t_Bytes) (out: t_HandshakeData) -> true);
    f_from = fun (value: t13.Tls13utils.t_Bytes) -> HandshakeData value <: t_HandshakeData
  }

val impl__HandshakeData__concat (self other: t_HandshakeData)
    : Prims.Pure t_HandshakeData Prims.l_True (fun _ -> Prims.l_True)

val impl__HandshakeData__from_bytes
      (handshake_type: t_HandshakeType)
      (handshake_bytes: t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_HandshakeData u8) Prims.l_True (fun _ -> Prims.l_True)

val impl__HandshakeData__find_handshake_message
      (self: t_HandshakeData)
      (handshake_type: t_HandshakeType)
      (start: usize)
    : Prims.Pure bool
      (v start <= v (impl__HandshakeData__len self))
      (fun _ -> Prims.l_True)
      (decreases (v (impl__HandshakeData__len self) - v start))
