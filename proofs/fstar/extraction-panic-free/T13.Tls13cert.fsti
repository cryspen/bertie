module t13.Tls13cert
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_Asn1Error = u8

let v_ASN1_ERROR: u8 = 25uy

let v_ASN1_INVALID_CERTIFICATE: u8 = 23uy

let v_ASN1_INVALID_TAG: u8 = 22uy

let v_ASN1_SEQUENCE_TOO_LONG: u8 = 21uy

let v_ASN1_UNSUPPORTED_ALGORITHM: u8 = 24uy

val asn1_error (#v_T: Type) (err: u8)
    : Prims.Pure (Core.Result.t_Result v_T u8) Prims.l_True (fun _ -> Prims.l_True)

val check_success (v_val: bool)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

type t_CertificateKey = | CertificateKey : usize -> usize -> t_CertificateKey

unfold
let t_Spki = (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey)

val ecdsa_secp256r1_sha256_oid: Prims.unit
  -> Prims.Pure t13.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val rsa_pkcs1_encryption_oid: Prims.unit
  -> Prims.Pure t13.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val x962_ec_public_key_oid: Prims.unit
  -> Prims.Pure t13.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val check_tag (b: t13.Tls13utils.t_Bytes) (offset: usize) (value: u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) 
      (v offset < Seq.length b._0)
      (fun _ -> Prims.l_True)

val ecdsa_public_key (cert: t13.Tls13utils.t_Bytes) (indices: t_CertificateKey)
    : Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      (v indices._0 < Seq.length cert._0 /\
       v indices._0 < pow2 31 - 1 /\ v indices._1 > 0)
      (fun _ -> Prims.l_True)

val length_length (b: t13.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure usize 
      (v offset < Seq.length b._0)
      (fun res -> v res < 128)

val read_octet_header (b: t13.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result usize u8) 
      (v offset + 128 < Seq.length b._0)
      (fun _ -> Prims.l_True)

val read_sequence_header (b: t13.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result usize u8)
      (v offset + 1 < Seq.length b._0 /\ v offset + 129 < pow2 32)
      (fun _ -> Prims.l_True)

val short_length (b: t13.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

val read_version_number (b: t13.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

val long_length (b: t13.Tls13utils.t_Bytes) (offset len: usize)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

val length (b: t13.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result (usize & usize) u8) Prims.l_True (fun _ -> Prims.l_True)

val read_integer (b: t13.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val read_spki (cert: t13.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val skip_integer (b: t13.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

val skip_sequence (b: t13.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

val rsa_private_key (key: t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val verification_key_from_cert (cert: t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val rsa_public_key (cert: t13.Tls13utils.t_Bytes) (indices: t_CertificateKey)
    : Prims.Pure (Core.Result.t_Result t13.Tls13crypto.t_RsaVerificationKey u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val cert_public_key
      (certificate: t13.Tls13utils.t_Bytes)
      (spki: (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey))
    : Prims.Pure (Core.Result.t_Result t13.Tls13crypto.t_PublicVerificationKey u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
