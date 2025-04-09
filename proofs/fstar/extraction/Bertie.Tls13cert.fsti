module Bertie.Tls13cert
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13utils in
  ()

/// Certificate key start and length within the certificate DER.
type t_CertificateKey = | CertificateKey : usize -> usize -> t_CertificateKey

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Core.Clone.t_Clone t_CertificateKey

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core.Marker.t_Copy t_CertificateKey

let v_ASN1_SEQUENCE_TOO_LONG: u8 = mk_u8 21

let v_ASN1_INVALID_TAG: u8 = mk_u8 22

let v_ASN1_INVALID_CERTIFICATE: u8 = mk_u8 23

let v_ASN1_UNSUPPORTED_ALGORITHM: u8 = mk_u8 24

let v_ASN1_ERROR: u8 = mk_u8 25

val asn1_error (#v_T: Type0) (err: u8)
    : Prims.Pure (Core.Result.t_Result v_T u8) Prims.l_True (fun _ -> Prims.l_True)

val long_length (b: Bertie.Tls13utils.t_Bytes) (offset len: usize)
    : Prims.Pure (Core.Result.t_Result usize u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result usize u8 = result in
          match result <: Core.Result.t_Result usize u8 with
          | Core.Result.Result_Ok _ ->
            (Bertie.Tls13utils.impl_Bytes__len b <: usize) >=. offset &&
            ((Bertie.Tls13utils.impl_Bytes__len b <: usize) -! offset <: usize) >=. len
          | _ -> true)

val length_length (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result usize u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result usize u8 = result in
          match result <: Core.Result.t_Result usize u8 with
          | Core.Result.Result_Ok l ->
            (Bertie.Tls13utils.impl_Bytes__len b <: usize) >. offset && l <=. mk_usize 255
          | _ -> true)

val short_length (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result usize u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result usize u8 = result in
          match result <: Core.Result.t_Result usize u8 with
          | Core.Result.Result_Ok _ -> (Bertie.Tls13utils.impl_Bytes__len b <: usize) >. offset
          | _ -> true)

/// Get the length of an ASN.1 type.
/// This assumes that the length starts at the beginning of the provided byte
/// sequence.
/// Returns: (offset, length)
val length (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result (usize & usize) u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result (usize & usize) u8 = result in
          match result <: Core.Result.t_Result (usize & usize) u8 with
          | Core.Result.Result_Ok _ -> (Bertie.Tls13utils.impl_Bytes__len b <: usize) >. offset
          | _ -> true)

/// Check that the tag has a certain value.
val check_tag (b: Bertie.Tls13utils.t_Bytes) (offset: usize) (value: u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result Prims.unit u8 = result in
          match result <: Core.Result.t_Result Prims.unit u8 with
          | Core.Result.Result_Ok _ -> (Bertie.Tls13utils.impl_Bytes__len b <: usize) >. offset
          | _ -> true)

/// Read a byte sequence header from the provided bytes.
/// Returns the new offset into the bytes.
val read_sequence_header (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

/// Read an octet string from the provided bytes.
/// Returns the new offset into the bytes.
val read_octet_header (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

/// Skip a sequence.
/// XXX: Share code with [read_sequence_header].
/// Returns the new offset into the bytes.
val skip_sequence (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

/// Read the version number.
/// We don't really care, just check that it's some valid structure and keep the
/// offset moving.
/// Note that this might be missing. So we don't fail in here.
val read_version_number (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

/// Skip an integer.
/// We don't really care, just check that it's some valid structure and keep the
/// offset moving.
val skip_integer (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

/// Read an integer and return a copy of the actual bytes.
val read_integer (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val x962_ec_public_key_oid: Prims.unit
  -> Prims.Pure Bertie.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val ecdsa_secp256r1_sha256_oid: Prims.unit
  -> Prims.Pure Bertie.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val rsa_pkcs1_encryption_oid: Prims.unit
  -> Prims.Pure Bertie.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val check_success (v_val: bool)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Read the spki from the `cert`.
/// Returns an error or the [`Spki`].
val read_spki (cert: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Basic, but complete ASN.1 parser to read the public key from an X.509
/// certificate.
/// Returns the start offset within the `cert` bytes and length of the key.
val verification_key_from_cert (cert: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Read the EC PK from the cert as uncompressed point.
val ecdsa_public_key (cert: Bertie.Tls13utils.t_Bytes) (indices: t_CertificateKey)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      (requires v indices._1 > 0 && Seq.length cert._0 >= v indices._0 + v indices._1)
      (fun _ -> Prims.l_True)

val rsa_public_key (cert: Bertie.Tls13utils.t_Bytes) (indices: t_CertificateKey)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Read the private key (d) from an RSA private key.
/// We expect to have the [version, privateKeyAlgorithm, privateKey] with
/// RSAPrivateKey ::= SEQUENCE {
///     version   Version,
///     modulus   INTEGER,  -- n
///     publicExponentINTEGER,  -- e
///     privateExponent   INTEGER,  -- d
///     prime1INTEGER,  -- p
///     prime2INTEGER,  -- q
///     exponent1 INTEGER,  -- d mod (p-1)
///     exponent2 INTEGER,  -- d mod (q-1)
///     coefficient   INTEGER,  -- (inverse of q) mod p
///     otherPrimeInfos   OtherPrimeInfos OPTIONAL
/// }
val rsa_private_key (key: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the public key from from a certificate.
/// On input of a `certificate` and `spki`, return a [`PublicVerificationKey`]
/// if successful, or an [`Asn1Error`] otherwise.
val cert_public_key
      (certificate: Bertie.Tls13utils.t_Bytes)
      (spki: (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey))
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
