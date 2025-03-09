module Bertie.Tls13crypto
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13utils in
  let open Libcrux_ecdsa.P256.Conversions in
  let open Libcrux_kem in
  let open Libcrux_rsa.Impl_hacl in
  let open Rand.Rng in
  let open Rand_core in
  ()

/// An RSA public key.
type t_RsaVerificationKey = {
  f_modulus:Bertie.Tls13utils.t_Bytes;
  f_exponent:Bertie.Tls13utils.t_Bytes
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_6:Core.Fmt.t_Debug t_RsaVerificationKey

/// Bertie public verification keys.
type t_PublicVerificationKey =
  | PublicVerificationKey_EcDsa : Bertie.Tls13utils.t_Bytes -> t_PublicVerificationKey
  | PublicVerificationKey_Rsa : t_RsaVerificationKey -> t_PublicVerificationKey

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_7:Core.Fmt.t_Debug t_PublicVerificationKey

/// Bertie hash algorithms.
type t_HashAlgorithm =
  | HashAlgorithm_SHA256 : t_HashAlgorithm
  | HashAlgorithm_SHA384 : t_HashAlgorithm
  | HashAlgorithm_SHA512 : t_HashAlgorithm

val t_HashAlgorithm_cast_to_repr (x: t_HashAlgorithm)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_8:Core.Clone.t_Clone t_HashAlgorithm

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_9:Core.Marker.t_Copy t_HashAlgorithm

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_10:Core.Marker.t_StructuralPartialEq t_HashAlgorithm

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_11:Core.Cmp.t_PartialEq t_HashAlgorithm t_HashAlgorithm

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_12:Core.Fmt.t_Debug t_HashAlgorithm

/// Get the libcrux hash algorithm
val impl_HashAlgorithm__libcrux_algorithm (self: t_HashAlgorithm)
    : Prims.Pure (Core.Result.t_Result Libcrux_sha2.Impl_hacl.t_Algorithm u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Hash `data` with the given `algorithm`.
/// Returns the digest or an [`TLSError`].
val impl_HashAlgorithm__hash (self: t_HashAlgorithm) (data: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the size of the hash digest.
val impl_HashAlgorithm__hash_len (self: t_HashAlgorithm)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// Get the libcrux hmac algorithm.
val impl_HashAlgorithm__hmac_algorithm (self: t_HashAlgorithm)
    : Prims.Pure (Core.Result.t_Result Libcrux_hmac.t_Algorithm u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the size of the hmac tag.
val impl_HashAlgorithm__hmac_tag_len (self: t_HashAlgorithm)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// Compute the HMAC tag.
/// Returns the tag [`Hmac`] or a [`TLSError`].
val hmac_tag (alg: t_HashAlgorithm) (mk input: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Verify a given HMAC `tag`.
/// Returns `()` if successful or a [`TLSError`].
val hmac_verify (alg: t_HashAlgorithm) (mk input tag: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Get an empty key of the correct size.
val zero_key (alg: t_HashAlgorithm)
    : Prims.Pure Bertie.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Get the libcrux HKDF algorithm.
val hkdf_algorithm (alg: t_HashAlgorithm)
    : Prims.Pure (Core.Result.t_Result Libcrux_hkdf.t_Algorithm u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// HKDF Extract.
/// Returns the result as [`Bytes`] or a [`TLSError`].
val hkdf_extract (alg: t_HashAlgorithm) (ikm salt: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// HKDF Expand.
/// Returns the result as [`Bytes`] or a [`TLSError`].
val hkdf_expand (alg: t_HashAlgorithm) (prk info: Bertie.Tls13utils.t_Bytes) (len: usize)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// AEAD Algorithms for Bertie
type t_AeadAlgorithm =
  | AeadAlgorithm_Chacha20Poly1305 : t_AeadAlgorithm
  | AeadAlgorithm_Aes128Gcm : t_AeadAlgorithm
  | AeadAlgorithm_Aes256Gcm : t_AeadAlgorithm

/// An AEAD key.
type t_AeadKey = {
  f_bytes:Bertie.Tls13utils.t_Bytes;
  f_e_alg:t_AeadAlgorithm
}

/// An AEAD key and iv package.
type t_AeadKeyIV = {
  f_key:t_AeadKey;
  f_iv:Bertie.Tls13utils.t_Bytes
}

/// Create a new [`AeadKeyIV`].
val impl_AeadKeyIV__new (key: t_AeadKey) (iv: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure t_AeadKeyIV Prims.l_True (fun _ -> Prims.l_True)

/// Create a new AEAD key from the raw bytes and the algorithm.
val impl_AeadKey__new (bytes: Bertie.Tls13utils.t_Bytes) (e_alg: t_AeadAlgorithm)
    : Prims.Pure t_AeadKey Prims.l_True (fun _ -> Prims.l_True)

val t_AeadAlgorithm_cast_to_repr (x: t_AeadAlgorithm)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_13:Core.Clone.t_Clone t_AeadAlgorithm

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_14:Core.Marker.t_Copy t_AeadAlgorithm

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_15:Core.Marker.t_StructuralPartialEq t_AeadAlgorithm

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_16:Core.Cmp.t_PartialEq t_AeadAlgorithm t_AeadAlgorithm

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_17:Core.Fmt.t_Debug t_AeadAlgorithm

/// Get the key length of the AEAD algorithm in bytes.
val impl_AeadAlgorithm__key_len (self: t_AeadAlgorithm)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// Get the length of the IV for this algorithm.
val impl_AeadAlgorithm__iv_len (self: t_AeadAlgorithm)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// AEAD encrypt
val aead_encrypt (k: t_AeadKey) (iv plain aad: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// AEAD decrypt.
val aead_decrypt (k: t_AeadKey) (iv cip aad: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Signature schemes for Bertie.
type t_SignatureScheme =
  | SignatureScheme_RsaPssRsaSha256 : t_SignatureScheme
  | SignatureScheme_EcdsaSecp256r1Sha256 : t_SignatureScheme
  | SignatureScheme_ED25519 : t_SignatureScheme

val t_SignatureScheme_cast_to_repr (x: t_SignatureScheme)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_18:Core.Clone.t_Clone t_SignatureScheme

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_19:Core.Marker.t_Copy t_SignatureScheme

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_20:Core.Marker.t_StructuralPartialEq t_SignatureScheme

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_21:Core.Cmp.t_PartialEq t_SignatureScheme t_SignatureScheme

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_22:Core.Fmt.t_Debug t_SignatureScheme

/// Sign the bytes in `input` with the signature key `sk` and `algorithm`.
val sign
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (algorithm: t_SignatureScheme)
      (sk input: Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
    : Prims.Pure (iimpl_447424039_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Determine if given modulus conforms to one of the key sizes supported by
/// `libcrux`.
val supported_rsa_key_size (n: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Determine if given public exponent is supported by `libcrux`, i.e. whether
///  `e == 0x010001`.
val valid_rsa_exponent (e: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Sign the `input` with the provided RSA key.
val sign_rsa
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (sk pk_modulus pk_exponent: Bertie.Tls13utils.t_Bytes)
      (cert_scheme: t_SignatureScheme)
      (input: Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
    : Prims.Pure (iimpl_447424039_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Verify the `input` bytes against the provided `signature`.
/// Return `Ok(())` if the verification succeeds, and a [`TLSError`] otherwise.
val verify
      (alg: t_SignatureScheme)
      (pk: t_PublicVerificationKey)
      (input sig: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Bertie KEM schemes.
/// This includes ECDH curves.
type t_KemScheme =
  | KemScheme_X25519 : t_KemScheme
  | KemScheme_Secp256r1 : t_KemScheme
  | KemScheme_X448 : t_KemScheme
  | KemScheme_Secp384r1 : t_KemScheme
  | KemScheme_Secp521r1 : t_KemScheme
  | KemScheme_X25519Kyber768Draft00 : t_KemScheme
  | KemScheme_X25519MlKem768 : t_KemScheme

val t_KemScheme_cast_to_repr (x: t_KemScheme)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_23:Core.Clone.t_Clone t_KemScheme

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_24:Core.Marker.t_Copy t_KemScheme

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_25:Core.Marker.t_StructuralPartialEq t_KemScheme

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_26:Core.Cmp.t_PartialEq t_KemScheme t_KemScheme

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_27:Core.Cmp.t_Eq t_KemScheme

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_28:Core.Fmt.t_Debug t_KemScheme

/// Get the libcrux algorithm for this [`KemScheme`].
val impl_KemScheme__libcrux_kem_algorithm (self: t_KemScheme)
    : Prims.Pure (Core.Result.t_Result Libcrux_kem.t_Algorithm u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Note that the `encode` in libcrux currently returns the raw
/// concatenation of bytes. We have to prepend the 0x04 for
/// uncompressed points on NIST curves.
val encoding_prefix (alg: t_KemScheme)
    : Prims.Pure Bertie.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Generate a new KEM key pair.
val kem_keygen
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (alg: t_KemScheme)
      (rng: iimpl_447424039_)
    : Prims.Pure
      (iimpl_447424039_ &
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Note that the `encode` in libcrux operates on the raw
/// concatenation of bytes. We have to work with uncompressed NIST points here.
val into_raw (alg: t_KemScheme) (point: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure Bertie.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// We only want the X coordinate for points on NIST curves.
val to_shared_secret (alg: t_KemScheme) (shared_secret: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure Bertie.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// KEM encapsulation
val kem_encap
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (alg: t_KemScheme)
      (pk: Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
    : Prims.Pure
      (iimpl_447424039_ &
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// KEM decapsulation
val kem_decap (alg: t_KemScheme) (ct sk: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// The algorithms for Bertie.
/// Note that this is more than the TLS 1.3 ciphersuite. It contains all
/// necessary cryptographic algorithms and options.
type t_Algorithms = {
  f_hash:t_HashAlgorithm;
  f_aead:t_AeadAlgorithm;
  f_signature:t_SignatureScheme;
  f_kem:t_KemScheme;
  f_psk_mode:bool;
  f_zero_rtt:bool
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_29:Core.Clone.t_Clone t_Algorithms

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_30:Core.Marker.t_Copy t_Algorithms

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_31:Core.Marker.t_StructuralPartialEq t_Algorithms

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_32:Core.Cmp.t_PartialEq t_Algorithms t_Algorithms

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_33:Core.Fmt.t_Debug t_Algorithms

/// Create a new [`Algorithms`] object for the TLS 1.3 ciphersuite.
val impl_Algorithms__new
      (hash: t_HashAlgorithm)
      (aead: t_AeadAlgorithm)
      (sig: t_SignatureScheme)
      (kem: t_KemScheme)
      (psk zero_rtt: bool)
    : Prims.Pure t_Algorithms Prims.l_True (fun _ -> Prims.l_True)

/// Get the [`HashAlgorithm`].
val impl_Algorithms__hash (self: t_Algorithms)
    : Prims.Pure t_HashAlgorithm Prims.l_True (fun _ -> Prims.l_True)

/// Get the [`AeadAlgorithm`].
val impl_Algorithms__aead (self: t_Algorithms)
    : Prims.Pure t_AeadAlgorithm Prims.l_True (fun _ -> Prims.l_True)

/// Get the [`SignatureAlgorithm`].
val impl_Algorithms__signature (self: t_Algorithms)
    : Prims.Pure t_SignatureScheme Prims.l_True (fun _ -> Prims.l_True)

/// Get the [`KemScheme`].
val impl_Algorithms__kem (self: t_Algorithms)
    : Prims.Pure t_KemScheme Prims.l_True (fun _ -> Prims.l_True)

/// Returns `true` when using the PSK mode and `false` otherwise.
val impl_Algorithms__psk_mode (self: t_Algorithms)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Returns `true` when using zero rtt and `false` otherwise.
val impl_Algorithms__zero_rtt (self: t_Algorithms)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Returns the TLS ciphersuite for the given algorithm when it is supported, or
/// a [`TLSError`] otherwise.
val impl_Algorithms__ciphersuite (self: t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Returns the curve id for the given algorithm when it is supported, or a [`TLSError`]
/// otherwise.
val impl_Algorithms__supported_group (self: t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Returns the signature id for the given algorithm when it is supported, or a
///  [`TLSError`] otherwise.
val impl_Algorithms__signature_algorithm (self: t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Check the ciphersuite in `bytes` against this ciphersuite.
val impl_Algorithms__check (self: t_Algorithms) (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result usize u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core.Result.t_Result usize u8 = result in
          match result <: Core.Result.t_Result usize u8 with
          | Core.Result.Result_Ok len ->
            (Core.Slice.impl__len #u8 bytes <: usize) >=. len && len <. mk_usize 65538
          | _ -> true)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_35:Core.Convert.t_TryFrom t_Algorithms string

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_5:Core.Fmt.t_Display t_Algorithms

/// `TLS_CHACHA20_POLY1305_SHA256`
/// with
/// * x25519 for key exchange
/// * EcDSA P256 SHA256 for signatures
let v_SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519: t_Algorithms =
  impl_Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Chacha20Poly1305 <: t_AeadAlgorithm)
    (SignatureScheme_EcdsaSecp256r1Sha256 <: t_SignatureScheme)
    (KemScheme_X25519 <: t_KemScheme)
    false
    false

/// `TLS_CHACHA20_POLY1305_SHA256`
/// with
/// * X25519Kyber768Draft00 for key exchange (cf. https://www.ietf.org/archive/id/draft-tls-westerbaan-xyber768d00-02.html)
/// * EcDSA P256 SHA256 for signatures
let v_SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519Kyber768Draft00: t_Algorithms =
  impl_Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Chacha20Poly1305 <: t_AeadAlgorithm)
    (SignatureScheme_EcdsaSecp256r1Sha256 <: t_SignatureScheme)
    (KemScheme_X25519Kyber768Draft00 <: t_KemScheme)
    false
    false

/// `TLS_CHACHA20_POLY1305_SHA256`
/// with
/// * X25519MlKem768 for key exchange (cf. https://datatracker.ietf.org/doc/draft-kwiatkowski-tls-ecdhe-mlkem/)
/// * EcDSA P256 SHA256 for signatures
let v_SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519MlKem768: t_Algorithms =
  impl_Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Chacha20Poly1305 <: t_AeadAlgorithm)
    (SignatureScheme_EcdsaSecp256r1Sha256 <: t_SignatureScheme)
    (KemScheme_X25519MlKem768 <: t_KemScheme)
    false
    false

/// `TLS_CHACHA20_POLY1305_SHA256`
/// with
/// * x25519 for key exchange
/// * RSA PSS SHA256 for signatures
let v_SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519: t_Algorithms =
  impl_Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Chacha20Poly1305 <: t_AeadAlgorithm)
    (SignatureScheme_RsaPssRsaSha256 <: t_SignatureScheme)
    (KemScheme_X25519 <: t_KemScheme)
    false
    false

/// `TLS_CHACHA20_POLY1305_SHA256`
/// with
/// * P256 for key exchange
/// * EcDSA P256 SHA256 for signatures
let v_SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256: t_Algorithms =
  impl_Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Chacha20Poly1305 <: t_AeadAlgorithm)
    (SignatureScheme_EcdsaSecp256r1Sha256 <: t_SignatureScheme)
    (KemScheme_Secp256r1 <: t_KemScheme)
    false
    false

/// `TLS_CHACHA20_POLY1305_SHA256`
/// with
/// * P256 for key exchange
/// * RSA PSSS SHA256 for signatures
let v_SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256: t_Algorithms =
  impl_Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Chacha20Poly1305 <: t_AeadAlgorithm)
    (SignatureScheme_RsaPssRsaSha256 <: t_SignatureScheme)
    (KemScheme_Secp256r1 <: t_KemScheme)
    false
    false
