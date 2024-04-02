module Bertie.Tls13crypto
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_AeadAlgorithm =
  | AeadAlgorithm_Chacha20Poly1305 : t_AeadAlgorithm
  | AeadAlgorithm_Aes128Gcm : t_AeadAlgorithm
  | AeadAlgorithm_Aes256Gcm : t_AeadAlgorithm

val impl__AeadAlgorithm__iv_len (self: t_AeadAlgorithm)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl__AeadAlgorithm__key_len (self: t_AeadAlgorithm)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val t_AeadAlgorithm_cast_to_repr (x: t_AeadAlgorithm)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

type t_HashAlgorithm =
  | HashAlgorithm_SHA256 : t_HashAlgorithm
  | HashAlgorithm_SHA384 : t_HashAlgorithm
  | HashAlgorithm_SHA512 : t_HashAlgorithm

val t_HashAlgorithm_cast_to_repr (x: t_HashAlgorithm)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

type t_KemScheme =
  | KemScheme_X25519 : t_KemScheme
  | KemScheme_Secp256r1 : t_KemScheme
  | KemScheme_X448 : t_KemScheme
  | KemScheme_Secp384r1 : t_KemScheme
  | KemScheme_Secp521r1 : t_KemScheme

val t_KemScheme_cast_to_repr (x: t_KemScheme)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

type t_SignatureScheme =
  | SignatureScheme_RsaPssRsaSha256 : t_SignatureScheme
  | SignatureScheme_EcdsaSecp256r1Sha256 : t_SignatureScheme
  | SignatureScheme_ED25519 : t_SignatureScheme

val t_SignatureScheme_cast_to_repr (x: t_SignatureScheme)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val valid_rsa_exponent (e: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

(*
val impl__HashAlgorithm__libcrux_algorithm (self: t_HashAlgorithm)
    : Prims.Pure (Core.Result.t_Result Libcrux.Digest.t_Algorithm u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
*)

val impl__HashAlgorithm__hash_len (self: t_HashAlgorithm)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl__HashAlgorithm__hmac_tag_len (self: t_HashAlgorithm)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

(*
val hkdf_algorithm (alg: t_HashAlgorithm)
    : Prims.Pure (Core.Result.t_Result Libcrux.Hkdf.t_Algorithm u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl__HashAlgorithm__hmac_algorithm (self: t_HashAlgorithm)
    : Prims.Pure (Core.Result.t_Result Libcrux.Hmac.t_Algorithm u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl__SignatureScheme__libcrux_scheme (self: t_SignatureScheme)
    : Prims.Pure (Core.Result.t_Result Libcrux.Signature.t_Algorithm u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl__KemScheme__libcrux_algorithm (self: t_KemScheme)
    : Prims.Pure (Core.Result.t_Result Libcrux.Kem.t_Algorithm u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
*)

type t_Algorithms = {
  f_hash:t_HashAlgorithm;
  f_aead:t_AeadAlgorithm;
  f_signature:t_SignatureScheme;
  f_kem:t_KemScheme;
  f_psk_mode:bool;
  f_zero_rtt:bool
}

val impl__Algorithms__aead (self: t_Algorithms)
    : Prims.Pure t_AeadAlgorithm Prims.l_True (fun _ -> Prims.l_True)

val impl__Algorithms__hash (self: t_Algorithms)
    : Prims.Pure t_HashAlgorithm Prims.l_True (fun _ -> Prims.l_True)

val impl__Algorithms__kem (self: t_Algorithms)
    : Prims.Pure t_KemScheme Prims.l_True (fun _ -> Prims.l_True)

val impl__Algorithms__new
      (hash: t_HashAlgorithm)
      (aead: t_AeadAlgorithm)
      (sig: t_SignatureScheme)
      (kem: t_KemScheme)
      (psk zero_rtt: bool)
    : Prims.Pure t_Algorithms Prims.l_True (fun _ -> Prims.l_True)

val impl__Algorithms__psk_mode (self: t_Algorithms)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val impl__Algorithms__signature (self: t_Algorithms)
    : Prims.Pure t_SignatureScheme Prims.l_True (fun _ -> Prims.l_True)

val impl__Algorithms__zero_rtt (self: t_Algorithms)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Fmt.t_Display t_Algorithms =
  {
    f_fmt_pre = (fun (self: t_Algorithms) (f: Core.Fmt.t_Formatter) -> true);
    f_fmt_post
    =
    (fun
        (self: t_Algorithms)
        (f: Core.Fmt.t_Formatter)
        (out1: (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error))
        ->
        true);
    f_fmt
    =
    fun (self: t_Algorithms) (f: Core.Fmt.t_Formatter) ->
      let tmp0, out:(Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error) =
        Core.Fmt.impl_7__write_fmt f
          (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize (let list =
                      ["TLS_"; "_"; " w/ "; " | "]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
                    Rust_primitives.Hax.array_of_list 4 list)
                <:
                t_Slice string)
              (Rust_primitives.unsize (let list =
                      [
                        Core.Fmt.Rt.impl_1__new_debug self.f_aead <: Core.Fmt.Rt.t_Argument;
                        Core.Fmt.Rt.impl_1__new_debug self.f_hash <: Core.Fmt.Rt.t_Argument;
                        Core.Fmt.Rt.impl_1__new_debug self.f_signature <: Core.Fmt.Rt.t_Argument;
                        Core.Fmt.Rt.impl_1__new_debug self.f_kem <: Core.Fmt.Rt.t_Argument
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
                    Rust_primitives.Hax.array_of_list 4 list)
                <:
                t_Slice Core.Fmt.Rt.t_Argument)
            <:
            Core.Fmt.t_Arguments)
      in
      let f:Core.Fmt.t_Formatter = tmp0 in
      let hax_temp_output:Core.Result.t_Result Prims.unit Core.Fmt.t_Error = out in
      f, hax_temp_output
      <:
      (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
  }

let v_SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256: t_Algorithms =
  impl__Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Aes128Gcm <: t_AeadAlgorithm)
    (SignatureScheme_EcdsaSecp256r1Sha256 <: t_SignatureScheme)
    (KemScheme_Secp256r1 <: t_KemScheme)
    false
    false

let v_SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519: t_Algorithms =
  impl__Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Aes128Gcm <: t_AeadAlgorithm)
    (SignatureScheme_EcdsaSecp256r1Sha256 <: t_SignatureScheme)
    (KemScheme_X25519 <: t_KemScheme)
    false
    false

let v_SHA256_Aes128Gcm_RsaPssRsaSha256_P256: t_Algorithms =
  impl__Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Aes128Gcm <: t_AeadAlgorithm)
    (SignatureScheme_RsaPssRsaSha256 <: t_SignatureScheme)
    (KemScheme_Secp256r1 <: t_KemScheme)
    false
    false

let v_SHA256_Aes128Gcm_RsaPssRsaSha256_X25519: t_Algorithms =
  impl__Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Aes128Gcm <: t_AeadAlgorithm)
    (SignatureScheme_RsaPssRsaSha256 <: t_SignatureScheme)
    (KemScheme_X25519 <: t_KemScheme)
    false
    false

let v_SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256: t_Algorithms =
  impl__Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Chacha20Poly1305 <: t_AeadAlgorithm)
    (SignatureScheme_EcdsaSecp256r1Sha256 <: t_SignatureScheme)
    (KemScheme_Secp256r1 <: t_KemScheme)
    false
    false

let v_SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519: t_Algorithms =
  impl__Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Chacha20Poly1305 <: t_AeadAlgorithm)
    (SignatureScheme_EcdsaSecp256r1Sha256 <: t_SignatureScheme)
    (KemScheme_X25519 <: t_KemScheme)
    false
    false

let v_SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256: t_Algorithms =
  impl__Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Chacha20Poly1305 <: t_AeadAlgorithm)
    (SignatureScheme_RsaPssRsaSha256 <: t_SignatureScheme)
    (KemScheme_Secp256r1 <: t_KemScheme)
    false
    false

let v_SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519: t_Algorithms =
  impl__Algorithms__new (HashAlgorithm_SHA256 <: t_HashAlgorithm)
    (AeadAlgorithm_Chacha20Poly1305 <: t_AeadAlgorithm)
    (SignatureScheme_RsaPssRsaSha256 <: t_SignatureScheme)
    (KemScheme_X25519 <: t_KemScheme)
    false
    false

let v_SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256: t_Algorithms =
  impl__Algorithms__new (HashAlgorithm_SHA384 <: t_HashAlgorithm)
    (AeadAlgorithm_Aes256Gcm <: t_AeadAlgorithm)
    (SignatureScheme_EcdsaSecp256r1Sha256 <: t_SignatureScheme)
    (KemScheme_Secp256r1 <: t_KemScheme)
    false
    false

let v_SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519: t_Algorithms =
  impl__Algorithms__new (HashAlgorithm_SHA384 <: t_HashAlgorithm)
    (AeadAlgorithm_Aes256Gcm <: t_AeadAlgorithm)
    (SignatureScheme_EcdsaSecp256r1Sha256 <: t_SignatureScheme)
    (KemScheme_X25519 <: t_KemScheme)
    false
    false

let v_SHA384_Aes256Gcm_RsaPssRsaSha256_P256: t_Algorithms =
  impl__Algorithms__new (HashAlgorithm_SHA384 <: t_HashAlgorithm)
    (AeadAlgorithm_Aes256Gcm <: t_AeadAlgorithm)
    (SignatureScheme_RsaPssRsaSha256 <: t_SignatureScheme)
    (KemScheme_Secp256r1 <: t_KemScheme)
    false
    false

let v_SHA384_Aes256Gcm_RsaPssRsaSha256_X25519: t_Algorithms =
  impl__Algorithms__new (HashAlgorithm_SHA384 <: t_HashAlgorithm)
    (AeadAlgorithm_Aes256Gcm <: t_AeadAlgorithm)
    (SignatureScheme_RsaPssRsaSha256 <: t_SignatureScheme)
    (KemScheme_X25519 <: t_KemScheme)
    false
    false

unfold
let t_AeadIV = Bertie.Tls13utils.t_Bytes

unfold
let t_Digest = Bertie.Tls13utils.t_Bytes

unfold
let t_Hmac = Bertie.Tls13utils.t_Bytes

unfold
let t_KemPk = Bertie.Tls13utils.t_Bytes

unfold
let t_KemSk = Bertie.Tls13utils.t_Bytes

unfold
let t_Key = Bertie.Tls13utils.t_Bytes

unfold
let t_MacKey = Bertie.Tls13utils.t_Bytes

unfold
let t_Psk = Bertie.Tls13utils.t_Bytes

unfold
let t_Random = Bertie.Tls13utils.t_Bytes

unfold
let t_SignatureKey = Bertie.Tls13utils.t_Bytes

unfold
let t_VerificationKey = Bertie.Tls13utils.t_Bytes

val impl__HashAlgorithm__hash (self: t_HashAlgorithm) (data: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val hkdf_expand (alg: t_HashAlgorithm) (prk info: Bertie.Tls13utils.t_Bytes) (len: usize)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val hkdf_extract (alg: t_HashAlgorithm) (ikm salt: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val hmac_tag (alg: t_HashAlgorithm) (mk input: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl__Algorithms__ciphersuite (self: t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl__Algorithms__check (self: t_Algorithms) (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

val impl__Algorithms__signature_algorithm (self: t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl__Algorithms__supported_group (self: t_Algorithms)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sign
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (algorithm: t_SignatureScheme)
      (sk input: Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : Prims.Pure (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

(*
val supported_rsa_key_size (n: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
*)

val sign_rsa
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (sk pk_modulus pk_exponent: Bertie.Tls13utils.t_Bytes)
      (cert_scheme: t_SignatureScheme)
      (input: Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : Prims.Pure (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val encoding_prefix (alg: t_KemScheme)
    : Prims.Pure Bertie.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val kem_keygen
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (alg: t_KemScheme)
      (rng: impl_916461611_)
    : Prims.Pure
      (impl_916461611_ &
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val into_raw (alg: t_KemScheme) (point: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure Bertie.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val to_shared_secret (alg: t_KemScheme) (shared_secret: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure Bertie.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val kem_decap (alg: t_KemScheme) (ct sk: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val kem_encap
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (alg: t_KemScheme)
      (pk: Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : Prims.Pure
      (impl_916461611_ &
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val zero_key (alg: t_HashAlgorithm)
    : Prims.Pure Bertie.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val hmac_verify (alg: t_HashAlgorithm) (mk input tag: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Convert.t_TryFrom t_Algorithms string =
  {
    f_Error = Bertie.Tls13utils.t_Error;
    f_try_from_pre = (fun (s: string) -> true);
    f_try_from_post
    =
    (fun (s: string) (out: Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error) -> true);
    f_try_from
    =
    fun (s: string) ->
      match s with
      | "SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519" ->
        Core.Result.Result_Ok v_SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | "SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519" ->
        Core.Result.Result_Ok v_SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | "SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256" ->
        Core.Result.Result_Ok v_SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | "SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256" ->
        Core.Result.Result_Ok v_SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | "SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256" ->
        Core.Result.Result_Ok v_SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | "SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519" ->
        Core.Result.Result_Ok v_SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | "SHA256_Aes128Gcm_RsaPssRsaSha256_P256" ->
        Core.Result.Result_Ok v_SHA256_Aes128Gcm_RsaPssRsaSha256_P256
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | "SHA256_Aes128Gcm_RsaPssRsaSha256_X25519" ->
        Core.Result.Result_Ok v_SHA256_Aes128Gcm_RsaPssRsaSha256_X25519
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | "SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256" ->
        Core.Result.Result_Ok v_SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | "SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519" ->
        Core.Result.Result_Ok v_SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | "SHA384_Aes256Gcm_RsaPssRsaSha256_P256" ->
        Core.Result.Result_Ok v_SHA384_Aes256Gcm_RsaPssRsaSha256_P256
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | "SHA384_Aes256Gcm_RsaPssRsaSha256_X25519" ->
        Core.Result.Result_Ok v_SHA384_Aes256Gcm_RsaPssRsaSha256_X25519
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | _ ->
        let res:Alloc.String.t_String =
          Alloc.Fmt.format (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize (let list =
                        ["Invalid ciphersuite description: "]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                  <:
                  t_Slice string)
                (Rust_primitives.unsize (let list =
                        [Core.Fmt.Rt.impl_1__new_display s <: Core.Fmt.Rt.t_Argument]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                  <:
                  t_Slice Core.Fmt.Rt.t_Argument)
              <:
              Core.Fmt.t_Arguments)
        in
        Core.Result.Result_Err
        (Bertie.Tls13utils.Error_UnknownCiphersuite res <: Bertie.Tls13utils.t_Error)
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
  }

type t_AeadKey = {
  f_bytes:Bertie.Tls13utils.t_Bytes;
  f_alg:t_AeadAlgorithm
}

(*
val impl__AeadKey__as_libcrux_key (self: t_AeadKey)
    : Prims.Pure (Core.Result.t_Result Libcrux.Aead.t_Key u8) Prims.l_True (fun _ -> Prims.l_True)
*)
val impl__AeadKey__new (bytes: Bertie.Tls13utils.t_Bytes) (alg: t_AeadAlgorithm)
    : Prims.Pure t_AeadKey Prims.l_True (fun _ -> Prims.l_True)

type t_RsaVerificationKey = {
  f_modulus:Bertie.Tls13utils.t_Bytes;
  f_exponent:Bertie.Tls13utils.t_Bytes
}

type t_PublicVerificationKey =
  | PublicVerificationKey_EcDsa : Bertie.Tls13utils.t_Bytes -> t_PublicVerificationKey
  | PublicVerificationKey_Rsa : t_RsaVerificationKey -> t_PublicVerificationKey

val aead_decrypt (k: t_AeadKey) (iv cip aad: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val aead_encrypt (k: t_AeadKey) (iv plain aad: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val verify
      (alg: t_SignatureScheme)
      (pk: t_PublicVerificationKey)
      (input sig: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

type t_AeadKeyIV = {
  f_key:t_AeadKey;
  f_iv:Bertie.Tls13utils.t_Bytes
}

val impl__AeadKeyIV__new (key: t_AeadKey) (iv: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure t_AeadKeyIV Prims.l_True (fun _ -> Prims.l_True)
