module Bertie.Tls13crypto
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_AeadAlgorithm =
  | AeadAlgorithm_Chacha20Poly1305 : t_AeadAlgorithm
  | AeadAlgorithm_Aes128Gcm : t_AeadAlgorithm
  | AeadAlgorithm_Aes256Gcm : t_AeadAlgorithm

let impl__AeadAlgorithm__iv_len (self: t_AeadAlgorithm) : usize =
  match self with
  | AeadAlgorithm_Chacha20Poly1305  -> sz 12
  | AeadAlgorithm_Aes128Gcm  -> sz 12
  | AeadAlgorithm_Aes256Gcm  -> sz 12

let impl__AeadAlgorithm__key_len (self: t_AeadAlgorithm) : usize =
  match self with
  | AeadAlgorithm_Chacha20Poly1305  -> sz 32
  | AeadAlgorithm_Aes128Gcm  -> sz 16
  | AeadAlgorithm_Aes256Gcm  -> sz 32

type t_HashAlgorithm =
  | HashAlgorithm_SHA256 : t_HashAlgorithm
  | HashAlgorithm_SHA384 : t_HashAlgorithm
  | HashAlgorithm_SHA512 : t_HashAlgorithm

type t_KemScheme =
  | KemScheme_X25519 : t_KemScheme
  | KemScheme_Secp256r1 : t_KemScheme
  | KemScheme_X448 : t_KemScheme
  | KemScheme_Secp384r1 : t_KemScheme
  | KemScheme_Secp521r1 : t_KemScheme

type t_SignatureScheme =
  | SignatureScheme_RsaPssRsaSha256 : t_SignatureScheme
  | SignatureScheme_EcdsaSecp256r1Sha256 : t_SignatureScheme
  | SignatureScheme_ED25519 : t_SignatureScheme

let valid_rsa_exponent (e: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : bool =
  (Alloc.Vec.impl_1__len e <: usize) =. sz 3 && (e.[ sz 0 ] <: u8) =. 1uy &&
  (e.[ sz 1 ] <: u8) =. 0uy &&
  (e.[ sz 2 ] <: u8) =. 1uy

let impl__HashAlgorithm__libcrux_algorithm (self: t_HashAlgorithm)
    : Core.Result.t_Result Libcrux.Digest.t_Algorithm u8 =
  match self with
  | HashAlgorithm_SHA256  ->
    Core.Result.Result_Ok (Libcrux.Digest.Algorithm_Sha256 <: Libcrux.Digest.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Digest.t_Algorithm u8
  | HashAlgorithm_SHA384  ->
    Core.Result.Result_Ok (Libcrux.Digest.Algorithm_Sha384 <: Libcrux.Digest.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Digest.t_Algorithm u8
  | HashAlgorithm_SHA512  ->
    Core.Result.Result_Ok (Libcrux.Digest.Algorithm_Sha512 <: Libcrux.Digest.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Digest.t_Algorithm u8

let impl__HashAlgorithm__hash_len (self: t_HashAlgorithm) : usize =
  match self with
  | HashAlgorithm_SHA256  ->
    Libcrux.Digest.digest_size (Libcrux.Digest.Algorithm_Sha256 <: Libcrux.Digest.t_Algorithm)
  | HashAlgorithm_SHA384  ->
    Libcrux.Digest.digest_size (Libcrux.Digest.Algorithm_Sha384 <: Libcrux.Digest.t_Algorithm)
  | HashAlgorithm_SHA512  ->
    Libcrux.Digest.digest_size (Libcrux.Digest.Algorithm_Sha512 <: Libcrux.Digest.t_Algorithm)

let impl__HashAlgorithm__hmac_tag_len (self: t_HashAlgorithm) : usize =
  impl__HashAlgorithm__hash_len self

let hkdf_algorithm (alg: t_HashAlgorithm) : Core.Result.t_Result Libcrux.Hkdf.t_Algorithm u8 =
  match alg with
  | HashAlgorithm_SHA256  ->
    Core.Result.Result_Ok (Libcrux.Hkdf.Algorithm_Sha256 <: Libcrux.Hkdf.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Hkdf.t_Algorithm u8
  | HashAlgorithm_SHA384  ->
    Core.Result.Result_Ok (Libcrux.Hkdf.Algorithm_Sha384 <: Libcrux.Hkdf.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Hkdf.t_Algorithm u8
  | HashAlgorithm_SHA512  ->
    Core.Result.Result_Ok (Libcrux.Hkdf.Algorithm_Sha512 <: Libcrux.Hkdf.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Hkdf.t_Algorithm u8

let impl__HashAlgorithm__hmac_algorithm (self: t_HashAlgorithm)
    : Core.Result.t_Result Libcrux.Hmac.t_Algorithm u8 =
  match self with
  | HashAlgorithm_SHA256  ->
    Core.Result.Result_Ok (Libcrux.Hmac.Algorithm_Sha256 <: Libcrux.Hmac.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Hmac.t_Algorithm u8
  | HashAlgorithm_SHA384  ->
    Core.Result.Result_Ok (Libcrux.Hmac.Algorithm_Sha384 <: Libcrux.Hmac.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Hmac.t_Algorithm u8
  | HashAlgorithm_SHA512  ->
    Core.Result.Result_Ok (Libcrux.Hmac.Algorithm_Sha512 <: Libcrux.Hmac.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Hmac.t_Algorithm u8

let impl__SignatureScheme__libcrux_scheme (self: t_SignatureScheme)
    : Core.Result.t_Result Libcrux.Signature.t_Algorithm u8 =
  match self with
  | SignatureScheme_RsaPssRsaSha256  ->
    Core.Result.Result_Ok
    (Libcrux.Signature.Algorithm_RsaPss
      (Libcrux.Signature.DigestAlgorithm_Sha256 <: Libcrux.Signature.t_DigestAlgorithm)
      <:
      Libcrux.Signature.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Signature.t_Algorithm u8
  | SignatureScheme_ED25519  ->
    Core.Result.Result_Ok (Libcrux.Signature.Algorithm_Ed25519 <: Libcrux.Signature.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Signature.t_Algorithm u8
  | SignatureScheme_EcdsaSecp256r1Sha256  ->
    Core.Result.Result_Ok
    (Libcrux.Signature.Algorithm_EcDsaP256
      (Libcrux.Signature.DigestAlgorithm_Sha256 <: Libcrux.Signature.t_DigestAlgorithm)
      <:
      Libcrux.Signature.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Signature.t_Algorithm u8

let impl__KemScheme__libcrux_algorithm (self: t_KemScheme)
    : Core.Result.t_Result Libcrux.Kem.t_Algorithm u8 =
  match self with
  | KemScheme_X25519  ->
    Core.Result.Result_Ok (Libcrux.Kem.Algorithm_X25519 <: Libcrux.Kem.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Kem.t_Algorithm u8
  | KemScheme_Secp256r1  ->
    Core.Result.Result_Ok (Libcrux.Kem.Algorithm_Secp256r1 <: Libcrux.Kem.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Kem.t_Algorithm u8
  | _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

type t_Algorithms = {
  f_hash:t_HashAlgorithm;
  f_aead:t_AeadAlgorithm;
  f_signature:t_SignatureScheme;
  f_kem:t_KemScheme;
  f_psk_mode:bool;
  f_zero_rtt:bool
}

let impl__Algorithms__aead (self: t_Algorithms) : t_AeadAlgorithm = self.f_aead

let impl__Algorithms__hash (self: t_Algorithms) : t_HashAlgorithm = self.f_hash

let impl__Algorithms__kem (self: t_Algorithms) : t_KemScheme = self.f_kem

let impl__Algorithms__new
      (hash: t_HashAlgorithm)
      (aead: t_AeadAlgorithm)
      (sig: t_SignatureScheme)
      (kem: t_KemScheme)
      (psk zero_rtt: bool)
    : t_Algorithms =
  {
    f_hash = hash;
    f_aead = aead;
    f_signature = sig;
    f_kem = kem;
    f_psk_mode = psk;
    f_zero_rtt = zero_rtt
  }
  <:
  t_Algorithms

let impl__Algorithms__psk_mode (self: t_Algorithms) : bool = self.f_psk_mode

let impl__Algorithms__signature (self: t_Algorithms) : t_SignatureScheme = self.f_signature

let impl__Algorithms__zero_rtt (self: t_Algorithms) : bool = self.f_zero_rtt

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Fmt.t_Display t_Algorithms =
  {
    f_fmt
    =
    fun (self: t_Algorithms) (f: Core.Fmt.t_Formatter) ->
      let tmp0, out:(Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error) =
        Core.Fmt.impl_7__write_fmt f
          (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize (let list =
                      ["TLS_"; "_"; " w/ "; " | "]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
                    Rust_primitives.Hax.array_of_list list)
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
                    Rust_primitives.Hax.array_of_list list)
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

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Convert.t_TryFrom t_Algorithms string =
  {
    f_Error = Bertie.Tls13utils.t_Error;
    f_try_from
    =
    fun (s: string) ->
      match s with
      | [
        83uy ;
        72uy ;
        65uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        67uy ;
        104uy ;
        97uy ;
        99uy ;
        104uy ;
        97uy ;
        50uy ;
        48uy ;
        80uy ;
        111uy ;
        108uy ;
        121uy ;
        49uy ;
        51uy ;
        48uy ;
        53uy ;
        95uy ;
        82uy ;
        115uy ;
        97uy ;
        80uy ;
        115uy ;
        115uy ;
        82uy ;
        115uy ;
        97uy ;
        83uy ;
        104uy ;
        97uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        88uy ;
        50uy ;
        53uy ;
        53uy ;
        49uy ;
        57uy
      ] ->
        Core.Result.Result_Ok v_SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | [
        83uy ;
        72uy ;
        65uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        67uy ;
        104uy ;
        97uy ;
        99uy ;
        104uy ;
        97uy ;
        50uy ;
        48uy ;
        80uy ;
        111uy ;
        108uy ;
        121uy ;
        49uy ;
        51uy ;
        48uy ;
        53uy ;
        95uy ;
        69uy ;
        99uy ;
        100uy ;
        115uy ;
        97uy ;
        83uy ;
        101uy ;
        99uy ;
        112uy ;
        50uy ;
        53uy ;
        54uy ;
        114uy ;
        49uy ;
        83uy ;
        104uy ;
        97uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        88uy ;
        50uy ;
        53uy ;
        53uy ;
        49uy ;
        57uy
      ] ->
        Core.Result.Result_Ok v_SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | [
        83uy ;
        72uy ;
        65uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        67uy ;
        104uy ;
        97uy ;
        99uy ;
        104uy ;
        97uy ;
        50uy ;
        48uy ;
        80uy ;
        111uy ;
        108uy ;
        121uy ;
        49uy ;
        51uy ;
        48uy ;
        53uy ;
        95uy ;
        69uy ;
        99uy ;
        100uy ;
        115uy ;
        97uy ;
        83uy ;
        101uy ;
        99uy ;
        112uy ;
        50uy ;
        53uy ;
        54uy ;
        114uy ;
        49uy ;
        83uy ;
        104uy ;
        97uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        80uy ;
        50uy ;
        53uy ;
        54uy
      ] ->
        Core.Result.Result_Ok v_SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | [
        83uy ;
        72uy ;
        65uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        67uy ;
        104uy ;
        97uy ;
        99uy ;
        104uy ;
        97uy ;
        50uy ;
        48uy ;
        80uy ;
        111uy ;
        108uy ;
        121uy ;
        49uy ;
        51uy ;
        48uy ;
        53uy ;
        95uy ;
        82uy ;
        115uy ;
        97uy ;
        80uy ;
        115uy ;
        115uy ;
        82uy ;
        115uy ;
        97uy ;
        83uy ;
        104uy ;
        97uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        80uy ;
        50uy ;
        53uy ;
        54uy
      ] ->
        Core.Result.Result_Ok v_SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | [
        83uy ;
        72uy ;
        65uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        65uy ;
        101uy ;
        115uy ;
        49uy ;
        50uy ;
        56uy ;
        71uy ;
        99uy ;
        109uy ;
        95uy ;
        69uy ;
        99uy ;
        100uy ;
        115uy ;
        97uy ;
        83uy ;
        101uy ;
        99uy ;
        112uy ;
        50uy ;
        53uy ;
        54uy ;
        114uy ;
        49uy ;
        83uy ;
        104uy ;
        97uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        80uy ;
        50uy ;
        53uy ;
        54uy
      ] ->
        Core.Result.Result_Ok v_SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | [
        83uy ;
        72uy ;
        65uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        65uy ;
        101uy ;
        115uy ;
        49uy ;
        50uy ;
        56uy ;
        71uy ;
        99uy ;
        109uy ;
        95uy ;
        69uy ;
        99uy ;
        100uy ;
        115uy ;
        97uy ;
        83uy ;
        101uy ;
        99uy ;
        112uy ;
        50uy ;
        53uy ;
        54uy ;
        114uy ;
        49uy ;
        83uy ;
        104uy ;
        97uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        88uy ;
        50uy ;
        53uy ;
        53uy ;
        49uy ;
        57uy
      ] ->
        Core.Result.Result_Ok v_SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | [
        83uy ;
        72uy ;
        65uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        65uy ;
        101uy ;
        115uy ;
        49uy ;
        50uy ;
        56uy ;
        71uy ;
        99uy ;
        109uy ;
        95uy ;
        82uy ;
        115uy ;
        97uy ;
        80uy ;
        115uy ;
        115uy ;
        82uy ;
        115uy ;
        97uy ;
        83uy ;
        104uy ;
        97uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        80uy ;
        50uy ;
        53uy ;
        54uy
      ] ->
        Core.Result.Result_Ok v_SHA256_Aes128Gcm_RsaPssRsaSha256_P256
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | [
        83uy ;
        72uy ;
        65uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        65uy ;
        101uy ;
        115uy ;
        49uy ;
        50uy ;
        56uy ;
        71uy ;
        99uy ;
        109uy ;
        95uy ;
        82uy ;
        115uy ;
        97uy ;
        80uy ;
        115uy ;
        115uy ;
        82uy ;
        115uy ;
        97uy ;
        83uy ;
        104uy ;
        97uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        88uy ;
        50uy ;
        53uy ;
        53uy ;
        49uy ;
        57uy
      ] ->
        Core.Result.Result_Ok v_SHA256_Aes128Gcm_RsaPssRsaSha256_X25519
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | [
        83uy ;
        72uy ;
        65uy ;
        51uy ;
        56uy ;
        52uy ;
        95uy ;
        65uy ;
        101uy ;
        115uy ;
        50uy ;
        53uy ;
        54uy ;
        71uy ;
        99uy ;
        109uy ;
        95uy ;
        69uy ;
        99uy ;
        100uy ;
        115uy ;
        97uy ;
        83uy ;
        101uy ;
        99uy ;
        112uy ;
        50uy ;
        53uy ;
        54uy ;
        114uy ;
        49uy ;
        83uy ;
        104uy ;
        97uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        80uy ;
        50uy ;
        53uy ;
        54uy
      ] ->
        Core.Result.Result_Ok v_SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | [
        83uy ;
        72uy ;
        65uy ;
        51uy ;
        56uy ;
        52uy ;
        95uy ;
        65uy ;
        101uy ;
        115uy ;
        50uy ;
        53uy ;
        54uy ;
        71uy ;
        99uy ;
        109uy ;
        95uy ;
        69uy ;
        99uy ;
        100uy ;
        115uy ;
        97uy ;
        83uy ;
        101uy ;
        99uy ;
        112uy ;
        50uy ;
        53uy ;
        54uy ;
        114uy ;
        49uy ;
        83uy ;
        104uy ;
        97uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        88uy ;
        50uy ;
        53uy ;
        53uy ;
        49uy ;
        57uy
      ] ->
        Core.Result.Result_Ok v_SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | [
        83uy ;
        72uy ;
        65uy ;
        51uy ;
        56uy ;
        52uy ;
        95uy ;
        65uy ;
        101uy ;
        115uy ;
        50uy ;
        53uy ;
        54uy ;
        71uy ;
        99uy ;
        109uy ;
        95uy ;
        82uy ;
        115uy ;
        97uy ;
        80uy ;
        115uy ;
        115uy ;
        82uy ;
        115uy ;
        97uy ;
        83uy ;
        104uy ;
        97uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        80uy ;
        50uy ;
        53uy ;
        54uy
      ] ->
        Core.Result.Result_Ok v_SHA384_Aes256Gcm_RsaPssRsaSha256_P256
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | [
        83uy ;
        72uy ;
        65uy ;
        51uy ;
        56uy ;
        52uy ;
        95uy ;
        65uy ;
        101uy ;
        115uy ;
        50uy ;
        53uy ;
        54uy ;
        71uy ;
        99uy ;
        109uy ;
        95uy ;
        82uy ;
        115uy ;
        97uy ;
        80uy ;
        115uy ;
        115uy ;
        82uy ;
        115uy ;
        97uy ;
        83uy ;
        104uy ;
        97uy ;
        50uy ;
        53uy ;
        54uy ;
        95uy ;
        88uy ;
        50uy ;
        53uy ;
        53uy ;
        49uy ;
        57uy
      ] ->
        Core.Result.Result_Ok v_SHA384_Aes256Gcm_RsaPssRsaSha256_X25519
        <:
        Core.Result.t_Result t_Algorithms Bertie.Tls13utils.t_Error
      | _ ->
        let res:Alloc.String.t_String =
          Alloc.Fmt.format (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize (let list =
                        ["Invalid ciphersuite description: "]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list list)
                  <:
                  t_Slice string)
                (Rust_primitives.unsize (let list =
                        [Core.Fmt.Rt.impl_1__new_display s <: Core.Fmt.Rt.t_Argument]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list list)
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

let impl__HashAlgorithm__hash (self: t_HashAlgorithm) (data: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist16:Libcrux.Digest.t_Algorithm =
        match
          Core.Ops.Try_trait.f_branch (impl__HashAlgorithm__libcrux_algorithm self
              <:
              Core.Result.t_Result Libcrux.Digest.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist15:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist15)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Digest.t_Algorithm
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Digest.t_Algorithm
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist17:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
          Libcrux.Digest.hash hoist16
            (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify data
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              t_Slice u8)
        in
        let hoist18:Bertie.Tls13utils.t_Bytes = Core.Convert.f_into hoist17 in
        Core.Result.Result_Ok hoist18 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let hkdf_expand (alg: t_HashAlgorithm) (prk info: Bertie.Tls13utils.t_Bytes) (len: usize)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist20:Libcrux.Hkdf.t_Algorithm =
        match
          Core.Ops.Try_trait.f_branch (hkdf_algorithm alg
              <:
              Core.Result.t_Result Libcrux.Hkdf.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist19:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist19)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Hkdf.t_Algorithm
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Hkdf.t_Algorithm
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist21:Core.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          Libcrux.Hkdf.t_Error =
          Libcrux.Hkdf.expand hoist20
            (Bertie.Tls13utils.impl__Bytes__declassify prk
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            (Bertie.Tls13utils.impl__Bytes__declassify info
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            len
        in
        match hoist21 with
        | Core.Result.Result_Ok x ->
          Core.Result.Result_Ok (Core.Convert.f_into x)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | Core.Result.Result_Err _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let hkdf_extract (alg: t_HashAlgorithm) (ikm salt: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist23:Libcrux.Hkdf.t_Algorithm =
        match
          Core.Ops.Try_trait.f_branch (hkdf_algorithm alg
              <:
              Core.Result.t_Result Libcrux.Hkdf.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist22:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist22)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Hkdf.t_Algorithm
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Hkdf.t_Algorithm
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist24:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
          Libcrux.Hkdf.extract hoist23
            (Bertie.Tls13utils.impl__Bytes__declassify salt
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            (Bertie.Tls13utils.impl__Bytes__declassify ikm
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        in
        let hoist25:Bertie.Tls13utils.t_Bytes = Core.Convert.f_into hoist24 in
        Core.Result.Result_Ok hoist25 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let hmac_tag (alg: t_HashAlgorithm) (mk input: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist27:Libcrux.Hmac.t_Algorithm =
        match
          Core.Ops.Try_trait.f_branch (impl__HashAlgorithm__hmac_algorithm alg
              <:
              Core.Result.t_Result Libcrux.Hmac.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist26:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist26)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Hmac.t_Algorithm
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Hmac.t_Algorithm
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist28:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
          Libcrux.Hmac.hmac hoist27
            (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify mk
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              t_Slice u8)
            (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify input
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              t_Slice u8)
            (Core.Option.Option_None <: Core.Option.t_Option usize)
        in
        let hoist29:Bertie.Tls13utils.t_Bytes = Core.Convert.f_into hoist28 in
        Core.Result.Result_Ok hoist29 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let impl__Algorithms__ciphersuite (self: t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  match self.f_hash, self.f_aead <: (t_HashAlgorithm & t_AeadAlgorithm) with
  | HashAlgorithm_SHA256 , AeadAlgorithm_Aes128Gcm  ->
    Core.Result.Result_Ok
    (Core.Convert.f_into (let list = [19uy; 1uy] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list list))
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | HashAlgorithm_SHA384 , AeadAlgorithm_Aes256Gcm  ->
    Core.Result.Result_Ok
    (Core.Convert.f_into (let list = [19uy; 2uy] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list list))
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | HashAlgorithm_SHA256 , AeadAlgorithm_Chacha20Poly1305  ->
    Core.Result.Result_Ok
    (Core.Convert.f_into (let list = [19uy; 3uy] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list list))
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let impl__Algorithms__check (self: t_Algorithms) (bytes: t_Slice Bertie.Tls13utils.t_U8)
    : Core.Result.t_Result usize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u16_encoded bytes
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist33:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist33)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result usize u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result usize u8) usize
      in
      let* cs:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (impl__Algorithms__ciphersuite self
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist34:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist34)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result usize u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result usize u8)
            Bertie.Tls13utils.t_Bytes
      in
      let csl:t_Slice Bertie.Tls13utils.t_U8 =
        bytes.[ { Core.Ops.Range.f_start = sz 2; Core.Ops.Range.f_end = sz 2 +! len <: usize }
          <:
          Core.Ops.Range.t_Range usize ]
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_mem (Bertie.Tls13utils.impl__Bytes__as_raw
                    cs
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
                csl
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist35:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist35)
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

let impl__Algorithms__signature_algorithm (self: t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  match impl__Algorithms__signature self with
  | SignatureScheme_RsaPssRsaSha256  ->
    Core.Result.Result_Ok
    (Core.Convert.f_into (let list = [8uy; 4uy] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list list))
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | SignatureScheme_EcdsaSecp256r1Sha256  ->
    Core.Result.Result_Ok
    (Core.Convert.f_into (let list = [4uy; 3uy] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list list))
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | SignatureScheme_ED25519  -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let impl__Algorithms__supported_group (self: t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  match impl__Algorithms__kem self with
  | KemScheme_X25519  ->
    Core.Result.Result_Ok
    (Core.Convert.f_into (let list = [0uy; 29uy] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list list))
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | KemScheme_Secp256r1  ->
    Core.Result.Result_Ok
    (Core.Convert.f_into (let list = [0uy; 23uy] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list list))
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | KemScheme_X448  -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
  | KemScheme_Secp384r1  -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
  | KemScheme_Secp521r1  -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let sign
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (algorithm: t_SignatureScheme)
      (sk input: Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* rng, sig:(impl_916461611_ &
        Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error) =
        match algorithm with
        | SignatureScheme_EcdsaSecp256r1Sha256  ->
          let* hoist56:Libcrux.Signature.t_Algorithm =
            match
              Core.Ops.Try_trait.f_branch (impl__SignatureScheme__libcrux_scheme algorithm
                  <:
                  Core.Result.t_Result Libcrux.Signature.t_Algorithm u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist55:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                    <:
                    (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist55)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                Libcrux.Signature.t_Algorithm
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                Libcrux.Signature.t_Algorithm
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let tmp0, out:(impl_916461611_ &
              Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error) =
              Libcrux.Signature.sign hoist56
                (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify input
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  t_Slice u8)
                (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify sk
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  t_Slice u8)
                rng
            in
            let rng:impl_916461611_ = tmp0 in
            rng, out
            <:
            (impl_916461611_ &
              Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (impl_916461611_ &
              Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error)
        | SignatureScheme_ED25519  ->
          let* hoist58:Libcrux.Signature.t_Algorithm =
            match
              Core.Ops.Try_trait.f_branch (impl__SignatureScheme__libcrux_scheme algorithm
                  <:
                  Core.Result.t_Result Libcrux.Signature.t_Algorithm u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist57:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                    <:
                    (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist57)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                Libcrux.Signature.t_Algorithm
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                Libcrux.Signature.t_Algorithm
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let tmp0, out:(impl_916461611_ &
              Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error) =
              Libcrux.Signature.sign hoist58
                (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify input
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  t_Slice u8)
                (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify sk
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  t_Slice u8)
                rng
            in
            let rng:impl_916461611_ = tmp0 in
            rng, out
            <:
            (impl_916461611_ &
              Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (impl_916461611_ &
              Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error)
        | SignatureScheme_RsaPssRsaSha256  ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (rng,
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_const (Rust_primitives.unsize
                          (let list = ["wrong function, use sign_rsa"] in
                            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                            Rust_primitives.Hax.array_of_list list)
                        <:
                        t_Slice string)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
            <:
            (impl_916461611_ &
              Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (impl_916461611_ &
              Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hax_temp_output:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
          match sig with
          | Core.Result.Result_Ok (Libcrux.Signature.Signature_Ed25519 sig) ->
            Core.Result.Result_Ok
            (Core.Convert.f_into (Libcrux.Signature.impl__Ed25519Signature__as_bytes sig
                  <:
                  t_Array u8 (sz 64)))
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          | Core.Result.Result_Ok (Libcrux.Signature.Signature_EcDsaP256 sig) ->
            let r, s:(t_Array u8 (sz 32) & t_Array u8 (sz 32)) =
              Libcrux.Signature.impl__EcDsaP256Signature__as_bytes sig
            in
            Core.Result.Result_Ok
            (Bertie.Tls13utils.impl__Bytes__concat (Core.Convert.f_from r
                  <:
                  Bertie.Tls13utils.t_Bytes)
                (Core.Convert.f_from s <: Bertie.Tls13utils.t_Bytes))
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          | Core.Result.Result_Ok (Libcrux.Signature.Signature_RsaPss sig) ->
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_const (Rust_primitives.unsize
                          (let list = ["wrong function, use sign_rsa"] in
                            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                            Rust_primitives.Hax.array_of_list list)
                        <:
                        t_Slice string)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
          | Core.Result.Result_Err _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR
        in
        rng, hax_temp_output
        <:
        (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let supported_rsa_key_size (n: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* key_size:Libcrux.Signature.Rsa_pss.t_RsaPssKeySize
      =
        match cast (Bertie.Tls13utils.impl__Bytes__len n <: usize) <: u16 with
        | 257us ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (Libcrux.Signature.Rsa_pss.RsaPssKeySize_N2048
            <:
            Libcrux.Signature.Rsa_pss.t_RsaPssKeySize)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
            Libcrux.Signature.Rsa_pss.t_RsaPssKeySize
        | 385us ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (Libcrux.Signature.Rsa_pss.RsaPssKeySize_N3072
            <:
            Libcrux.Signature.Rsa_pss.t_RsaPssKeySize)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
            Libcrux.Signature.Rsa_pss.t_RsaPssKeySize
        | 513us ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (Libcrux.Signature.Rsa_pss.RsaPssKeySize_N4096
            <:
            Libcrux.Signature.Rsa_pss.t_RsaPssKeySize)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
            Libcrux.Signature.Rsa_pss.t_RsaPssKeySize
        | 769us ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (Libcrux.Signature.Rsa_pss.RsaPssKeySize_N6144
            <:
            Libcrux.Signature.Rsa_pss.t_RsaPssKeySize)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
            Libcrux.Signature.Rsa_pss.t_RsaPssKeySize
        | 1025us ->
          Core.Ops.Control_flow.ControlFlow_Continue
          (Libcrux.Signature.Rsa_pss.RsaPssKeySize_N8192
            <:
            Libcrux.Signature.Rsa_pss.t_RsaPssKeySize)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
            Libcrux.Signature.Rsa_pss.t_RsaPssKeySize
        | _ ->
          let* hoist59:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

                <:
                Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist59)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
            Libcrux.Signature.Rsa_pss.t_RsaPssKeySize
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok key_size
        <:
        Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
        (Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8))

let sign_rsa
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (sk pk_modulus pk_exponent: Bertie.Tls13utils.t_Bytes)
      (cert_scheme: t_SignatureScheme)
      (input: Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let salt:t_Array u8 (sz 32) =
        Rust_primitives.Hax.repeat 0uy (sz 32)
      in
      let tmp0, tmp1:(impl_916461611_ & t_Array u8 (sz 32)) = Rand_core.f_fill_bytes rng salt in
      let rng:impl_916461611_ = tmp0 in
      let salt:t_Array u8 (sz 32) = tmp1 in
      let _:Prims.unit = () in
      let* _:Prims.unit =
        if
          ~.(match cert_scheme with
            | SignatureScheme_RsaPssRsaSha256  -> true
            | _ -> false)
        then
          let* hoist60:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                <:
                (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist60)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Prims.unit
        else
          Core.Ops.Control_flow.ControlFlow_Continue ()
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Prims.unit
      in
      let* _:Prims.unit =
        if
          ~.(valid_rsa_exponent (Bertie.Tls13utils.impl__Bytes__declassify pk_exponent
                <:
                Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            <:
            bool)
        then
          let* hoist61:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                <:
                (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist61)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Prims.unit
        else
          Core.Ops.Control_flow.ControlFlow_Continue ()
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Prims.unit
      in
      let* key_size:Libcrux.Signature.Rsa_pss.t_RsaPssKeySize =
        match
          Core.Ops.Try_trait.f_branch (supported_rsa_key_size pk_modulus
              <:
              Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist62:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                <:
                (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist62)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Signature.Rsa_pss.t_RsaPssKeySize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Signature.Rsa_pss.t_RsaPssKeySize
      in
      let* pk:Libcrux.Signature.Rsa_pss.t_RsaPssPublicKey =
        match
          Core.Ops.Try_trait.f_branch (Core.Result.impl__map_err (Libcrux.Signature.Rsa_pss.impl__RsaPssPublicKey__new
                    key_size
                    ((Bertie.Tls13utils.impl__Bytes__declassify pk_modulus
                        <:
                        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global).[ { Core.Ops.Range.f_start = sz 1 }
                        <:
                        Core.Ops.Range.t_RangeFrom usize ]
                      <:
                      t_Slice u8)
                  <:
                  Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssPublicKey
                    Libcrux.Signature.t_Error)
                (fun temp_0_ ->
                    let _:Libcrux.Signature.t_Error = temp_0_ in
                    Bertie.Tls13utils.v_CRYPTO_ERROR)
              <:
              Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssPublicKey u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist63:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                <:
                (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist63)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Signature.Rsa_pss.t_RsaPssPublicKey
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Signature.Rsa_pss.t_RsaPssPublicKey
      in
      let* sk:Libcrux.Signature.Rsa_pss.t_RsaPssPrivateKey =
        match
          Core.Ops.Try_trait.f_branch (Core.Result.impl__map_err (Libcrux.Signature.Rsa_pss.impl_5__new
                    pk
                    (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify sk
                          <:
                          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                      <:
                      t_Slice u8)
                  <:
                  Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssPrivateKey
                    Libcrux.Signature.t_Error)
                (fun temp_0_ ->
                    let _:Libcrux.Signature.t_Error = temp_0_ in
                    Bertie.Tls13utils.v_CRYPTO_ERROR)
              <:
              Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssPrivateKey u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist64:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                <:
                (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist64)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Signature.Rsa_pss.t_RsaPssPrivateKey
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Signature.Rsa_pss.t_RsaPssPrivateKey
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let msg:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
          Bertie.Tls13utils.impl__Bytes__declassify input
        in
        let sig:Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssSignature
          Libcrux.Signature.t_Error =
          Libcrux.Signature.Rsa_pss.impl_5__sign sk
            (Libcrux.Signature.DigestAlgorithm_Sha256 <: Libcrux.Signature.t_DigestAlgorithm)
            (Rust_primitives.unsize salt <: t_Slice u8)
            (Core.Ops.Deref.f_deref msg <: t_Slice u8)
        in
        let hax_temp_output:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
          Core.Result.impl__map_err (Core.Result.impl__map sig
                (fun sig ->
                    let sig:Libcrux.Signature.Rsa_pss.t_RsaPssSignature = sig in
                    Core.Convert.f_into (Libcrux.Signature.Rsa_pss.impl__RsaPssSignature__as_bytes sig

                        <:
                        t_Slice u8)
                    <:
                    Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes Libcrux.Signature.t_Error)
            (fun temp_0_ ->
                let _:Libcrux.Signature.t_Error = temp_0_ in
                Bertie.Tls13utils.v_CRYPTO_ERROR)
        in
        rng, hax_temp_output
        <:
        (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let encoding_prefix (alg: t_KemScheme) : Bertie.Tls13utils.t_Bytes =
  if
    alg =. (KemScheme_Secp256r1 <: t_KemScheme) || alg =. (KemScheme_Secp384r1 <: t_KemScheme) ||
    alg =. (KemScheme_Secp521r1 <: t_KemScheme)
  then
    Core.Convert.f_from (let list = [4uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list list)
  else Bertie.Tls13utils.impl__Bytes__new ()

let kem_keygen
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (alg: t_KemScheme)
      (rng: impl_916461611_)
    : (impl_916461611_ &
      Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8) =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist66:Libcrux.Kem.t_Algorithm =
        match
          Core.Ops.Try_trait.f_branch (impl__KemScheme__libcrux_algorithm alg
              <:
              Core.Result.t_Result Libcrux.Kem.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist65:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist65)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Libcrux.Kem.t_Algorithm
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Libcrux.Kem.t_Algorithm
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let tmp0, out:(impl_916461611_ &
          Core.Result.t_Result (Libcrux.Kem.t_PrivateKey & Libcrux.Kem.t_PublicKey)
            Libcrux.Kem.t_Error) =
          Libcrux.Kem.key_gen hoist66 rng
        in
        let rng:impl_916461611_ = tmp0 in
        let res:Core.Result.t_Result (Libcrux.Kem.t_PrivateKey & Libcrux.Kem.t_PublicKey)
          Libcrux.Kem.t_Error =
          out
        in
        let hax_temp_output:Core.Result.t_Result
          (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
          match res with
          | Core.Result.Result_Ok (sk, pk) ->
            Core.Result.Result_Ok
            (Core.Convert.f_from (Libcrux.Kem.impl__PrivateKey__encode sk
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global),
              Bertie.Tls13utils.impl__Bytes__concat (encoding_prefix alg
                  <:
                  Bertie.Tls13utils.t_Bytes)
                (Core.Convert.f_from (Libcrux.Kem.impl__PublicKey__encode pk
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
            <:
            Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8
          | Core.Result.Result_Err _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR
        in
        rng, hax_temp_output
        <:
        (impl_916461611_ &
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (impl_916461611_ &
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        (impl_916461611_ &
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8))

let into_raw (alg: t_KemScheme) (point: Bertie.Tls13utils.t_Bytes) : Bertie.Tls13utils.t_Bytes =
  if
    alg =. (KemScheme_Secp256r1 <: t_KemScheme) || alg =. (KemScheme_Secp384r1 <: t_KemScheme) ||
    alg =. (KemScheme_Secp521r1 <: t_KemScheme)
  then
    Core.Convert.f_into (Bertie.Tls13utils.impl__Bytes__slice_range point
          ({
              Core.Ops.Range.f_start = sz 1;
              Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len point <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Bertie.Tls13utils.t_Bytes)
  else point

let to_shared_secret (alg: t_KemScheme) (shared_secret: Bertie.Tls13utils.t_Bytes)
    : Bertie.Tls13utils.t_Bytes =
  if alg =. (KemScheme_Secp256r1 <: t_KemScheme)
  then
    Core.Convert.f_into (Bertie.Tls13utils.impl__Bytes__slice_range shared_secret
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 32 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Bertie.Tls13utils.t_Bytes)
  else
    if alg =. (KemScheme_Secp384r1 <: t_KemScheme) || alg =. (KemScheme_Secp521r1 <: t_KemScheme)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize
                    (let list = ["not implemented: not supported yet"] in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list list)
                  <:
                  t_Slice string)
                (Rust_primitives.unsize (Core.Fmt.Rt.impl_1__none ()
                      <:
                      t_Array Core.Fmt.Rt.t_Argument (sz 0))
                  <:
                  t_Slice Core.Fmt.Rt.t_Argument)
              <:
              Core.Fmt.t_Arguments)
          <:
          Rust_primitives.Hax.t_Never)
    else shared_secret

let kem_decap (alg: t_KemScheme) (ct sk: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* librux_algorithm:Libcrux.Kem.t_Algorithm
      =
        match
          Core.Ops.Try_trait.f_branch (impl__KemScheme__libcrux_algorithm alg
              <:
              Core.Result.t_Result Libcrux.Kem.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist68:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist68)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Kem.t_Algorithm
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Kem.t_Algorithm
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let sk:Libcrux.Kem.t_PrivateKey =
          Core.Result.impl__unwrap (Libcrux.Kem.impl__PrivateKey__decode librux_algorithm
                (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify sk
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Libcrux.Kem.t_PrivateKey Libcrux.Kem.t_Error)
        in
        let ct:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
          Bertie.Tls13utils.impl__Bytes__declassify (into_raw alg
                (Core.Clone.f_clone ct <: Bertie.Tls13utils.t_Bytes)
              <:
              Bertie.Tls13utils.t_Bytes)
        in
        let ct:Libcrux.Kem.t_Ct =
          Core.Result.impl__unwrap (Libcrux.Kem.impl__Ct__decode librux_algorithm
                (Core.Ops.Deref.f_deref ct <: t_Slice u8)
              <:
              Core.Result.t_Result Libcrux.Kem.t_Ct Libcrux.Kem.t_Error)
        in
        let res:Core.Result.t_Result Libcrux.Kem.t_Ss Libcrux.Kem.t_Error =
          Libcrux.Kem.decapsulate ct sk
        in
        match res with
        | Core.Result.Result_Ok shared_secret ->
          let (shared_secret: Bertie.Tls13utils.t_Bytes):Bertie.Tls13utils.t_Bytes =
            Core.Convert.f_into (Libcrux.Kem.impl__Ss__encode shared_secret
                <:
                Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          in
          let shared_secret:Bertie.Tls13utils.t_Bytes = to_shared_secret alg shared_secret in
          Core.Result.Result_Ok shared_secret <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | Core.Result.Result_Err _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let kem_encap
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (alg: t_KemScheme)
      (pk: Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : (impl_916461611_ &
      Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8) =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let pk:Bertie.Tls13utils.t_Bytes =
        into_raw alg (Core.Clone.f_clone pk <: Bertie.Tls13utils.t_Bytes)
      in
      let* hoist70:Libcrux.Kem.t_Algorithm =
        match
          Core.Ops.Try_trait.f_branch (impl__KemScheme__libcrux_algorithm alg
              <:
              Core.Result.t_Result Libcrux.Kem.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist69:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist69)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Libcrux.Kem.t_Algorithm
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Libcrux.Kem.t_Algorithm
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist71:Core.Result.t_Result Libcrux.Kem.t_PublicKey Libcrux.Kem.t_Error =
          Libcrux.Kem.impl__PublicKey__decode hoist70
            (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify pk
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              t_Slice u8)
        in
        let pk:Libcrux.Kem.t_PublicKey = Core.Result.impl__unwrap hoist71 in
        let tmp0, out:(impl_916461611_ &
          Core.Result.t_Result (Libcrux.Kem.t_Ss & Libcrux.Kem.t_Ct) Libcrux.Kem.t_Error) =
          Libcrux.Kem.encapsulate pk rng
        in
        let rng:impl_916461611_ = tmp0 in
        let res:Core.Result.t_Result (Libcrux.Kem.t_Ss & Libcrux.Kem.t_Ct) Libcrux.Kem.t_Error =
          out
        in
        let hax_temp_output:Core.Result.t_Result
          (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
          match res with
          | Core.Result.Result_Ok (shared_secret, ct) ->
            let ct:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__concat (encoding_prefix alg
                  <:
                  Bertie.Tls13utils.t_Bytes)
                (Core.Convert.f_from (Libcrux.Kem.impl__Ct__encode ct
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  Bertie.Tls13utils.t_Bytes)
            in
            let shared_secret:Bertie.Tls13utils.t_Bytes =
              to_shared_secret alg
                (Core.Convert.f_from (Libcrux.Kem.impl__Ss__encode shared_secret
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  Bertie.Tls13utils.t_Bytes)
            in
            Core.Result.Result_Ok
            (shared_secret, ct <: (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
            <:
            Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8
          | Core.Result.Result_Err _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR
        in
        rng, hax_temp_output
        <:
        (impl_916461611_ &
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (impl_916461611_ &
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        (impl_916461611_ &
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8))

let zero_key (alg: t_HashAlgorithm) : Bertie.Tls13utils.t_Bytes =
  Bertie.Tls13utils.impl__Bytes__zeroes (impl__HashAlgorithm__hash_len alg <: usize)

let hmac_verify (alg: t_HashAlgorithm) (mk input tag: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist250:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (hmac_tag alg mk input
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist249:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist249)
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
      (let hoist251:bool = Bertie.Tls13utils.eq hoist250 tag in
        if hoist251
        then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
        else Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

type t_AeadKey = {
  f_bytes:Bertie.Tls13utils.t_Bytes;
  f_alg:t_AeadAlgorithm
}

let impl__AeadKey__as_libcrux_key (self: t_AeadKey) : Core.Result.t_Result Libcrux.Aead.t_Key u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (match self.f_alg with
      | AeadAlgorithm_Chacha20Poly1305  ->
        let* hoist258:t_Array u8 (sz 32) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 32)
                  self.f_bytes
                <:
                Core.Result.t_Result (t_Array u8 (sz 32)) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist257:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Libcrux.Aead.t_Key u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist257)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Libcrux.Aead.t_Key u8)
              (t_Array u8 (sz 32))
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Libcrux.Aead.t_Key u8)
              (t_Array u8 (sz 32))
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let hoist259:Libcrux.Aead.t_Chacha20Key =
            Libcrux.Aead.Chacha20Key hoist258 <: Libcrux.Aead.t_Chacha20Key
          in
          let hoist260:Libcrux.Aead.t_Key =
            Libcrux.Aead.Key_Chacha20Poly1305 hoist259 <: Libcrux.Aead.t_Key
          in
          Core.Result.Result_Ok hoist260 <: Core.Result.t_Result Libcrux.Aead.t_Key u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Libcrux.Aead.t_Key u8)
          (Core.Result.t_Result Libcrux.Aead.t_Key u8)
      | AeadAlgorithm_Aes128Gcm  ->
        let* hoist262:t_Array u8 (sz 16) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 16)
                  self.f_bytes
                <:
                Core.Result.t_Result (t_Array u8 (sz 16)) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist261:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Libcrux.Aead.t_Key u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist261)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Libcrux.Aead.t_Key u8)
              (t_Array u8 (sz 16))
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Libcrux.Aead.t_Key u8)
              (t_Array u8 (sz 16))
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let hoist263:Libcrux.Aead.t_Aes128Key =
            Libcrux.Aead.Aes128Key hoist262 <: Libcrux.Aead.t_Aes128Key
          in
          let hoist264:Libcrux.Aead.t_Key =
            Libcrux.Aead.Key_Aes128 hoist263 <: Libcrux.Aead.t_Key
          in
          Core.Result.Result_Ok hoist264 <: Core.Result.t_Result Libcrux.Aead.t_Key u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Libcrux.Aead.t_Key u8)
          (Core.Result.t_Result Libcrux.Aead.t_Key u8)
      | AeadAlgorithm_Aes256Gcm  ->
        let* hoist266:t_Array u8 (sz 32) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 32)
                  self.f_bytes
                <:
                Core.Result.t_Result (t_Array u8 (sz 32)) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist265:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Libcrux.Aead.t_Key u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist265)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Libcrux.Aead.t_Key u8)
              (t_Array u8 (sz 32))
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Libcrux.Aead.t_Key u8)
              (t_Array u8 (sz 32))
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let hoist267:Libcrux.Aead.t_Aes256Key =
            Libcrux.Aead.Aes256Key hoist266 <: Libcrux.Aead.t_Aes256Key
          in
          let hoist268:Libcrux.Aead.t_Key =
            Libcrux.Aead.Key_Aes256 hoist267 <: Libcrux.Aead.t_Key
          in
          Core.Result.Result_Ok hoist268 <: Core.Result.t_Result Libcrux.Aead.t_Key u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Libcrux.Aead.t_Key u8)
          (Core.Result.t_Result Libcrux.Aead.t_Key u8))

let impl__AeadKey__new (bytes: Bertie.Tls13utils.t_Bytes) (alg: t_AeadAlgorithm) : t_AeadKey =
  { f_bytes = bytes; f_alg = alg } <: t_AeadKey

type t_RsaVerificationKey = {
  f_modulus:Bertie.Tls13utils.t_Bytes;
  f_exponent:Bertie.Tls13utils.t_Bytes
}

type t_PublicVerificationKey =
  | PublicVerificationKey_EcDsa : Bertie.Tls13utils.t_Bytes -> t_PublicVerificationKey
  | PublicVerificationKey_Rsa : t_RsaVerificationKey -> t_PublicVerificationKey

let aead_decrypt (k: t_AeadKey) (iv cip aad: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let tag:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice cip
          ((Bertie.Tls13utils.impl__Bytes__len cip <: usize) -! sz 16 <: usize)
          (sz 16)
      in
      let cip:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice cip
          (sz 0)
          ((Bertie.Tls13utils.impl__Bytes__len cip <: usize) -! sz 16 <: usize)
      in
      let* (tag: t_Array u8 (sz 16)):t_Array u8 (sz 16) =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 16) tag
              <:
              Core.Result.t_Result (t_Array u8 (sz 16)) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist277:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist277)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (t_Array u8 (sz 16))
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (t_Array u8 (sz 16))
      in
      let* hoist282:Libcrux.Aead.t_Key =
        match
          Core.Ops.Try_trait.f_branch (impl__AeadKey__as_libcrux_key k
              <:
              Core.Result.t_Result Libcrux.Aead.t_Key u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist278:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist278)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Aead.t_Key
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Aead.t_Key
      in
      let* hoist280:t_Array u8 (sz 12) =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 12) iv
              <:
              Core.Result.t_Result (t_Array u8 (sz 12)) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist279:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist279)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (t_Array u8 (sz 12))
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (t_Array u8 (sz 12))
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist281:Libcrux.Aead.t_Iv = Libcrux.Aead.Iv hoist280 <: Libcrux.Aead.t_Iv in
        let plain:Core.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          Libcrux.Aead.t_Error =
          Libcrux.Aead.decrypt_detached hoist282
            (Bertie.Tls13utils.impl__Bytes__declassify cip
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            hoist281
            (Bertie.Tls13utils.impl__Bytes__declassify aad
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            (Core.Convert.f_from tag <: Libcrux.Aead.t_Tag)
        in
        match plain with
        | Core.Result.Result_Ok plain ->
          Core.Result.Result_Ok (Core.Convert.f_into plain)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | Core.Result.Result_Err _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let aead_encrypt (k: t_AeadKey) (iv plain aad: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist287:Libcrux.Aead.t_Key =
        match
          Core.Ops.Try_trait.f_branch (impl__AeadKey__as_libcrux_key k
              <:
              Core.Result.t_Result Libcrux.Aead.t_Key u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist283:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist283)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Aead.t_Key
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Aead.t_Key
      in
      let* hoist285:t_Array u8 (sz 12) =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 12) iv
              <:
              Core.Result.t_Result (t_Array u8 (sz 12)) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist284:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist284)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (t_Array u8 (sz 12))
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (t_Array u8 (sz 12))
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist286:Libcrux.Aead.t_Iv = Libcrux.Aead.Iv hoist285 <: Libcrux.Aead.t_Iv in
        let res:Core.Result.t_Result (Libcrux.Aead.t_Tag & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          Libcrux.Aead.t_Error =
          Libcrux.Aead.encrypt_detached hoist287
            (Bertie.Tls13utils.impl__Bytes__declassify plain
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            hoist286
            (Bertie.Tls13utils.impl__Bytes__declassify aad
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        in
        match res with
        | Core.Result.Result_Ok (tag, cip) ->
          let (cipby: Bertie.Tls13utils.t_Bytes):Bertie.Tls13utils.t_Bytes =
            Core.Convert.f_into cip
          in
          let (tagby: Bertie.Tls13utils.t_Bytes):Bertie.Tls13utils.t_Bytes =
            Core.Convert.f_into (Core.Convert.f_as_ref tag <: t_Slice u8)
          in
          Core.Result.Result_Ok (Bertie.Tls13utils.impl__Bytes__concat cipby tagby)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | Core.Result.Result_Err _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let verify
      (alg: t_SignatureScheme)
      (pk: t_PublicVerificationKey)
      (input sig: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (match
        alg, pk <: (t_SignatureScheme & t_PublicVerificationKey)
      with
      | SignatureScheme_ED25519 , PublicVerificationKey_EcDsa pk ->
        let* hoist289:t_Array u8 (sz 64) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 64) sig
                <:
                Core.Result.t_Result (t_Array u8 (sz 64)) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist288:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Prims.unit u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist288)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
              (t_Array u8 (sz 64))
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
              (t_Array u8 (sz 64))
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let hoist290:Libcrux.Signature.t_Ed25519Signature =
            Libcrux.Signature.impl__Ed25519Signature__from_bytes hoist289
          in
          let hoist291:Libcrux.Signature.t_Signature =
            Libcrux.Signature.Signature_Ed25519 hoist290 <: Libcrux.Signature.t_Signature
          in
          let res:Core.Result.t_Result Prims.unit Libcrux.Signature.t_Error =
            Libcrux.Signature.verify (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify
                      input
                    <:
                    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                <:
                t_Slice u8)
              hoist291
              (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify pk
                    <:
                    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                <:
                t_Slice u8)
          in
          match res with
          | Core.Result.Result_Ok res ->
            Core.Result.Result_Ok res <: Core.Result.t_Result Prims.unit u8
          | Core.Result.Result_Err _ ->
            Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_INVALID_SIGNATURE)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
          (Core.Result.t_Result Prims.unit u8)
      | SignatureScheme_EcdsaSecp256r1Sha256 , PublicVerificationKey_EcDsa pk ->
        let* hoist293:t_Array u8 (sz 64) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 64) sig
                <:
                Core.Result.t_Result (t_Array u8 (sz 64)) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist292:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Prims.unit u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist292)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
              (t_Array u8 (sz 64))
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
              (t_Array u8 (sz 64))
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let hoist294:Libcrux.Signature.t_EcDsaP256Signature =
            Libcrux.Signature.impl__EcDsaP256Signature__from_bytes hoist293
              (Libcrux.Signature.Algorithm_EcDsaP256
                (Libcrux.Signature.DigestAlgorithm_Sha256 <: Libcrux.Signature.t_DigestAlgorithm)
                <:
                Libcrux.Signature.t_Algorithm)
          in
          let hoist295:Libcrux.Signature.t_Signature =
            Libcrux.Signature.Signature_EcDsaP256 hoist294 <: Libcrux.Signature.t_Signature
          in
          let res:Core.Result.t_Result Prims.unit Libcrux.Signature.t_Error =
            Libcrux.Signature.verify (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify
                      input
                    <:
                    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                <:
                t_Slice u8)
              hoist295
              (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify pk
                    <:
                    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                <:
                t_Slice u8)
          in
          match res with
          | Core.Result.Result_Ok res ->
            Core.Result.Result_Ok res <: Core.Result.t_Result Prims.unit u8
          | Core.Result.Result_Err _ ->
            Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_INVALID_SIGNATURE)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
          (Core.Result.t_Result Prims.unit u8)
      | SignatureScheme_RsaPssRsaSha256 ,
      PublicVerificationKey_Rsa { f_modulus = n ; f_exponent = e } ->
        if
          ~.(valid_rsa_exponent (Bertie.Tls13utils.impl__Bytes__declassify e
                <:
                Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            <:
            bool)
          <:
          bool
        then
          Core.Ops.Control_flow.ControlFlow_Continue
          (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
            <:
            Core.Result.t_Result Prims.unit u8)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
            (Core.Result.t_Result Prims.unit u8)
        else
          let* key_size:Libcrux.Signature.Rsa_pss.t_RsaPssKeySize =
            match
              Core.Ops.Try_trait.f_branch (supported_rsa_key_size n
                  <:
                  Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist296:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Prims.unit u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist296)
              <:
              Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
                Libcrux.Signature.Rsa_pss.t_RsaPssKeySize
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
                Libcrux.Signature.Rsa_pss.t_RsaPssKeySize
          in
          let* pk:Libcrux.Signature.Rsa_pss.t_RsaPssPublicKey =
            match
              Core.Ops.Try_trait.f_branch (Core.Result.impl__map_err (Libcrux.Signature.Rsa_pss.impl__RsaPssPublicKey__new
                        key_size
                        ((Bertie.Tls13utils.impl__Bytes__declassify n
                            <:
                            Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global).[ {
                              Core.Ops.Range.f_start = sz 1
                            }
                            <:
                            Core.Ops.Range.t_RangeFrom usize ]
                          <:
                          t_Slice u8)
                      <:
                      Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssPublicKey
                        Libcrux.Signature.t_Error)
                    (fun temp_0_ ->
                        let _:Libcrux.Signature.t_Error = temp_0_ in
                        Bertie.Tls13utils.v_CRYPTO_ERROR)
                  <:
                  Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssPublicKey u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist297:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Prims.unit u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist297)
              <:
              Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
                Libcrux.Signature.Rsa_pss.t_RsaPssPublicKey
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
                Libcrux.Signature.Rsa_pss.t_RsaPssPublicKey
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let res:Core.Result.t_Result Prims.unit Libcrux.Signature.t_Error =
              Libcrux.Signature.Rsa_pss.impl__RsaPssPublicKey__verify pk
                (Libcrux.Signature.DigestAlgorithm_Sha256 <: Libcrux.Signature.t_DigestAlgorithm)
                (Core.Convert.f_into (Bertie.Tls13utils.impl__Bytes__declassify sig
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  Libcrux.Signature.Rsa_pss.t_RsaPssSignature)
                (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify input
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  t_Slice u8)
                (sz 32)
            in
            match res with
            | Core.Result.Result_Ok res ->
              Core.Result.Result_Ok res <: Core.Result.t_Result Prims.unit u8
            | Core.Result.Result_Err _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
            (Core.Result.t_Result Prims.unit u8)
      | _ ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
          <:
          Core.Result.t_Result Prims.unit u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
          (Core.Result.t_Result Prims.unit u8))

type t_AeadKeyIV = {
  f_key:t_AeadKey;
  f_iv:Bertie.Tls13utils.t_Bytes
}

let impl__AeadKeyIV__new (key: t_AeadKey) (iv: Bertie.Tls13utils.t_Bytes) : t_AeadKeyIV =
  { f_key = key; f_iv = iv } <: t_AeadKeyIV
