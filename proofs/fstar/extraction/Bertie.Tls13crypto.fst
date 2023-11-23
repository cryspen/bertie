module Bertie.Tls13crypto
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_AeadAlgorithm =
  | AeadAlgorithm_Chacha20Poly1305 : t_AeadAlgorithm
  | AeadAlgorithm_Aes128Gcm : t_AeadAlgorithm
  | AeadAlgorithm_Aes256Gcm : t_AeadAlgorithm

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

let ae_iv_len (alg: t_AeadAlgorithm) : usize =
  match alg with
  | AeadAlgorithm_Chacha20Poly1305  -> sz 12
  | AeadAlgorithm_Aes128Gcm  -> sz 12
  | AeadAlgorithm_Aes256Gcm  -> sz 12

let ae_key_len (alg: t_AeadAlgorithm) : usize =
  match alg with
  | AeadAlgorithm_Chacha20Poly1305  -> sz 32
  | AeadAlgorithm_Aes128Gcm  -> sz 16
  | AeadAlgorithm_Aes256Gcm  -> sz 32

let kem_priv_len (alg: t_KemScheme) : usize =
  match alg with
  | KemScheme_X25519  -> sz 32
  | KemScheme_Secp256r1  -> sz 32
  | _ -> sz 64

let valid_rsa_exponent (e: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : bool =
  (Alloc.Vec.impl_1__len e <: usize) =. sz 3 && (e.[ sz 0 ] <: u8) =. 1uy &&
  (e.[ sz 1 ] <: u8) =. 0uy &&
  (e.[ sz 2 ] <: u8) =. 1uy

let to_libcrux_aead_alg (alg: t_AeadAlgorithm) : Core.Result.t_Result Libcrux.Aead.t_Algorithm u8 =
  match alg with
  | AeadAlgorithm_Chacha20Poly1305  ->
    Core.Result.Result_Ok (Libcrux.Aead.Algorithm_Chacha20Poly1305 <: Libcrux.Aead.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Aead.t_Algorithm u8
  | AeadAlgorithm_Aes128Gcm  ->
    Core.Result.Result_Ok (Libcrux.Aead.Algorithm_Aes128Gcm <: Libcrux.Aead.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Aead.t_Algorithm u8
  | AeadAlgorithm_Aes256Gcm  ->
    Core.Result.Result_Ok (Libcrux.Aead.Algorithm_Aes256Gcm <: Libcrux.Aead.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Aead.t_Algorithm u8

let to_libcrux_hash_alg (alg: t_HashAlgorithm) : Core.Result.t_Result Libcrux.Digest.t_Algorithm u8 =
  match alg with
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

let hash_len (alg: t_HashAlgorithm) : usize =
  match alg with
  | HashAlgorithm_SHA256  ->
    Libcrux.Digest.digest_size (Libcrux.Digest.Algorithm_Sha256 <: Libcrux.Digest.t_Algorithm)
  | HashAlgorithm_SHA384  ->
    Libcrux.Digest.digest_size (Libcrux.Digest.Algorithm_Sha384 <: Libcrux.Digest.t_Algorithm)
  | HashAlgorithm_SHA512  ->
    Libcrux.Digest.digest_size (Libcrux.Digest.Algorithm_Sha512 <: Libcrux.Digest.t_Algorithm)

let hmac_tag_len (alg: t_HashAlgorithm) : usize = hash_len alg

let to_libcrux_hkdf_alg (alg: t_HashAlgorithm) : Core.Result.t_Result Libcrux.Hkdf.t_Algorithm u8 =
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

let to_libcrux_hmac_alg (alg: t_HashAlgorithm) : Core.Result.t_Result Libcrux.Hmac.t_Algorithm u8 =
  match alg with
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

let to_libcrux_sig_alg (a: t_SignatureScheme)
    : Core.Result.t_Result Libcrux.Signature.t_Algorithm u8 =
  match a with
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

let to_libcrux_kem_alg (alg: t_KemScheme) : Core.Result.t_Result Libcrux.Kem.t_Algorithm u8 =
  match alg with
  | KemScheme_X25519  ->
    Core.Result.Result_Ok (Libcrux.Kem.Algorithm_X25519 <: Libcrux.Kem.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Kem.t_Algorithm u8
  | KemScheme_Secp256r1  ->
    Core.Result.Result_Ok (Libcrux.Kem.Algorithm_Secp256r1 <: Libcrux.Kem.t_Algorithm)
    <:
    Core.Result.t_Result Libcrux.Kem.t_Algorithm u8
  | _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

type t_Algorithms =
  | Algorithms :
      t_HashAlgorithm ->
      t_AeadAlgorithm ->
      t_SignatureScheme ->
      t_KemScheme ->
      bool ->
      bool
    -> t_Algorithms

let aead_alg (algs: t_Algorithms) : t_AeadAlgorithm = algs._1

let hash_alg (algs: t_Algorithms) : t_HashAlgorithm = algs._0

let kem_alg (algs: t_Algorithms) : t_KemScheme = algs._3

let psk_mode (algs: t_Algorithms) : bool = algs._4

let sig_alg (algs: t_Algorithms) : t_SignatureScheme = algs._2

let zero_rtt (algs: t_Algorithms) : bool = algs._5

unfold
let t_AeadIV = Bertie.Tls13utils.t_Bytes

unfold
let t_AeadKey = Bertie.Tls13utils.t_Bytes

unfold
let t_AeadKeyIV = (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)

unfold
let t_Digest = Bertie.Tls13utils.t_Bytes

unfold
let t_Entropy = Bertie.Tls13utils.t_Bytes

unfold
let t_HMAC = Bertie.Tls13utils.t_Bytes

unfold
let t_KemPk = Bertie.Tls13utils.t_Bytes

unfold
let t_KemSk = Bertie.Tls13utils.t_Bytes

unfold
let t_Key = Bertie.Tls13utils.t_Bytes

unfold
let t_MacKey = Bertie.Tls13utils.t_Bytes

unfold
let t_PSK = Bertie.Tls13utils.t_Bytes

type t_PublicVerificationKey =
  | PublicVerificationKey_EcDsa : Bertie.Tls13utils.t_Bytes -> t_PublicVerificationKey
  | PublicVerificationKey_Rsa : (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
    -> t_PublicVerificationKey

unfold
let t_Random = Bertie.Tls13utils.t_Bytes

unfold
let t_RsaVerificationKey = (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)

unfold
let t_SignatureKey = Bertie.Tls13utils.t_Bytes

unfold
let t_VerificationKey = Bertie.Tls13utils.t_Bytes

let kem_keygen (alg: t_KemScheme) (ent: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist2:Libcrux.Kem.t_Algorithm =
        match
          Core.Ops.Try_trait.f_branch (to_libcrux_kem_alg alg
              <:
              Core.Result.t_Result Libcrux.Kem.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist1:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist1)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Libcrux.Kem.t_Algorithm
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Libcrux.Kem.t_Algorithm
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let _, out:(Rand.Rngs.Thread.t_ThreadRng &
          Core.Result.t_Result (Libcrux.Kem.t_PrivateKey & Libcrux.Kem.t_PublicKey)
            Libcrux.Kem.t_Error) =
          Libcrux.Kem.key_gen hoist2 (Rand.Rngs.Thread.thread_rng <: Rand.Rngs.Thread.t_ThreadRng)
        in
        let res:Core.Result.t_Result (Libcrux.Kem.t_PrivateKey & Libcrux.Kem.t_PublicKey)
          Libcrux.Kem.t_Error =
          out
        in
        match res with
        | Core.Result.Result_Ok (sk, pk) ->
          Core.Result.Result_Ok
          (Core.Convert.f_from (Libcrux.Kem.impl__PrivateKey__encode sk
                <:
                Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global),
            Core.Convert.f_from (Libcrux.Kem.impl__PublicKey__encode pk
                <:
                Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            <:
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8
        | Core.Result.Result_Err _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8))

let hash (alg: t_HashAlgorithm) (data: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist4:Libcrux.Digest.t_Algorithm =
        match
          Core.Ops.Try_trait.f_branch (to_libcrux_hash_alg alg
              <:
              Core.Result.t_Result Libcrux.Digest.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist3:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist3)
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
      (let hoist5:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
          Libcrux.Digest.hash hoist4
            (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify data
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              t_Slice u8)
        in
        let hoist6:Bertie.Tls13utils.t_Bytes = Core.Convert.f_into hoist5 in
        Core.Result.Result_Ok hoist6 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let hkdf_expand (alg: t_HashAlgorithm) (prk info: Bertie.Tls13utils.t_Bytes) (len: usize)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist8:Libcrux.Hkdf.t_Algorithm =
        match
          Core.Ops.Try_trait.f_branch (to_libcrux_hkdf_alg alg
              <:
              Core.Result.t_Result Libcrux.Hkdf.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist7:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist7)
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
      (let hoist9:Core.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          Libcrux.Hkdf.t_Error =
          Libcrux.Hkdf.expand hoist8
            (Bertie.Tls13utils.impl__Bytes__declassify prk
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            (Bertie.Tls13utils.impl__Bytes__declassify info
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            len
        in
        match hoist9 with
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
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist11:Libcrux.Hkdf.t_Algorithm =
        match
          Core.Ops.Try_trait.f_branch (to_libcrux_hkdf_alg alg
              <:
              Core.Result.t_Result Libcrux.Hkdf.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist10:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist10)
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
      (let hoist12:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
          Libcrux.Hkdf.extract hoist11
            (Bertie.Tls13utils.impl__Bytes__declassify salt
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            (Bertie.Tls13utils.impl__Bytes__declassify ikm
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        in
        let hoist13:Bertie.Tls13utils.t_Bytes = Core.Convert.f_into hoist12 in
        Core.Result.Result_Ok hoist13 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let hmac_tag (alg: t_HashAlgorithm) (mk input: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist15:Libcrux.Hmac.t_Algorithm =
        match
          Core.Ops.Try_trait.f_branch (to_libcrux_hmac_alg alg
              <:
              Core.Result.t_Result Libcrux.Hmac.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist14:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist14)
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
      (let hoist16:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
          Libcrux.Hmac.hmac hoist15
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
        let hoist17:Bertie.Tls13utils.t_Bytes = Core.Convert.f_into hoist16 in
        Core.Result.Result_Ok hoist17 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let kem_decap (alg: t_KemScheme) (ct sk: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* alg:Libcrux.Kem.t_Algorithm =
        match
          Core.Ops.Try_trait.f_branch (to_libcrux_kem_alg alg
              <:
              Core.Result.t_Result Libcrux.Kem.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist18:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist18)
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
          Core.Result.impl__unwrap (Libcrux.Kem.impl__PrivateKey__decode alg
                (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify sk
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Libcrux.Kem.t_PrivateKey Libcrux.Kem.t_Error)
        in
        let ct:Libcrux.Kem.t_Ct =
          Core.Result.impl__unwrap (Libcrux.Kem.impl__Ct__decode alg
                (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify ct
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Libcrux.Kem.t_Ct Libcrux.Kem.t_Error)
        in
        let res:Core.Result.t_Result Libcrux.Kem.t_Ss Libcrux.Kem.t_Error =
          Libcrux.Kem.decapsulate ct sk
        in
        match res with
        | Core.Result.Result_Ok x ->
          Core.Result.Result_Ok
          (Core.Convert.f_into (Libcrux.Kem.impl__Ss__encode x
                <:
                Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | Core.Result.Result_Err _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let kem_encap (alg: t_KemScheme) (pk ent: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist20:Libcrux.Kem.t_Algorithm =
        match
          Core.Ops.Try_trait.f_branch (to_libcrux_kem_alg alg
              <:
              Core.Result.t_Result Libcrux.Kem.t_Algorithm u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist19:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist19)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Libcrux.Kem.t_Algorithm
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Libcrux.Kem.t_Algorithm
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist21:Core.Result.t_Result Libcrux.Kem.t_PublicKey Libcrux.Kem.t_Error =
          Libcrux.Kem.impl__PublicKey__decode hoist20
            (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify pk
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              t_Slice u8)
        in
        let pk:Libcrux.Kem.t_PublicKey = Core.Result.impl__unwrap hoist21 in
        let _, out:(Rand.Rngs.Thread.t_ThreadRng &
          Core.Result.t_Result (Libcrux.Kem.t_Ss & Libcrux.Kem.t_Ct) Libcrux.Kem.t_Error) =
          Libcrux.Kem.encapsulate pk (Rand.Rngs.Thread.thread_rng <: Rand.Rngs.Thread.t_ThreadRng)
        in
        let res:Core.Result.t_Result (Libcrux.Kem.t_Ss & Libcrux.Kem.t_Ct) Libcrux.Kem.t_Error =
          out
        in
        match res with
        | Core.Result.Result_Ok (gxy, gy) ->
          Core.Result.Result_Ok
          (Core.Convert.f_from (Libcrux.Kem.impl__Ss__encode gxy
                <:
                Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global),
            Core.Convert.f_from (Libcrux.Kem.impl__Ct__encode gy
                <:
                Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            <:
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8
        | Core.Result.Result_Err _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8))

let ae_key_wrap (alg: t_AeadAlgorithm) (k: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Libcrux.Aead.t_Key u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (match alg with
      | AeadAlgorithm_Chacha20Poly1305  ->
        let* hoist23:t_Array u8 (sz 32) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 32) k
                <:
                Core.Result.t_Result (t_Array u8 (sz 32)) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist22:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Libcrux.Aead.t_Key u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist22)
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
        (let hoist24:Libcrux.Aead.t_Chacha20Key =
            Libcrux.Aead.Chacha20Key hoist23 <: Libcrux.Aead.t_Chacha20Key
          in
          let hoist25:Libcrux.Aead.t_Key =
            Libcrux.Aead.Key_Chacha20Poly1305 hoist24 <: Libcrux.Aead.t_Key
          in
          Core.Result.Result_Ok hoist25 <: Core.Result.t_Result Libcrux.Aead.t_Key u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Libcrux.Aead.t_Key u8)
          (Core.Result.t_Result Libcrux.Aead.t_Key u8)
      | AeadAlgorithm_Aes128Gcm  ->
        let* hoist27:t_Array u8 (sz 16) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 16) k
                <:
                Core.Result.t_Result (t_Array u8 (sz 16)) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist26:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Libcrux.Aead.t_Key u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist26)
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
        (let hoist28:Libcrux.Aead.t_Aes128Key =
            Libcrux.Aead.Aes128Key hoist27 <: Libcrux.Aead.t_Aes128Key
          in
          let hoist29:Libcrux.Aead.t_Key = Libcrux.Aead.Key_Aes128 hoist28 <: Libcrux.Aead.t_Key in
          Core.Result.Result_Ok hoist29 <: Core.Result.t_Result Libcrux.Aead.t_Key u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Libcrux.Aead.t_Key u8)
          (Core.Result.t_Result Libcrux.Aead.t_Key u8)
      | AeadAlgorithm_Aes256Gcm  ->
        let* hoist31:t_Array u8 (sz 32) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 32) k
                <:
                Core.Result.t_Result (t_Array u8 (sz 32)) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist30:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Libcrux.Aead.t_Key u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist30)
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
        (let hoist32:Libcrux.Aead.t_Aes256Key =
            Libcrux.Aead.Aes256Key hoist31 <: Libcrux.Aead.t_Aes256Key
          in
          let hoist33:Libcrux.Aead.t_Key = Libcrux.Aead.Key_Aes256 hoist32 <: Libcrux.Aead.t_Key in
          Core.Result.Result_Ok hoist33 <: Core.Result.t_Result Libcrux.Aead.t_Key u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Libcrux.Aead.t_Key u8)
          (Core.Result.t_Result Libcrux.Aead.t_Key u8))

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
          let* hoist44:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

                <:
                Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist44)
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

let verify
      (alg: t_SignatureScheme)
      (pk: t_PublicVerificationKey)
      (input sig: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (match
        alg, pk <: (t_SignatureScheme & t_PublicVerificationKey)
      with
      | SignatureScheme_ED25519 , PublicVerificationKey_EcDsa pk ->
        let* hoist46:t_Array u8 (sz 64) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 64) sig
                <:
                Core.Result.t_Result (t_Array u8 (sz 64)) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist45:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Prims.unit u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist45)
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
        (let hoist47:Libcrux.Signature.t_Ed25519Signature =
            Libcrux.Signature.impl__Ed25519Signature__from_bytes hoist46
          in
          let hoist48:Libcrux.Signature.t_Signature =
            Libcrux.Signature.Signature_Ed25519 hoist47 <: Libcrux.Signature.t_Signature
          in
          let res:Core.Result.t_Result Prims.unit Libcrux.Signature.t_Error =
            Libcrux.Signature.verify (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify
                      input
                    <:
                    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                <:
                t_Slice u8)
              hoist48
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
        let* hoist50:t_Array u8 (sz 64) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 64) sig
                <:
                Core.Result.t_Result (t_Array u8 (sz 64)) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist49:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Prims.unit u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist49)
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
        (let hoist51:Libcrux.Signature.t_EcDsaP256Signature =
            Libcrux.Signature.impl__EcDsaP256Signature__from_bytes hoist50
              (Libcrux.Signature.Algorithm_EcDsaP256
                (Libcrux.Signature.DigestAlgorithm_Sha256 <: Libcrux.Signature.t_DigestAlgorithm)
                <:
                Libcrux.Signature.t_Algorithm)
          in
          let hoist52:Libcrux.Signature.t_Signature =
            Libcrux.Signature.Signature_EcDsaP256 hoist51 <: Libcrux.Signature.t_Signature
          in
          let res:Core.Result.t_Result Prims.unit Libcrux.Signature.t_Error =
            Libcrux.Signature.verify (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify
                      input
                    <:
                    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                <:
                t_Slice u8)
              hoist52
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
      | SignatureScheme_RsaPssRsaSha256 , PublicVerificationKey_Rsa (n, e) ->
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
              let* hoist53:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Prims.unit u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist53)
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
              let* hoist54:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Prims.unit u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist54)
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

let aead_decrypt (alg: t_AeadAlgorithm) (k iv cip aad: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let _:Prims.unit =
        Std.Io.Stdio.v__print (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize (let list =
                      ["dec key "; "\n nonce: "; "\n"]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
                    Rust_primitives.Hax.array_of_list list)
                <:
                t_Slice string)
              (Rust_primitives.unsize (let list =
                      [
                        Core.Fmt.Rt.impl_1__new_display (Bertie.Tls13utils.impl__Bytes__to_hex k
                            <:
                            Alloc.String.t_String)
                        <:
                        Core.Fmt.Rt.t_Argument;
                        Core.Fmt.Rt.impl_1__new_display (Bertie.Tls13utils.impl__Bytes__to_hex iv
                            <:
                            Alloc.String.t_String)
                        <:
                        Core.Fmt.Rt.t_Argument
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                    Rust_primitives.Hax.array_of_list list)
                <:
                t_Slice Core.Fmt.Rt.t_Argument)
            <:
            Core.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      let tag:Bertie.Tls13utils.t_Bytes =
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
          let* hoist56:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist56)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (t_Array u8 (sz 16))
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (t_Array u8 (sz 16))
      in
      let* hoist61:Libcrux.Aead.t_Key =
        match
          Core.Ops.Try_trait.f_branch (ae_key_wrap alg k
              <:
              Core.Result.t_Result Libcrux.Aead.t_Key u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist57:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist57)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Aead.t_Key
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Aead.t_Key
      in
      let* hoist59:t_Array u8 (sz 12) =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 12) iv
              <:
              Core.Result.t_Result (t_Array u8 (sz 12)) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist58:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist58)
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
      (let hoist60:Libcrux.Aead.t_Iv = Libcrux.Aead.Iv hoist59 <: Libcrux.Aead.t_Iv in
        let plain:Core.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          Libcrux.Aead.t_Error =
          Libcrux.Aead.decrypt_detached hoist61
            (Bertie.Tls13utils.impl__Bytes__declassify cip
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            hoist60
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

let aead_encrypt (alg: t_AeadAlgorithm) (k iv plain aad: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let _:Prims.unit =
        Std.Io.Stdio.v__print (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize (let list =
                      ["enc key "; "\n nonce: "; "\n"]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
                    Rust_primitives.Hax.array_of_list list)
                <:
                t_Slice string)
              (Rust_primitives.unsize (let list =
                      [
                        Core.Fmt.Rt.impl_1__new_display (Bertie.Tls13utils.impl__Bytes__to_hex k
                            <:
                            Alloc.String.t_String)
                        <:
                        Core.Fmt.Rt.t_Argument;
                        Core.Fmt.Rt.impl_1__new_display (Bertie.Tls13utils.impl__Bytes__to_hex iv
                            <:
                            Alloc.String.t_String)
                        <:
                        Core.Fmt.Rt.t_Argument
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                    Rust_primitives.Hax.array_of_list list)
                <:
                t_Slice Core.Fmt.Rt.t_Argument)
            <:
            Core.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      let* hoist66:Libcrux.Aead.t_Key =
        match
          Core.Ops.Try_trait.f_branch (ae_key_wrap alg k
              <:
              Core.Result.t_Result Libcrux.Aead.t_Key u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist62:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist62)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Aead.t_Key
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Libcrux.Aead.t_Key
      in
      let* hoist64:t_Array u8 (sz 12) =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__Bytes__declassify_array (sz 12) iv
              <:
              Core.Result.t_Result (t_Array u8 (sz 12)) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist63:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist63)
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
      (let hoist65:Libcrux.Aead.t_Iv = Libcrux.Aead.Iv hoist64 <: Libcrux.Aead.t_Iv in
        let res:Core.Result.t_Result (Libcrux.Aead.t_Tag & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          Libcrux.Aead.t_Error =
          Libcrux.Aead.encrypt_detached hoist66
            (Bertie.Tls13utils.impl__Bytes__declassify plain
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            hoist65
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

let sign (alg: t_SignatureScheme) (sk cert input ent: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* sig:Core.Result.t_Result
        Libcrux.Signature.t_Signature Libcrux.Signature.t_Error =
        match alg with
        | SignatureScheme_EcdsaSecp256r1Sha256  ->
          let* hoist114:Libcrux.Signature.t_Algorithm =
            match
              Core.Ops.Try_trait.f_branch (to_libcrux_sig_alg alg
                  <:
                  Core.Result.t_Result Libcrux.Signature.t_Algorithm u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist113:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist113)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Libcrux.Signature.t_Algorithm
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Libcrux.Signature.t_Algorithm
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let _, out:(Rand.Rngs.Thread.t_ThreadRng &
              Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error) =
              Libcrux.Signature.sign hoist114
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
                (Rand.Rngs.Thread.thread_rng <: Rand.Rngs.Thread.t_ThreadRng)
            in
            out)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error)
        | SignatureScheme_ED25519  ->
          let* hoist116:Libcrux.Signature.t_Algorithm =
            match
              Core.Ops.Try_trait.f_branch (to_libcrux_sig_alg alg
                  <:
                  Core.Result.t_Result Libcrux.Signature.t_Algorithm u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist115:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist115)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Libcrux.Signature.t_Algorithm
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Libcrux.Signature.t_Algorithm
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let _, out:(Rand.Rngs.Thread.t_ThreadRng &
              Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error) =
              Libcrux.Signature.sign hoist116
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
                (Rand.Rngs.Thread.thread_rng <: Rand.Rngs.Thread.t_ThreadRng)
            in
            out)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error)
        | SignatureScheme_RsaPssRsaSha256  ->
          let salt:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
          let salt:(Rand.Rngs.Thread.t_ThreadRng & t_Array u8 (sz 32)) =
            Rand_core.f_fill_bytes (Rand.Rngs.Thread.thread_rng <: Rand.Rngs.Thread.t_ThreadRng)
              salt
          in
          let* cert_scheme, cert_slice:(t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey) =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13cert.verification_key_from_cert cert
                  <:
                  Core.Result.t_Result (t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey) u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist117:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist117)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                (t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                (t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey)
          in
          let* _:Prims.unit =
            if
              ~.(match cert_scheme with
                | SignatureScheme_RsaPssRsaSha256  -> true
                | _ -> false)
            then
              let* hoist118:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist118)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Prims.unit
            else
              Core.Ops.Control_flow.ControlFlow_Continue ()
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Prims.unit
          in
          let* pk_modulus, pk_exponent:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13cert.rsa_public_key cert cert_slice
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist119:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist119)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
          in
          let* _:Prims.unit =
            if
              ~.(valid_rsa_exponent (Bertie.Tls13utils.impl__Bytes__declassify pk_exponent
                    <:
                    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                <:
                bool)
            then
              let* hoist120:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist120)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Prims.unit
            else
              Core.Ops.Control_flow.ControlFlow_Continue ()
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) Prims.unit
          in
          let* key_size:Libcrux.Signature.Rsa_pss.t_RsaPssKeySize =
            match
              Core.Ops.Try_trait.f_branch (supported_rsa_key_size pk_modulus
                  <:
                  Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssKeySize u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist121:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist121)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                Libcrux.Signature.Rsa_pss.t_RsaPssKeySize
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                Libcrux.Signature.Rsa_pss.t_RsaPssKeySize
          in
          let* pk:Libcrux.Signature.Rsa_pss.t_RsaPssPublicKey =
            match
              Core.Ops.Try_trait.f_branch (Core.Result.impl__map_err (Libcrux.Signature.Rsa_pss.impl__RsaPssPublicKey__new
                        key_size
                        ((Bertie.Tls13utils.impl__Bytes__declassify pk_modulus
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
              let* hoist122:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist122)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                Libcrux.Signature.Rsa_pss.t_RsaPssPublicKey
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
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
              let* hoist123:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist123)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                Libcrux.Signature.Rsa_pss.t_RsaPssPrivateKey
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                Libcrux.Signature.Rsa_pss.t_RsaPssPrivateKey
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (Core.Result.impl__map (Libcrux.Signature.Rsa_pss.impl_5__sign sk
                  (Libcrux.Signature.DigestAlgorithm_Sha256 <: Libcrux.Signature.t_DigestAlgorithm)
                  (Rust_primitives.unsize salt <: t_Slice u8)
                  (Core.Ops.Deref.f_deref (Bertie.Tls13utils.impl__Bytes__declassify input
                        <:
                        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                    <:
                    t_Slice u8)
                <:
                Core.Result.t_Result Libcrux.Signature.Rsa_pss.t_RsaPssSignature
                  Libcrux.Signature.t_Error)
              Libcrux.Signature.Signature.v_RsaPss)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Result.t_Result Libcrux.Signature.t_Signature Libcrux.Signature.t_Error)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (match sig with
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
          (Bertie.Tls13utils.impl__Bytes__concat (Core.Convert.f_from r <: Bertie.Tls13utils.t_Bytes
              )
              (Core.Convert.f_from s <: Bertie.Tls13utils.t_Bytes))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | Core.Result.Result_Ok (Libcrux.Signature.Signature_RsaPss sig) ->
          Core.Result.Result_Ok
          (Core.Convert.f_into (Libcrux.Signature.Rsa_pss.impl__RsaPssSignature__as_bytes sig
                <:
                t_Slice u8))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | Core.Result.Result_Err _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let zero_key (alg: t_HashAlgorithm) : Bertie.Tls13utils.t_Bytes =
  Bertie.Tls13utils.impl__Bytes__zeroes (hash_len alg <: usize)

let hmac_verify (alg: t_HashAlgorithm) (mk input tag: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist142:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (hmac_tag alg mk input
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist141:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist141)
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
      (let hoist143:bool = Bertie.Tls13utils.eq hoist142 tag in
        if hoist143
        then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
        else Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_CRYPTO_ERROR)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))
