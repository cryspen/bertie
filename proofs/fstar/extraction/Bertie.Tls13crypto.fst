module Bertie.Tls13crypto
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13utils in
  let open Rand_core in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Fmt.t_Debug t_RsaVerificationKey

let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Fmt.t_Debug t_PublicVerificationKey

let impl_5 = impl_5'

let t_HashAlgorithm_cast_to_repr (x: t_HashAlgorithm) =
  match x <: t_HashAlgorithm with
  | HashAlgorithm_SHA256  -> mk_isize 0
  | HashAlgorithm_SHA384  -> mk_isize 1
  | HashAlgorithm_SHA512  -> mk_isize 2

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': Core_models.Marker.t_Copy t_HashAlgorithm

let impl_8 = impl_8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_10': Core_models.Marker.t_StructuralPartialEq t_HashAlgorithm

let impl_10 = impl_10'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_11': Core_models.Cmp.t_PartialEq t_HashAlgorithm t_HashAlgorithm

let impl_11 = impl_11'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core_models.Cmp.t_Eq t_HashAlgorithm

let impl_9 = impl_9'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_12': Core_models.Fmt.t_Debug t_HashAlgorithm

let impl_12 = impl_12'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_13': Core_models.Hash.t_Hash t_HashAlgorithm

let impl_13 = impl_13'

let impl_HashAlgorithm__hash_len (self: t_HashAlgorithm) =
  match self <: t_HashAlgorithm with
  | HashAlgorithm_SHA256  -> mk_usize 32
  | HashAlgorithm_SHA384  -> mk_usize 48
  | HashAlgorithm_SHA512  -> mk_usize 64

let impl_HashAlgorithm__hmac_tag_len (self: t_HashAlgorithm) = impl_HashAlgorithm__hash_len self

let zero_key (alg: t_HashAlgorithm) =
  Bertie.Tls13utils.impl_Bytes__zeroes (impl_HashAlgorithm__hash_len alg <: usize)

let impl_AeadKeyIV__new (key: t_AeadKey) (iv: Bertie.Tls13utils.t_Bytes) =
  { f_key = key; f_iv = iv } <: t_AeadKeyIV

let impl_AeadKey__new (bytes: Bertie.Tls13utils.t_Bytes) (e_alg: t_AeadAlgorithm) =
  { f_bytes = bytes; f_e_alg = e_alg } <: t_AeadKey

let t_AeadAlgorithm_cast_to_repr (x: t_AeadAlgorithm) =
  match x <: t_AeadAlgorithm with
  | AeadAlgorithm_Chacha20Poly1305  -> mk_isize 0
  | AeadAlgorithm_Aes128Gcm  -> mk_isize 1
  | AeadAlgorithm_Aes256Gcm  -> mk_isize 2

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_16': Core_models.Marker.t_Copy t_AeadAlgorithm

let impl_16 = impl_16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_17': Core_models.Marker.t_StructuralPartialEq t_AeadAlgorithm

let impl_17 = impl_17'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_18': Core_models.Cmp.t_PartialEq t_AeadAlgorithm t_AeadAlgorithm

let impl_18 = impl_18'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_19': Core_models.Fmt.t_Debug t_AeadAlgorithm

let impl_19 = impl_19'

let impl_AeadAlgorithm__key_len (self: t_AeadAlgorithm) =
  match self <: t_AeadAlgorithm with
  | AeadAlgorithm_Chacha20Poly1305  -> mk_usize 32
  | AeadAlgorithm_Aes128Gcm  -> mk_usize 16
  | AeadAlgorithm_Aes256Gcm  -> mk_usize 32

let impl_AeadAlgorithm__iv_len (self: t_AeadAlgorithm) =
  match self <: t_AeadAlgorithm with
  | AeadAlgorithm_Chacha20Poly1305  -> mk_usize 12
  | AeadAlgorithm_Aes128Gcm  -> mk_usize 12
  | AeadAlgorithm_Aes256Gcm  -> mk_usize 12

let t_SignatureScheme_cast_to_repr (x: t_SignatureScheme) =
  match x <: t_SignatureScheme with
  | SignatureScheme_RsaPssRsaSha256  -> mk_isize 0
  | SignatureScheme_EcdsaSecp256r1Sha256  -> mk_isize 1
  | SignatureScheme_ED25519  -> mk_isize 2

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_21': Core_models.Marker.t_Copy t_SignatureScheme

let impl_21 = impl_21'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_22': Core_models.Marker.t_StructuralPartialEq t_SignatureScheme

let impl_22 = impl_22'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_23': Core_models.Cmp.t_PartialEq t_SignatureScheme t_SignatureScheme

let impl_23 = impl_23'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_24': Core_models.Fmt.t_Debug t_SignatureScheme

let impl_24 = impl_24'

let supported_rsa_key_size (n: Bertie.Tls13utils.t_Bytes) =
  match Bertie.Tls13utils.impl_Bytes__len n <: usize with
  | Rust_primitives.Integers.MkInt 257
  | Rust_primitives.Integers.MkInt 385
  | Rust_primitives.Integers.MkInt 513
  | Rust_primitives.Integers.MkInt 769
  | Rust_primitives.Integers.MkInt 1025 ->
    Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit u8
  | _ -> Bertie.Tls13utils.tlserr #Prims.unit Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let valid_rsa_exponent (e: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global e <: usize) =. mk_usize 3 &&
  (e.[ mk_usize 0 ] <: u8) =. mk_u8 1 &&
  (e.[ mk_usize 1 ] <: u8) =. mk_u8 0 &&
  (e.[ mk_usize 2 ] <: u8) =. mk_u8 1

let t_KemScheme_cast_to_repr (x: t_KemScheme) =
  match x <: t_KemScheme with
  | KemScheme_X25519  -> mk_isize 0
  | KemScheme_Secp256r1  -> mk_isize 1
  | KemScheme_X448  -> mk_isize 2
  | KemScheme_Secp384r1  -> mk_isize 3
  | KemScheme_Secp521r1  -> mk_isize 4
  | KemScheme_X25519MlKem768  -> mk_isize 5

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_26': Core_models.Marker.t_Copy t_KemScheme

let impl_26 = impl_26'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_27': Core_models.Marker.t_StructuralPartialEq t_KemScheme

let impl_27 = impl_27'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_28': Core_models.Cmp.t_PartialEq t_KemScheme t_KemScheme

let impl_28 = impl_28'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_29': Core_models.Cmp.t_Eq t_KemScheme

let impl_29 = impl_29'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_30': Core_models.Fmt.t_Debug t_KemScheme

let impl_30 = impl_30'

let raw_public_key_len (alg: t_KemScheme) =
  match alg <: t_KemScheme with
  | KemScheme_X25519  ->
    Core_models.Result.Result_Ok (mk_usize 32) <: Core_models.Result.t_Result usize u8
  | KemScheme_Secp256r1  ->
    Core_models.Result.Result_Ok (mk_usize 64) <: Core_models.Result.t_Result usize u8
  | KemScheme_X25519MlKem768  ->
    Core_models.Result.Result_Ok (mk_usize 1216) <: Core_models.Result.t_Result usize u8
  | _ -> Bertie.Tls13utils.tlserr #usize Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let private_key_len (alg: t_KemScheme) =
  match alg <: t_KemScheme with
  | KemScheme_X25519
  | KemScheme_Secp256r1  ->
    Core_models.Result.Result_Ok (mk_usize 32) <: Core_models.Result.t_Result usize u8
  | KemScheme_X25519MlKem768  ->
    Core_models.Result.Result_Ok (mk_usize 2432) <: Core_models.Result.t_Result usize u8
  | _ -> Bertie.Tls13utils.tlserr #usize Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let encoding_prefix (alg: t_KemScheme) =
  if
    alg =. (KemScheme_Secp256r1 <: t_KemScheme) || alg =. (KemScheme_Secp384r1 <: t_KemScheme) ||
    alg =. (KemScheme_Secp521r1 <: t_KemScheme)
  then
    Core_models.Convert.f_from #Bertie.Tls13utils.t_Bytes
      #(t_Array u8 (mk_usize 1))
      #FStar.Tactics.Typeclasses.solve
      (let list = [mk_u8 4] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
  else Bertie.Tls13utils.impl_Bytes__new ()

let into_raw (alg: t_KemScheme) (point: Bertie.Tls13utils.t_Bytes) =
  if
    (alg =. (KemScheme_Secp256r1 <: t_KemScheme) || alg =. (KemScheme_Secp384r1 <: t_KemScheme) ||
    alg =. (KemScheme_Secp521r1 <: t_KemScheme)) &&
    (Bertie.Tls13utils.impl_Bytes__len point <: usize) >=. mk_usize 1
  then
    Bertie.Tls13utils.impl_Bytes__slice_range point
      ({
          Core_models.Ops.Range.f_start = mk_usize 1;
          Core_models.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len point <: usize
        }
        <:
        Core_models.Ops.Range.t_Range usize)
  else point

let to_shared_secret (alg: t_KemScheme) (shared_secret: Bertie.Tls13utils.t_Bytes) =
  match alg <: t_KemScheme with
  | KemScheme_Secp256r1  ->
    if (Bertie.Tls13utils.impl_Bytes__len shared_secret <: usize) >=. mk_usize 32
    then
      Core_models.Result.Result_Ok
      (Bertie.Tls13utils.impl_Bytes__slice_range shared_secret
          ({ Core_models.Ops.Range.f_start = mk_usize 0; Core_models.Ops.Range.f_end = mk_usize 32 }
            <:
            Core_models.Ops.Range.t_Range usize))
      <:
      Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
    else Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_CRYPTO_ERROR
  | KemScheme_X25519
  | KemScheme_X25519MlKem768  ->
    Core_models.Result.Result_Ok shared_secret
    <:
    Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | _ ->
    Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

assume
val libcrux_hash': ha: t_HashAlgorithm -> data: t_Slice u8
  -> Prims.Pure (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Prims.l_True
      (ensures
        fun result ->
          let result:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = result in
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global result <: usize) =.
          (impl_HashAlgorithm__hash_len ha <: usize))

let libcrux_hash = libcrux_hash'

let hash (ha: t_HashAlgorithm) (data: Bertie.Tls13utils.t_Bytes) =
  Core_models.Result.Result_Ok
  (Core_models.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (libcrux_hash ha
          (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify data
                <:
                Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            <:
            t_Slice u8)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
  <:
  Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8

assume
val libcrux_hmac': ha: t_HashAlgorithm -> key: t_Slice u8 -> data: t_Slice u8
  -> Prims.Pure (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Prims.l_True
      (ensures
        fun result ->
          let result:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = result in
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global result <: usize) =.
          (impl_HashAlgorithm__hash_len ha <: usize))

let libcrux_hmac = libcrux_hmac'

let hmac_tag (alg: t_HashAlgorithm) (mk input: Bertie.Tls13utils.t_Bytes) =
  Core_models.Result.Result_Ok
  (Core_models.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (libcrux_hmac alg
          (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify mk
                <:
                Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            <:
            t_Slice u8)
          (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify input
                <:
                Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            <:
            t_Slice u8)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
  <:
  Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let hmac_verify (alg: t_HashAlgorithm) (mk input tag: Bertie.Tls13utils.t_Bytes) =
  match hmac_tag alg mk input <: Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
  | Core_models.Result.Result_Ok hoist181 ->
    if Bertie.Tls13utils.eq hoist181 tag
    then
      Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit u8
    else Bertie.Tls13utils.tlserr #Prims.unit Bertie.Tls13utils.v_CRYPTO_ERROR
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit u8

assume
val libcrux_hkdf_extract': ha: t_HashAlgorithm -> salt: t_Slice u8 -> ikm: t_Slice u8
  -> Prims.Pure (Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
            result
          in
          match result <: Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) with
          | Core_models.Option.Option_Some prk ->
            (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global prk <: usize) =.
            (impl_HashAlgorithm__hash_len ha <: usize)
          | Core_models.Option.Option_None  -> true)

let libcrux_hkdf_extract = libcrux_hkdf_extract'

let hkdf_extract (alg: t_HashAlgorithm) (ikm salt: Bertie.Tls13utils.t_Bytes) =
  match
    libcrux_hkdf_extract alg
      (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify salt
            <:
            Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        <:
        t_Slice u8)
      (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify ikm
            <:
            Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        <:
        t_Slice u8)
    <:
    Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  with
  | Core_models.Option.Option_Some prk ->
    Core_models.Result.Result_Ok
    (Core_models.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        #Bertie.Tls13utils.t_Bytes
        #FStar.Tactics.Typeclasses.solve
        prk)
    <:
    Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Core_models.Option.Option_None  ->
    Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_CRYPTO_ERROR

assume
val libcrux_hkdf_expand': ha: t_HashAlgorithm -> prk: t_Slice u8 -> info: t_Slice u8 -> len: usize
  -> Prims.Pure (Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
            result
          in
          match result <: Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) with
          | Core_models.Option.Option_Some okm ->
            (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global okm <: usize) =. len
          | Core_models.Option.Option_None  -> true)

let libcrux_hkdf_expand = libcrux_hkdf_expand'

let hkdf_expand (alg: t_HashAlgorithm) (prk info: Bertie.Tls13utils.t_Bytes) (len: usize) =
  match
    libcrux_hkdf_expand alg
      (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify prk
            <:
            Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        <:
        t_Slice u8)
      (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify info
            <:
            Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        <:
        t_Slice u8)
      len
    <:
    Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  with
  | Core_models.Option.Option_Some okm ->
    Core_models.Result.Result_Ok
    (Core_models.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        #Bertie.Tls13utils.t_Bytes
        #FStar.Tactics.Typeclasses.solve
        okm)
    <:
    Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Core_models.Option.Option_None  ->
    Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_CRYPTO_ERROR

assume
val libcrux_chacha20poly1305_encrypt':
    key: t_Array u8 (mk_usize 32) ->
    nonce: t_Array u8 (mk_usize 12) ->
    aad: t_Slice u8 ->
    ptxt: t_Slice u8
  -> Prims.Pure (Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      Prims.l_True
      (fun _ -> Prims.l_True)

let libcrux_chacha20poly1305_encrypt = libcrux_chacha20poly1305_encrypt'

let aead_encrypt (k: t_AeadKey) (iv plain aad: Bertie.Tls13utils.t_Bytes) =
  match
    Core_models.Result.impl__map_err #(t_Array u8 (mk_usize 32))
      #u8
      #u8
      #(u8 -> u8)
      (Bertie.Tls13utils.impl_Bytes__declassify_array (mk_usize 32) k.f_bytes
        <:
        Core_models.Result.t_Result (t_Array u8 (mk_usize 32)) u8)
      (fun temp_0_ ->
          let _:u8 = temp_0_ in
          Bertie.Tls13utils.v_INCORRECT_ARRAY_LENGTH)
    <:
    Core_models.Result.t_Result (t_Array u8 (mk_usize 32)) u8
  with
  | Core_models.Result.Result_Ok key ->
    (match
        Bertie.Tls13utils.impl_Bytes__declassify_array (mk_usize 12) iv
        <:
        Core_models.Result.t_Result (t_Array u8 (mk_usize 12)) u8
      with
      | Core_models.Result.Result_Ok iv ->
        (match
            libcrux_chacha20poly1305_encrypt key
              iv
              (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify aad
                    <:
                    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                <:
                t_Slice u8)
              (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify plain
                    <:
                    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                <:
                t_Slice u8)
            <:
            Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          with
          | Core_models.Option.Option_Some ctxt ->
            Core_models.Result.Result_Ok
            (Core_models.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                #Bertie.Tls13utils.t_Bytes
                #FStar.Tactics.Typeclasses.solve
                ctxt)
            <:
            Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          | Core_models.Option.Option_None  ->
            Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_CRYPTO_ERROR)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8

assume
val libcrux_chacha20poly1305_decrypt':
    key: t_Array u8 (mk_usize 32) ->
    nonce: t_Array u8 (mk_usize 12) ->
    aad: t_Slice u8 ->
    ctxt: t_Slice u8 ->
    tag: t_Array u8 (mk_usize 16)
  -> Prims.Pure (Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      Prims.l_True
      (fun _ -> Prims.l_True)

let libcrux_chacha20poly1305_decrypt = libcrux_chacha20poly1305_decrypt'

let aead_decrypt (k: t_AeadKey) (iv cip aad: Bertie.Tls13utils.t_Bytes) =
  if (Bertie.Tls13utils.impl_Bytes__len cip <: usize) <. mk_usize 16
  then Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_CRYPTO_ERROR
  else
    let tag:Bertie.Tls13utils.t_Bytes =
      Bertie.Tls13utils.impl_Bytes__slice cip
        ((Bertie.Tls13utils.impl_Bytes__len cip <: usize) -! mk_usize 16 <: usize)
        (mk_usize 16)
    in
    let ctxt:Bertie.Tls13utils.t_Bytes =
      Bertie.Tls13utils.impl_Bytes__slice cip
        (mk_usize 0)
        ((Bertie.Tls13utils.impl_Bytes__len cip <: usize) -! mk_usize 16 <: usize)
    in
    match
      Bertie.Tls13utils.impl_Bytes__declassify_array (mk_usize 16) tag
      <:
      Core_models.Result.t_Result (t_Array u8 (mk_usize 16)) u8
    with
    | Core_models.Result.Result_Ok (tag: t_Array u8 (mk_usize 16)) ->
      (match
          Core_models.Result.impl__map_err #(t_Array u8 (mk_usize 32))
            #u8
            #u8
            #(u8 -> u8)
            (Bertie.Tls13utils.impl_Bytes__declassify_array (mk_usize 32) k.f_bytes
              <:
              Core_models.Result.t_Result (t_Array u8 (mk_usize 32)) u8)
            (fun temp_0_ ->
                let _:u8 = temp_0_ in
                Bertie.Tls13utils.v_INCORRECT_ARRAY_LENGTH)
          <:
          Core_models.Result.t_Result (t_Array u8 (mk_usize 32)) u8
        with
        | Core_models.Result.Result_Ok key ->
          (match
              Bertie.Tls13utils.impl_Bytes__declassify_array (mk_usize 12) iv
              <:
              Core_models.Result.t_Result (t_Array u8 (mk_usize 12)) u8
            with
            | Core_models.Result.Result_Ok iv ->
              (match
                  libcrux_chacha20poly1305_decrypt key
                    iv
                    (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify aad
                          <:
                          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                      <:
                      t_Slice u8)
                    (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify ctxt
                          <:
                          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                      <:
                      t_Slice u8)
                    tag
                  <:
                  Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                with
                | Core_models.Option.Option_Some plain ->
                  Core_models.Result.Result_Ok
                  (Core_models.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                      #Bertie.Tls13utils.t_Bytes
                      #FStar.Tactics.Typeclasses.solve
                      plain)
                  <:
                  Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                | Core_models.Option.Option_None  ->
                  Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes
                    Bertie.Tls13utils.v_CRYPTO_ERROR)
            | Core_models.Result.Result_Err err ->
              Core_models.Result.Result_Err err
              <:
              Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        | Core_models.Result.Result_Err err ->
          Core_models.Result.Result_Err err
          <:
          Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
    | Core_models.Result.Result_Err err ->
      Core_models.Result.Result_Err err <: Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8

assume
val libcrux_ecdsa_p256_sign':
    #iimpl_447424039_: Type0 ->
    {| i0: Rand_core.t_CryptoRng iimpl_447424039_ |} ->
    sk: t_Array u8 (mk_usize 32) ->
    msg: t_Slice u8 ->
    rng: iimpl_447424039_
  -> Prims.Pure
      (iimpl_447424039_ & Core_models.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

let libcrux_ecdsa_p256_sign
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand_core.t_CryptoRng iimpl_447424039_)
     = libcrux_ecdsa_p256_sign' #iimpl_447424039_ #i0

assume
val libcrux_ed25519_sign': sk: t_Array u8 (mk_usize 32) -> msg: t_Slice u8
  -> Prims.Pure (Core_models.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

let libcrux_ed25519_sign = libcrux_ed25519_sign'

let sign
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand_core.t_CryptoRng iimpl_447424039_)
      (algorithm: t_SignatureScheme)
      (sk input: Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
     =
  match algorithm <: t_SignatureScheme with
  | SignatureScheme_EcdsaSecp256r1Sha256  ->
    (match
        Bertie.Tls13utils.impl_Bytes__declassify_array (mk_usize 32) sk
        <:
        Core_models.Result.t_Result (t_Array u8 (mk_usize 32)) u8
      with
      | Core_models.Result.Result_Ok sk ->
        let
        (tmp0: iimpl_447424039_),
        (out: Core_models.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) u8) =
          libcrux_ecdsa_p256_sign #iimpl_447424039_
            sk
            (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify input
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              t_Slice u8)
            rng
        in
        let rng:iimpl_447424039_ = tmp0 in
        (match out <: Core_models.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) u8 with
          | Core_models.Result.Result_Ok hoist188 ->
            rng,
            (Core_models.Result.Result_Ok
              (Core_models.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  #Bertie.Tls13utils.t_Bytes
                  #FStar.Tactics.Typeclasses.solve
                  hoist188)
              <:
              Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            <:
            (iimpl_447424039_ & Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          | Core_models.Result.Result_Err err ->
            rng,
            (Core_models.Result.Result_Err err
              <:
              Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            <:
            (iimpl_447424039_ & Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
      | Core_models.Result.Result_Err err ->
        rng,
        (Core_models.Result.Result_Err err
          <:
          Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        (iimpl_447424039_ & Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
  | SignatureScheme_ED25519  ->
    (match
        Bertie.Tls13utils.impl_Bytes__declassify_array (mk_usize 32) sk
        <:
        Core_models.Result.t_Result (t_Array u8 (mk_usize 32)) u8
      with
      | Core_models.Result.Result_Ok sk ->
        (match
            libcrux_ed25519_sign sk
              (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify input
                    <:
                    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                <:
                t_Slice u8)
            <:
            Core_models.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) u8
          with
          | Core_models.Result.Result_Ok hoist190 ->
            rng,
            (Core_models.Result.Result_Ok
              (Core_models.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  #Bertie.Tls13utils.t_Bytes
                  #FStar.Tactics.Typeclasses.solve
                  hoist190)
              <:
              Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            <:
            (iimpl_447424039_ & Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          | Core_models.Result.Result_Err err ->
            rng,
            (Core_models.Result.Result_Err err
              <:
              Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            <:
            (iimpl_447424039_ & Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
      | Core_models.Result.Result_Err err ->
        rng,
        (Core_models.Result.Result_Err err
          <:
          Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        (iimpl_447424039_ & Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
  | SignatureScheme_RsaPssRsaSha256  ->
    rng,
    Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
    <:
    (iimpl_447424039_ & Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)

assume
val libcrux_ed25519_verify':
    pk: t_Array u8 (mk_usize 32) ->
    msg: t_Slice u8 ->
    sig: t_Array u8 (mk_usize 64)
  -> Prims.Pure (Core_models.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

let libcrux_ed25519_verify = libcrux_ed25519_verify'

assume
val libcrux_ecdsa_p256_verify':
    pk: t_Array u8 (mk_usize 64) ->
    msg: t_Slice u8 ->
    sig: t_Array u8 (mk_usize 64)
  -> Prims.Pure (Core_models.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

let libcrux_ecdsa_p256_verify = libcrux_ecdsa_p256_verify'

assume
val libcrux_rsa_pss_sign':
    #iimpl_447424039_: Type0 ->
    {| i0: Rand_core.t_CryptoRng iimpl_447424039_ |} ->
    modulus: t_Slice u8 ->
    sk: t_Slice u8 ->
    msg: t_Slice u8 ->
    rng: iimpl_447424039_
  -> Prims.Pure
      (iimpl_447424039_ & Core_models.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

let libcrux_rsa_pss_sign
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand_core.t_CryptoRng iimpl_447424039_)
     = libcrux_rsa_pss_sign' #iimpl_447424039_ #i0

let sign_rsa
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand_core.t_CryptoRng iimpl_447424039_)
      (sk pk_modulus pk_exponent: Bertie.Tls13utils.t_Bytes)
      (cert_scheme: t_SignatureScheme)
      (input: Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
     =
  if
    ~.(match cert_scheme <: t_SignatureScheme with
      | SignatureScheme_RsaPssRsaSha256  -> true
      | _ -> false)
  then
    rng, Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_CRYPTO_ERROR
    <:
    (iimpl_447424039_ & Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  else
    if
      ~.(valid_rsa_exponent (Bertie.Tls13utils.impl_Bytes__declassify pk_exponent
            <:
            Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        <:
        bool)
    then
      rng,
      Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
      <:
      (iimpl_447424039_ & Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
    else
      match supported_rsa_key_size pk_modulus <: Core_models.Result.t_Result Prims.unit u8 with
      | Core_models.Result.Result_Ok _ ->
        let modulus:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
          Bertie.Tls13utils.impl_Bytes__declassify pk_modulus
        in
        let
        (tmp0: iimpl_447424039_),
        (out: Core_models.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) u8) =
          libcrux_rsa_pss_sign #iimpl_447424039_
            (modulus.[ { Core_models.Ops.Range.f_start = mk_usize 1 }
                <:
                Core_models.Ops.Range.t_RangeFrom usize ]
              <:
              t_Slice u8)
            (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify sk
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              t_Slice u8)
            (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify input
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              t_Slice u8)
            rng
        in
        let rng:iimpl_447424039_ = tmp0 in
        (match out <: Core_models.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) u8 with
          | Core_models.Result.Result_Ok signature ->
            let hax_temp_output:Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
              Core_models.Result.Result_Ok
              (Core_models.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  #Bertie.Tls13utils.t_Bytes
                  #FStar.Tactics.Typeclasses.solve
                  signature)
              <:
              Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
            in
            rng, hax_temp_output
            <:
            (iimpl_447424039_ & Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          | Core_models.Result.Result_Err err ->
            rng,
            (Core_models.Result.Result_Err err
              <:
              Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            <:
            (iimpl_447424039_ & Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
      | Core_models.Result.Result_Err err ->
        rng,
        (Core_models.Result.Result_Err err
          <:
          Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        (iimpl_447424039_ & Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8)

assume
val libcrux_rsa_pss_verify': modulus: t_Slice u8 -> msg: t_Slice u8 -> sig: t_Slice u8
  -> Prims.Pure (Core_models.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

let libcrux_rsa_pss_verify = libcrux_rsa_pss_verify'

let verify
      (alg: t_SignatureScheme)
      (pk: t_PublicVerificationKey)
      (input sig: Bertie.Tls13utils.t_Bytes)
     =
  match alg, pk <: (t_SignatureScheme & t_PublicVerificationKey) with
  | SignatureScheme_ED25519 , PublicVerificationKey_EcDsa pk ->
    (match
        Bertie.Tls13utils.impl_Bytes__declassify_array (mk_usize 32) pk
        <:
        Core_models.Result.t_Result (t_Array u8 (mk_usize 32)) u8
      with
      | Core_models.Result.Result_Ok pk ->
        (match
            Bertie.Tls13utils.impl_Bytes__declassify_array (mk_usize 64) sig
            <:
            Core_models.Result.t_Result (t_Array u8 (mk_usize 64)) u8
          with
          | Core_models.Result.Result_Ok sig ->
            libcrux_ed25519_verify pk
              (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify input
                    <:
                    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                <:
                t_Slice u8)
              sig
          | Core_models.Result.Result_Err err ->
            Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit u8)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit u8)
  | SignatureScheme_EcdsaSecp256r1Sha256 , PublicVerificationKey_EcDsa pk ->
    (match
        Bertie.Tls13utils.impl_Bytes__declassify_array (mk_usize 64) sig
        <:
        Core_models.Result.t_Result (t_Array u8 (mk_usize 64)) u8
      with
      | Core_models.Result.Result_Ok sig ->
        (match
            Bertie.Tls13utils.impl_Bytes__declassify_array (mk_usize 64) pk
            <:
            Core_models.Result.t_Result (t_Array u8 (mk_usize 64)) u8
          with
          | Core_models.Result.Result_Ok pk ->
            libcrux_ecdsa_p256_verify pk
              (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify input
                    <:
                    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                <:
                t_Slice u8)
              sig
          | Core_models.Result.Result_Err err ->
            Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit u8)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit u8)
  | SignatureScheme_RsaPssRsaSha256 , PublicVerificationKey_Rsa { f_modulus = n ; f_exponent = e } ->
    if
      ~.(valid_rsa_exponent (Bertie.Tls13utils.impl_Bytes__declassify e
            <:
            Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        <:
        bool)
    then Bertie.Tls13utils.tlserr #Prims.unit Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
    else
      (match supported_rsa_key_size n <: Core_models.Result.t_Result Prims.unit u8 with
        | Core_models.Result.Result_Ok _ ->
          let n_vec:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
            Bertie.Tls13utils.impl_Bytes__declassify n
          in
          libcrux_rsa_pss_verify (n_vec.[ { Core_models.Ops.Range.f_start = mk_usize 1 }
                <:
                Core_models.Ops.Range.t_RangeFrom usize ]
              <:
              t_Slice u8)
            (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify input
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              t_Slice u8)
            (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify sig
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              t_Slice u8)
        | Core_models.Result.Result_Err err ->
          Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit u8)
  | _ -> Bertie.Tls13utils.tlserr #Prims.unit Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

assume
val libcrux_kem_keygen':
    #iimpl_447424039_: Type0 ->
    {| i0: Rand_core.t_CryptoRng iimpl_447424039_ |} ->
    alg: t_KemScheme ->
    rng: iimpl_447424039_
  -> Prims.Pure
      (iimpl_447424039_ &
        Core_models.Option.t_Option
        (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      Prims.l_True
      (fun _ -> Prims.l_True)

let libcrux_kem_keygen
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand_core.t_CryptoRng iimpl_447424039_)
     = libcrux_kem_keygen' #iimpl_447424039_ #i0

let kem_keygen
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand_core.t_CryptoRng iimpl_447424039_)
      (alg: t_KemScheme)
      (rng: iimpl_447424039_)
     =
  match raw_public_key_len alg <: Core_models.Result.t_Result usize u8 with
  | Core_models.Result.Result_Ok _ ->
    let
    (tmp0: iimpl_447424039_),
    (out:
      Core_models.Option.t_Option
      (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)) =
      libcrux_kem_keygen #iimpl_447424039_ alg rng
    in
    let rng:iimpl_447424039_ = tmp0 in
    let hax_temp_output:Core_models.Result.t_Result
      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
      match
        out
        <:
        Core_models.Option.t_Option
        (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      with
      | Core_models.Option.Option_Some (sk, pk) ->
        Core_models.Result.Result_Ok
        (Core_models.Convert.f_from #Bertie.Tls13utils.t_Bytes
            #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            #FStar.Tactics.Typeclasses.solve
            sk,
          Bertie.Tls13utils.impl_Bytes__concat (encoding_prefix alg <: Bertie.Tls13utils.t_Bytes)
            (Core_models.Convert.f_from #Bertie.Tls13utils.t_Bytes
                #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                #FStar.Tactics.Typeclasses.solve
                pk
              <:
              Bertie.Tls13utils.t_Bytes)
          <:
          (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
        <:
        Core_models.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8
      | Core_models.Option.Option_None  ->
        Bertie.Tls13utils.tlserr #(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
          Bertie.Tls13utils.v_CRYPTO_ERROR
    in
    rng, hax_temp_output
    <:
    (iimpl_447424039_ &
      Core_models.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
  | Core_models.Result.Result_Err err ->
    rng,
    (Core_models.Result.Result_Err err
      <:
      Core_models.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
    <:
    (iimpl_447424039_ &
      Core_models.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)

assume
val libcrux_kem_encap':
    #iimpl_447424039_: Type0 ->
    {| i0: Rand_core.t_CryptoRng iimpl_447424039_ |} ->
    alg: t_KemScheme ->
    pk: t_Slice u8 ->
    rng: iimpl_447424039_
  -> Prims.Pure
      (iimpl_447424039_ &
        Core_models.Option.t_Option
        (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      (requires
        (match raw_public_key_len alg <: Core_models.Result.t_Result usize u8 with
          | Core_models.Result.Result_Ok len -> (Core_models.Slice.impl__len #u8 pk <: usize) =. len
          | Core_models.Result.Result_Err _ -> false))
      (fun _ -> Prims.l_True)

let libcrux_kem_encap
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand_core.t_CryptoRng iimpl_447424039_)
     = libcrux_kem_encap' #iimpl_447424039_ #i0

let kem_encap
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand_core.t_CryptoRng iimpl_447424039_)
      (alg: t_KemScheme)
      (pk: Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
     =
  let pk:Bertie.Tls13utils.t_Bytes =
    into_raw alg
      (Core_models.Clone.f_clone #Bertie.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve pk
        <:
        Bertie.Tls13utils.t_Bytes)
  in
  match raw_public_key_len alg <: Core_models.Result.t_Result usize u8 with
  | Core_models.Result.Result_Ok hoist193 ->
    if (Bertie.Tls13utils.impl_Bytes__len pk <: usize) <>. hoist193
    then
      rng,
      Bertie.Tls13utils.tlserr #(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
        Bertie.Tls13utils.v_CRYPTO_ERROR
      <:
      (iimpl_447424039_ &
        Core_models.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
    else
      let
      (tmp0: iimpl_447424039_),
      (out:
        Core_models.Option.t_Option
        (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)) =
        libcrux_kem_encap #iimpl_447424039_
          alg
          (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify pk
                <:
                Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            <:
            t_Slice u8)
          rng
      in
      let rng:iimpl_447424039_ = tmp0 in
      (match
          out
          <:
          Core_models.Option.t_Option
          (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        with
        | Core_models.Option.Option_Some (shared_secret, ct) ->
          let ct:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl_Bytes__concat (encoding_prefix alg <: Bertie.Tls13utils.t_Bytes)
              (Core_models.Convert.f_from #Bertie.Tls13utils.t_Bytes
                  #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  #FStar.Tactics.Typeclasses.solve
                  ct
                <:
                Bertie.Tls13utils.t_Bytes)
          in
          (match
              to_shared_secret alg
                (Core_models.Convert.f_from #Bertie.Tls13utils.t_Bytes
                    #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    shared_secret
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
            with
            | Core_models.Result.Result_Ok shared_secret ->
              let hax_temp_output:Core_models.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
                Core_models.Result.Result_Ok
                (shared_secret, ct <: (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
                <:
                Core_models.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
                  u8
              in
              rng, hax_temp_output
              <:
              (iimpl_447424039_ &
                Core_models.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
                  u8)
            | Core_models.Result.Result_Err err ->
              rng,
              (Core_models.Result.Result_Err err
                <:
                Core_models.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
                  u8)
              <:
              (iimpl_447424039_ &
                Core_models.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
                  u8))
        | Core_models.Option.Option_None  ->
          let hax_temp_output:Core_models.Result.t_Result
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
            Bertie.Tls13utils.tlserr #(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
              Bertie.Tls13utils.v_CRYPTO_ERROR
          in
          rng, hax_temp_output
          <:
          (iimpl_447424039_ &
            Core_models.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8))
  | Core_models.Result.Result_Err err ->
    rng,
    (Core_models.Result.Result_Err err
      <:
      Core_models.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
    <:
    (iimpl_447424039_ &
      Core_models.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)

assume
val libcrux_kem_decap': alg: t_KemScheme -> ct: t_Slice u8 -> sk: t_Slice u8
  -> Prims.Pure (Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      (requires
        (match private_key_len alg <: Core_models.Result.t_Result usize u8 with
          | Core_models.Result.Result_Ok len -> (Core_models.Slice.impl__len #u8 sk <: usize) =. len
          | Core_models.Result.Result_Err _ -> false))
      (fun _ -> Prims.l_True)

let libcrux_kem_decap = libcrux_kem_decap'

let kem_decap (alg: t_KemScheme) (ct sk: Bertie.Tls13utils.t_Bytes) =
  match private_key_len alg <: Core_models.Result.t_Result usize u8 with
  | Core_models.Result.Result_Ok hoist197 ->
    if (Bertie.Tls13utils.impl_Bytes__len sk <: usize) <>. hoist197
    then Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_CRYPTO_ERROR
    else
      let ct:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        Bertie.Tls13utils.impl_Bytes__declassify (into_raw alg
              (Core_models.Clone.f_clone #Bertie.Tls13utils.t_Bytes
                  #FStar.Tactics.Typeclasses.solve
                  ct
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Bertie.Tls13utils.t_Bytes)
      in
      (match
          libcrux_kem_decap alg
            (Alloc.Vec.impl_1__as_slice ct <: t_Slice u8)
            (Alloc.Vec.impl_1__as_slice (Bertie.Tls13utils.impl_Bytes__declassify sk
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              t_Slice u8)
          <:
          Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        with
        | Core_models.Option.Option_Some shared_secret ->
          to_shared_secret alg
            (Core_models.Convert.f_from #Bertie.Tls13utils.t_Bytes
                #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                #FStar.Tactics.Typeclasses.solve
                shared_secret
              <:
              Bertie.Tls13utils.t_Bytes)
        | Core_models.Option.Option_None  ->
          Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_CRYPTO_ERROR)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_32': Core_models.Marker.t_Copy t_Algorithms

let impl_32 = impl_32'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_33': Core_models.Marker.t_StructuralPartialEq t_Algorithms

let impl_33 = impl_33'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_34': Core_models.Cmp.t_PartialEq t_Algorithms t_Algorithms

let impl_34 = impl_34'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_35': Core_models.Fmt.t_Debug t_Algorithms

let impl_35 = impl_35'

let impl_Algorithms__new
      (hash: t_HashAlgorithm)
      (aead: t_AeadAlgorithm)
      (sig: t_SignatureScheme)
      (kem: t_KemScheme)
      (psk zero_rtt: bool)
     =
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

let impl_Algorithms__hash (self: t_Algorithms) = self.f_hash

let impl_Algorithms__aead (self: t_Algorithms) = self.f_aead

let impl_Algorithms__signature (self: t_Algorithms) = self.f_signature

let impl_Algorithms__kem (self: t_Algorithms) = self.f_kem

let impl_Algorithms__psk_mode (self: t_Algorithms) = self.f_psk_mode

let impl_Algorithms__zero_rtt (self: t_Algorithms) = self.f_zero_rtt

let impl_Algorithms__ciphersuite (self: t_Algorithms) =
  match self.f_hash, self.f_aead <: (t_HashAlgorithm & t_AeadAlgorithm) with
  | HashAlgorithm_SHA256 , AeadAlgorithm_Aes128Gcm  ->
    Core_models.Result.Result_Ok (Bertie.Tls13utils.bytes2 (mk_u8 19) (mk_u8 1))
    <:
    Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | HashAlgorithm_SHA384 , AeadAlgorithm_Aes256Gcm  ->
    Core_models.Result.Result_Ok (Bertie.Tls13utils.bytes2 (mk_u8 19) (mk_u8 2))
    <:
    Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | HashAlgorithm_SHA256 , AeadAlgorithm_Chacha20Poly1305  ->
    Core_models.Result.Result_Ok (Bertie.Tls13utils.bytes2 (mk_u8 19) (mk_u8 3))
    <:
    Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | _ ->
    Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let impl_Algorithms__supported_group (self: t_Algorithms) =
  match impl_Algorithms__kem self <: t_KemScheme with
  | KemScheme_X25519  ->
    Core_models.Result.Result_Ok (Bertie.Tls13utils.bytes2 (mk_u8 0) (mk_u8 29))
    <:
    Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | KemScheme_Secp256r1  ->
    Core_models.Result.Result_Ok (Bertie.Tls13utils.bytes2 (mk_u8 0) (mk_u8 23))
    <:
    Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | KemScheme_X448  ->
    Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
  | KemScheme_Secp384r1  ->
    Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
  | KemScheme_Secp521r1  ->
    Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
  | KemScheme_X25519MlKem768  ->
    Core_models.Result.Result_Ok (Bertie.Tls13utils.bytes2 (mk_u8 17) (mk_u8 236))
    <:
    Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let impl_Algorithms__signature_algorithm (self: t_Algorithms) =
  match impl_Algorithms__signature self <: t_SignatureScheme with
  | SignatureScheme_RsaPssRsaSha256  ->
    Core_models.Result.Result_Ok (Bertie.Tls13utils.bytes2 (mk_u8 8) (mk_u8 4))
    <:
    Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | SignatureScheme_EcdsaSecp256r1Sha256  ->
    Core_models.Result.Result_Ok (Bertie.Tls13utils.bytes2 (mk_u8 4) (mk_u8 3))
    <:
    Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | SignatureScheme_ED25519  ->
    Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let impl_Algorithms__check (self: t_Algorithms) (bytes: t_Slice u8) =
  match Bertie.Tls13utils.length_u16_encoded bytes <: Core_models.Result.t_Result usize u8 with
  | Core_models.Result.Result_Ok len ->
    (match
        impl_Algorithms__ciphersuite self
        <:
        Core_models.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core_models.Result.Result_Ok cs ->
        let csl:t_Slice u8 =
          bytes.[ {
              Core_models.Ops.Range.f_start = mk_usize 2;
              Core_models.Ops.Range.f_end = mk_usize 2 +! len <: usize
            }
            <:
            Core_models.Ops.Range.t_Range usize ]
        in
        (match
            Bertie.Tls13utils.check_mem (Bertie.Tls13utils.impl_Bytes__as_raw cs <: t_Slice u8) csl
            <:
            Core_models.Result.t_Result Prims.unit u8
          with
          | Core_models.Result.Result_Ok _ ->
            Core_models.Result.Result_Ok (len +! mk_usize 2) <: Core_models.Result.t_Result usize u8
          | Core_models.Result.Result_Err err ->
            Core_models.Result.Result_Err err <: Core_models.Result.t_Result usize u8)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err <: Core_models.Result.t_Result usize u8)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result usize u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_37': Core_models.Convert.t_TryFrom t_Algorithms string

let impl_37 = impl_37'
