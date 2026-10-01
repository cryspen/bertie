module Bertie.Tls13utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Error = | Error_UnknownCiphersuite : Alloc.String.t_String -> t_Error

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_10:Core_models.Fmt.t_Debug t_Error

let impl_11: Core_models.Clone.t_Clone t_Error =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

let v_UNSUPPORTED_ALGORITHM: u8 = mk_u8 1

let v_CRYPTO_ERROR: u8 = mk_u8 2

let v_INSUFFICIENT_ENTROPY: u8 = mk_u8 3

let v_INCORRECT_ARRAY_LENGTH: u8 = mk_u8 4

let v_INCORRECT_STATE: u8 = mk_u8 128

let v_ZERO_RTT_DISABLED: u8 = mk_u8 129

let v_PAYLOAD_TOO_LONG: u8 = mk_u8 130

let v_PSK_MODE_MISMATCH: u8 = mk_u8 131

let v_NEGOTIATION_MISMATCH: u8 = mk_u8 132

let v_PARSE_FAILED: u8 = mk_u8 133

val parse_failed: Prims.unit -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v_INSUFFICIENT_DATA: u8 = mk_u8 134

let v_UNSUPPORTED: u8 = mk_u8 135

let v_INVALID_COMPRESSION_LIST: u8 = mk_u8 136

let v_PROTOCOL_VERSION_ALERT: u8 = mk_u8 137

let v_APPLICATION_DATA_INSTEAD_OF_HANDSHAKE: u8 = mk_u8 138

let v_MISSING_KEY_SHARE: u8 = mk_u8 139

let v_INVALID_SIGNATURE: u8 = mk_u8 140

let v_GOT_HANDSHAKE_FAILURE_ALERT: u8 = mk_u8 141

let v_DECODE_ERROR: u8 = mk_u8 142

val error_string (c: u8) : Prims.Pure Alloc.String.t_String Prims.l_True (fun _ -> Prims.l_True)

val tlserr (#v_T: Type0) (err: u8)
    : Prims.Pure (Core_models.Result.t_Result v_T u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result v_T u8 = result in
          Core_models.Result.impl__is_err #v_T #u8 result)

val v_U8 (x: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val v_U16 (x: u16) : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val v_U32 (x: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

/// Bytes used in Bertie.
type t_Bytes = | Bytes : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global -> t_Bytes

let impl_12: Core_models.Clone.t_Clone t_Bytes =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_13:Core_models.Marker.t_StructuralPartialEq t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_14:Core_models.Cmp.t_PartialEq t_Bytes t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_15:Core_models.Fmt.t_Debug t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_16:Core_models.Default.t_Default t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:Core_models.Convert.t_From t_Bytes (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

/// Assume that growing a vector of length `len` by `extra` elements does not
/// overflow `usize`. In Rust, the allocation fails first.
val assume_no_alloc_overflow (len extra: usize)
    : Prims.Pure Prims.unit
      Prims.l_True
      (ensures
        fun temp_0_ ->
          let _:Prims.unit = temp_0_ in
          ((Rust_primitives.Hax.Int.from_machine len <: Hax_lib.Int.t_Int) +
            (Rust_primitives.Hax.Int.from_machine extra <: Hax_lib.Int.t_Int)
            <:
            Hax_lib.Int.t_Int) <=
          (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int
          ))

/// Convert the bytes into raw bytes
val impl_Bytes__into_raw (self: t_Bytes)
    : Prims.Pure (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Prims.l_True (fun _ -> Prims.l_True)

/// Declassify these bytes and return a copy of [`u8`].
val impl_Bytes__declassify (self: t_Bytes)
    : Prims.Pure (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Prims.l_True
      (ensures
        fun result ->
          let result:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = result in
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global result <: usize) =.
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self._0 <: usize))

/// Get a reference to the raw bytes.
val impl_Bytes__as_raw (self: t_Bytes)
    : Prims.Pure (t_Slice u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Slice u8 = result in
          (Core_models.Slice.impl__len #u8 result <: usize) =.
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self._0 <: usize))

val impl_Bytes__declassify_array (v_C: usize) (self: t_Bytes)
    : Prims.Pure (Core_models.Result.t_Result (t_Array u8 v_C) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val u16_as_be_bytes (v_val: u16)
    : Prims.Pure (t_Array u8 (mk_usize 2)) Prims.l_True (fun _ -> Prims.l_True)

val u32_as_be_bytes (v_val: u32)
    : Prims.Pure (t_Array u8 (mk_usize 4)) Prims.l_True (fun _ -> Prims.l_True)

val u32_from_be_bytes (v_val: t_Array u8 (mk_usize 4))
    : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core_models.Ops.Index.t_Index t_Bytes usize =
  {
    f_Output = u8;
    f_index_pre
    =
    (fun (self_: t_Bytes) (x: usize) ->
        x <. (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self_._0 <: usize));
    f_index_post = (fun (self: t_Bytes) (x: usize) (out: u8) -> true);
    f_index = fun (self: t_Bytes) (x: usize) -> self._0.[ x ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core_models.Ops.Index.t_Index t_Bytes (Core_models.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index_pre
    =
    (fun (self_: t_Bytes) (x: Core_models.Ops.Range.t_Range usize) ->
        x.Core_models.Ops.Range.f_start <=. x.Core_models.Ops.Range.f_end &&
        x.Core_models.Ops.Range.f_end <=.
        (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self_._0 <: usize));
    f_index_post
    =
    (fun (self_: t_Bytes) (x: Core_models.Ops.Range.t_Range usize) (result: t_Slice u8) ->
        if x.Core_models.Ops.Range.f_end >=. x.Core_models.Ops.Range.f_start
        then
          (Core_models.Slice.impl__len #u8 result <: usize) =.
          (x.Core_models.Ops.Range.f_end -! x.Core_models.Ops.Range.f_start <: usize)
        else (Core_models.Slice.impl__len #u8 result <: usize) =. mk_usize 0);
    f_index = fun (self: t_Bytes) (x: Core_models.Ops.Range.t_Range usize) -> self._0.[ x ]
  }

/// Create new [`Bytes`].
val impl_Bytes__new: Prims.unit -> Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Create new [`Bytes`].
val impl_Bytes__new_alloc (len: usize)
    : Prims.Pure t_Bytes
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Bytes = result in
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global result._0 <: usize) =. mk_usize 0)

/// Generate `len` bytes of `0`.
val impl_Bytes__zeroes (len: usize)
    : Prims.Pure t_Bytes
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Bytes = result in
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global result._0 <: usize) =. len)

/// Get the length of these [`Bytes`].
val impl_Bytes__len (self: t_Bytes)
    : Prims.Pure usize
      Prims.l_True
      (ensures
        fun result ->
          let result:usize = result in
          result =. (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self._0 <: usize))

/// Add a prefix to these bytes and return it.
val impl_Bytes__prefix (self: t_Bytes) (prefix: t_Slice u8)
    : Prims.Pure t_Bytes
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Bytes = result in
          (impl_Bytes__len result <: usize) >=. (impl_Bytes__len self <: usize) &&
          ((impl_Bytes__len result <: usize) -! (impl_Bytes__len self <: usize) <: usize) =.
          (Core_models.Slice.impl__len #u8 prefix <: usize))

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_18:Core_models.Convert.t_From t_Bytes (t_Slice u8)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_19 (v_C: usize) : Core_models.Convert.t_From t_Bytes (t_Array u8 v_C)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_20 (v_C: usize) : Core_models.Convert.t_From t_Bytes (t_Array u8 v_C)

val bytes (x: t_Slice u8)
    : Prims.Pure t_Bytes
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Bytes = result in
          (impl_Bytes__len result <: usize) =. (Core_models.Slice.impl__len #u8 x <: usize))

val bytes1 (x: u8)
    : Prims.Pure t_Bytes
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Bytes = result in
          (impl_Bytes__len result <: usize) =. mk_usize 1)

val bytes2 (x y: u8)
    : Prims.Pure t_Bytes
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Bytes = result in
          (impl_Bytes__len result <: usize) =. mk_usize 2)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let update_at_usize_bytes: Rust_primitives.Hax.update_at_tc t_Bytes usize =
   {
     super_index = impl_21;
     update_at = fun s i x -> Bytes (Alloc.Vec.from_seq (Seq.upd s._0._0 (v i) x))
   }

/// This is needed only for hax, so should likely be guarded by a feature flag.
val e_update_at_usize_bytes_test (b: t_Bytes)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Generate a new [`Bytes`] struct from slice `s`.
val impl_Bytes__from_slice (s: t_Slice u8) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Push `x` into these [`Bytes`].
val impl_Bytes__push (self: t_Bytes) (x: u8)
    : Prims.Pure t_Bytes
      Prims.l_True
      (ensures
        fun self_e_future ->
          let self_e_future:t_Bytes = self_e_future in
          (Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                  #Alloc.Alloc.t_Global
                  self_e_future._0
                <:
                usize)
            <:
            Hax_lib.Int.t_Int) =
          ((Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                    #Alloc.Alloc.t_Global
                    self._0
                  <:
                  usize)
              <:
              Hax_lib.Int.t_Int) +
            (Rust_primitives.Hax.Int.from_machine (mk_i32 1) <: Hax_lib.Int.t_Int)
            <:
            Hax_lib.Int.t_Int))

/// Extend `self` with the slice `x`.
val impl_Bytes__extend_from_slice (self x: t_Bytes)
    : Prims.Pure t_Bytes
      Prims.l_True
      (ensures
        fun self_e_future ->
          let self_e_future:t_Bytes = self_e_future in
          (Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                  #Alloc.Alloc.t_Global
                  self_e_future._0
                <:
                usize)
            <:
            Hax_lib.Int.t_Int) =
          ((Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                    #Alloc.Alloc.t_Global
                    self._0
                  <:
                  usize)
              <:
              Hax_lib.Int.t_Int) +
            (Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                    #Alloc.Alloc.t_Global
                    x._0
                  <:
                  usize)
              <:
              Hax_lib.Int.t_Int)
            <:
            Hax_lib.Int.t_Int))

val concat_inner (bytes other: t_Bytes) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Extend `self` with the bytes `x`.
val impl_Bytes__append (self x: t_Bytes)
    : Prims.Pure t_Bytes
      Prims.l_True
      (ensures
        fun self_e_future ->
          let self_e_future:t_Bytes = self_e_future in
          (Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                  #Alloc.Alloc.t_Global
                  self_e_future._0
                <:
                usize)
            <:
            Hax_lib.Int.t_Int) =
          ((Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                    #Alloc.Alloc.t_Global
                    self._0
                  <:
                  usize)
              <:
              Hax_lib.Int.t_Int) +
            (Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                    #Alloc.Alloc.t_Global
                    x._0
                  <:
                  usize)
              <:
              Hax_lib.Int.t_Int)
            <:
            Hax_lib.Int.t_Int))

/// Get a slice of the given `range`.
val impl_Bytes__raw_slice (self: t_Bytes) (range: Core_models.Ops.Range.t_Range usize)
    : Prims.Pure (t_Slice u8)
      (requires
        range.Core_models.Ops.Range.f_start <=. range.Core_models.Ops.Range.f_end &&
        range.Core_models.Ops.Range.f_end <=.
        (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self._0 <: usize))
      (ensures
        fun result ->
          let result:t_Slice u8 = result in
          (Core_models.Slice.impl__len #u8 result <: usize) =.
          (range.Core_models.Ops.Range.f_end -! range.Core_models.Ops.Range.f_start <: usize))

/// Get a new copy of the given `range` as [`Bytes`].
val impl_Bytes__slice_range (self: t_Bytes) (range: Core_models.Ops.Range.t_Range usize)
    : Prims.Pure t_Bytes
      (requires
        range.Core_models.Ops.Range.f_start <=. range.Core_models.Ops.Range.f_end &&
        range.Core_models.Ops.Range.f_end <=.
        (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self._0 <: usize))
      (ensures
        fun result ->
          let result:t_Bytes = result in
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global result._0 <: usize) =.
          (range.Core_models.Ops.Range.f_end -! range.Core_models.Ops.Range.f_start <: usize))

/// Get a new copy of the given range `[start..start+len]` as [`Bytes`].
val impl_Bytes__slice (self: t_Bytes) (start len: usize)
    : Prims.Pure t_Bytes
      (requires
        (Rust_primitives.Hax.Int.from_machine start <: Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                #Alloc.Alloc.t_Global
                self._0
              <:
              usize)
          <:
          Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine start <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine len <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                #Alloc.Alloc.t_Global
                self._0
              <:
              usize)
          <:
          Hax_lib.Int.t_Int))
      (ensures
        fun result ->
          let result:t_Bytes = result in
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global result._0 <: usize) =. len)

/// Concatenate `other` with these bytes and return a copy as [`Bytes`].
val impl_Bytes__concat (self other: t_Bytes)
    : Prims.Pure t_Bytes
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Bytes = result in
          (Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                  #Alloc.Alloc.t_Global
                  result._0
                <:
                usize)
            <:
            Hax_lib.Int.t_Int) =
          ((Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                    #Alloc.Alloc.t_Global
                    self._0
                  <:
                  usize)
              <:
              Hax_lib.Int.t_Int) +
            (Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                    #Alloc.Alloc.t_Global
                    other._0
                  <:
                  usize)
              <:
              Hax_lib.Int.t_Int)
            <:
            Hax_lib.Int.t_Int))

/// Concatenate `other` with these bytes and return a copy as [`Bytes`].
val impl_Bytes__concat_array (v_N: usize) (self: t_Bytes) (other: t_Array u8 v_N)
    : Prims.Pure t_Bytes
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Bytes = result in
          (Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                  #Alloc.Alloc.t_Global
                  result._0
                <:
                usize)
            <:
            Hax_lib.Int.t_Int) =
          ((Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                    #Alloc.Alloc.t_Global
                    self._0
                  <:
                  usize)
              <:
              Hax_lib.Int.t_Int) +
            (Rust_primitives.Hax.Int.from_machine v_N <: Hax_lib.Int.t_Int)
            <:
            Hax_lib.Int.t_Int))

/// Update the slice `self[start..start+len] = other[beg..beg+len]` and return
/// a copy as [`Bytes`].
val impl_Bytes__update_slice (self: t_Bytes) (start: usize) (other: t_Bytes) (beg len: usize)
    : Prims.Pure t_Bytes
      (requires
        ((Rust_primitives.Hax.Int.from_machine start <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine len <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                #Alloc.Alloc.t_Global
                self._0
              <:
              usize)
          <:
          Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine beg <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine len <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (Alloc.Vec.impl_1__len #u8
                #Alloc.Alloc.t_Global
                other._0
              <:
              usize)
          <:
          Hax_lib.Int.t_Int))
      (ensures
        fun result ->
          let result:t_Bytes = result in
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global result._0 <: usize) =.
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self._0 <: usize))

/// Convert the bool `b` into a Result.
val check (b: bool)
    : Prims.Pure (Core_models.Result.t_Result Prims.unit u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result Prims.unit u8 = result in
          match result <: Core_models.Result.t_Result Prims.unit u8 with
          | Core_models.Result.Result_Ok () -> b =. true
          | _ -> true)

/// Attempt to TLS encode the `bytes` with [`u8`] length.
/// On success, return a new [Bytes] slice such that its first byte encodes the
/// length of `bytes` and the remainder equals `bytes`. Return a [TLSError] if
/// the length of `bytes` exceeds what can be encoded in one byte.
val encode_length_u8 (bytes: t_Slice u8)
    : Prims.Pure (Core_models.Result.t_Result t_Bytes u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result t_Bytes u8 = result in
          match result <: Core_models.Result.t_Result t_Bytes u8 with
          | Core_models.Result.Result_Ok lenb ->
            (Core_models.Slice.impl__len #u8 bytes <: usize) <. mk_usize 256 &&
            (impl_Bytes__len lenb <: usize) >=. mk_usize 1 &&
            ((impl_Bytes__len lenb <: usize) -! mk_usize 1 <: usize) =.
            (Core_models.Slice.impl__len #u8 bytes <: usize)
          | _ -> true)

/// Attempt to TLS encode the `bytes` with [`u16`] length.
/// On success, return a new [Bytes] slice such that its first two bytes encode the
/// big-endian length of `bytes` and the remainder equals `bytes`. Return a [TLSError] if
/// the length of `bytes` exceeds what can be encoded in two bytes.
val encode_length_u16 (bytes: t_Bytes)
    : Prims.Pure (Core_models.Result.t_Result t_Bytes u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result t_Bytes u8 = result in
          match result <: Core_models.Result.t_Result t_Bytes u8 with
          | Core_models.Result.Result_Ok lenb ->
            (impl_Bytes__len bytes <: usize) <. mk_usize 65536 &&
            (impl_Bytes__len lenb <: usize) >=. mk_usize 2 &&
            ((impl_Bytes__len lenb <: usize) -! mk_usize 2 <: usize) =.
            (impl_Bytes__len bytes <: usize)
          | _ -> true)

/// Attempt to TLS encode the `bytes` with [`u24`] length.
/// On success, return a new [Bytes] slice such that its first three bytes encode the
/// big-endian length of `bytes` and the remainder equals `bytes`. Return a [TLSError] if
/// the length of `bytes` exceeds what can be encoded in three bytes.
val encode_length_u24 (bytes: t_Bytes)
    : Prims.Pure (Core_models.Result.t_Result t_Bytes u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result t_Bytes u8 = result in
          match result <: Core_models.Result.t_Result t_Bytes u8 with
          | Core_models.Result.Result_Ok lenb ->
            (impl_Bytes__len bytes <: usize) <. mk_usize 16777216 &&
            (impl_Bytes__len lenb <: usize) >=. mk_usize 3 &&
            ((impl_Bytes__len lenb <: usize) -! mk_usize 3 <: usize) =.
            (impl_Bytes__len bytes <: usize)
          | _ -> true)

type t_AppData = | AppData : t_Bytes -> t_AppData

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_24:Core_models.Marker.t_StructuralPartialEq t_AppData

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_25:Core_models.Cmp.t_PartialEq t_AppData t_AppData

/// Create new application data from raw bytes.
val impl_AppData__new (b: t_Bytes) : Prims.Pure t_AppData Prims.l_True (fun _ -> Prims.l_True)

/// Convert this application data into raw bytes
val impl_AppData__into_raw (self: t_AppData)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Get a reference to the raw bytes.
val impl_AppData__as_raw (self: t_AppData) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_6:Core_models.Convert.t_From t_AppData (t_Slice u8)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_7 (v_N: usize) : Core_models.Convert.t_From t_AppData (t_Array u8 v_N)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_8:Core_models.Convert.t_From t_AppData (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_9:Core_models.Convert.t_From t_AppData t_Bytes

class t_Declassify (v_Self: Type0) (v_T: Type0) = {
  f_declassify_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_declassify_post:v_Self -> v_T -> Type0;
  f_declassify:x0: v_Self
    -> Prims.Pure v_T (f_declassify_pre x0) (fun result -> f_declassify_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:t_Declassify u8 u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:t_Declassify u32 u32

/// Test if [Bytes] `b1` and `b2` have the same value.
val eq1 (b1 b2: u8)
    : Prims.Pure bool
      Prims.l_True
      (ensures
        fun result ->
          let result:bool = result in
          result =. (b1 =. b2 <: bool))

/// Parser function to check if [Bytes] `b1` and `b2` have the same value,
/// returning a [TLSError] otherwise.
val check_eq1 (b1 b2: u8)
    : Prims.Pure (Core_models.Result.t_Result Prims.unit u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result Prims.unit u8 = result in
          match result <: Core_models.Result.t_Result Prims.unit u8 with
          | Core_models.Result.Result_Ok _ -> b1 =. b2
          | _ -> true)

/// Check if [U8] slices `b1` and `b2` are of the same
/// length and agree on all positions.
val eq_slice (b1 b2: t_Slice u8)
    : Prims.Pure bool
      Prims.l_True
      (ensures
        fun result ->
          let result:bool = result in
          b2t result ==> b2t (b1 =. b2 <: bool))

val eq_inner (b1 b2: t_Bytes)
    : Prims.Pure bool
      Prims.l_True
      (ensures
        fun result ->
          let result:bool = result in
          b2t result ==> b2t (b1 =. b2 <: bool))

/// Check if [Bytes] slices `b1` and `b2` are of the same
/// length and agree on all positions.
val eq (b1 b2: t_Bytes) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Parse function to check if two slices `b1` and `b2` are of the same
/// length and agree on all positions, returning a [TLSError] otherwise.
val check_eq_slice (b1 b2: t_Slice u8)
    : Prims.Pure (Core_models.Result.t_Result Prims.unit u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result Prims.unit u8 = result in
          match result <: Core_models.Result.t_Result Prims.unit u8 with
          | Core_models.Result.Result_Ok _ -> b1 =. b2
          | _ -> true)

val check_eq_inner (b1 b2: t_Bytes)
    : Prims.Pure (Core_models.Result.t_Result Prims.unit u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result Prims.unit u8 = result in
          match result <: Core_models.Result.t_Result Prims.unit u8 with
          | Core_models.Result.Result_Ok _ -> b1 =. b2
          | _ -> true)

/// Parse function to check if two slices `b1` and `b2` are of the same
/// length and agree on all positions, returning a [TLSError] otherwise.
val check_eq_with_slice (b1 b2: t_Slice u8) (start v_end: usize)
    : Prims.Pure (Core_models.Result.t_Result Prims.unit u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result Prims.unit u8 = result in
          match result <: Core_models.Result.t_Result Prims.unit u8 with
          | Core_models.Result.Result_Ok _ ->
            (Core_models.Slice.impl__len #u8 b2 <: usize) >=. v_end &&
            (Core_models.Slice.impl__len #u8 b2 <: usize) >=. start &&
            start <=. v_end
          | _ -> true)

/// Parse function to check if [Bytes] slices `b1` and `b2` are of the same
/// length and agree on all positions, returning a [TLSError] otherwise.
val check_eq (b1 b2: t_Bytes)
    : Prims.Pure (Core_models.Result.t_Result Prims.unit u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result Prims.unit u8 = result in
          match result <: Core_models.Result.t_Result Prims.unit u8 with
          | Core_models.Result.Result_Ok _ -> b1 =. b2
          | _ -> true)

/// Parse function to check if two [Option<Bytes>] slices `b1` and `b2` are of the same
/// length and agree on all positions, returning a [TLSError] otherwise.
val check_eq_option (b1 b2: Core_models.Option.t_Option t_Bytes)
    : Prims.Pure (Core_models.Result.t_Result Prims.unit u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result Prims.unit u8 = result in
          match result <: Core_models.Result.t_Result Prims.unit u8 with
          | Core_models.Result.Result_Ok _ -> b1 =. b2
          | _ -> true)

/// Compare the two provided byte slices.
/// Returns `Ok(())` when they are equal, and a [`TLSError`] otherwise.
val check_mem (b1 b2: t_Slice u8)
    : Prims.Pure (Core_models.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Check if `bytes[1..]` is at least as long as the length encoded by
/// `bytes[0]` in big-endian order.
/// On success, return the encoded length. Return a [TLSError] if `bytes` is
/// empty or if the encoded length exceeds the length of the remainder of
/// `bytes`.
val length_u8_encoded (bytes: t_Slice u8)
    : Prims.Pure (Core_models.Result.t_Result usize u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result usize u8 = result in
          match result <: Core_models.Result.t_Result usize u8 with
          | Core_models.Result.Result_Ok l ->
            (Core_models.Slice.impl__len #u8 bytes <: usize) >=. mk_usize 1 &&
            ((Core_models.Slice.impl__len #u8 bytes <: usize) -! mk_usize 1 <: usize) >=. l &&
            l <. mk_usize 256
          | _ -> true)

/// Check if `bytes[2..]` is at least as long as the length encoded by `bytes[0..2]`
/// in big-endian order.
/// On success, return the encoded length. Return a [TLSError] if `bytes` is less than 2
/// bytes long or if the encoded length exceeds the length of the remainder of
/// `bytes`.
val length_u16_encoded_slice (bytes: t_Slice u8)
    : Prims.Pure (Core_models.Result.t_Result usize u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result usize u8 = result in
          match result <: Core_models.Result.t_Result usize u8 with
          | Core_models.Result.Result_Ok l ->
            (Core_models.Slice.impl__len #u8 bytes <: usize) >=. mk_usize 2 &&
            ((Core_models.Slice.impl__len #u8 bytes <: usize) -! mk_usize 2 <: usize) >=. l &&
            l <. mk_usize 65536
          | _ -> true)

/// Check if `bytes[2..]` is at least as long as the length encoded by `bytes[0..2]`
/// in big-endian order.
/// On success, return the encoded length. Return a [TLSError] if `bytes` is less than 2
/// bytes long or if the encoded length exceeds the length of the remainder of
/// `bytes`.
val length_u16_encoded (bytes: t_Slice u8)
    : Prims.Pure (Core_models.Result.t_Result usize u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result usize u8 = result in
          match result <: Core_models.Result.t_Result usize u8 with
          | Core_models.Result.Result_Ok l ->
            (Core_models.Slice.impl__len #u8 bytes <: usize) >=. mk_usize 2 &&
            ((Core_models.Slice.impl__len #u8 bytes <: usize) -! mk_usize 2 <: usize) >=. l &&
            l <. mk_usize 65536
          | _ -> true)

/// Check if `bytes[3..]` is at least as long as the length encoded by `bytes[0..3]`
/// in big-endian order.
/// On success, return the encoded length. Return a [TLSError] if `bytes` is less than 3
/// bytes long or if the encoded length exceeds the length of the remainder of
/// `bytes`.
val length_u24_encoded (bytes: t_Slice u8)
    : Prims.Pure (Core_models.Result.t_Result usize u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result usize u8 = result in
          match result <: Core_models.Result.t_Result usize u8 with
          | Core_models.Result.Result_Ok l ->
            (Core_models.Slice.impl__len #u8 bytes <: usize) >=. mk_usize 3 &&
            ((Core_models.Slice.impl__len #u8 bytes <: usize) -! mk_usize 3 <: usize) >=. l &&
            l <. mk_usize 16777216
          | _ -> true)

val check_length_encoding_u8_slice (bytes: t_Slice u8)
    : Prims.Pure (Core_models.Result.t_Result Prims.unit u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result Prims.unit u8 = result in
          match result <: Core_models.Result.t_Result Prims.unit u8 with
          | Core_models.Result.Result_Ok _ ->
            (Core_models.Slice.impl__len #u8 bytes <: usize) >=. mk_usize 1 &&
            (Core_models.Slice.impl__len #u8 bytes <: usize) <=. mk_usize 256
          | _ -> true)

/// Check if `bytes` contains exactly the TLS `u8` length encoded content.
/// Returns `Ok(())` if there are no bytes left, and a [`TLSError`] if there are
/// more bytes in the `bytes`.
val check_length_encoding_u8 (bytes: t_Bytes)
    : Prims.Pure (Core_models.Result.t_Result Prims.unit u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result Prims.unit u8 = result in
          match result <: Core_models.Result.t_Result Prims.unit u8 with
          | Core_models.Result.Result_Ok _ ->
            (impl_Bytes__len bytes <: usize) >=. mk_usize 1 &&
            (impl_Bytes__len bytes <: usize) <=. mk_usize 256
          | _ -> true)

val check_length_encoding_u16_slice (bytes: t_Slice u8)
    : Prims.Pure (Core_models.Result.t_Result Prims.unit u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result Prims.unit u8 = result in
          match result <: Core_models.Result.t_Result Prims.unit u8 with
          | Core_models.Result.Result_Ok _ ->
            (Core_models.Slice.impl__len #u8 bytes <: usize) >=. mk_usize 2 &&
            (Core_models.Slice.impl__len #u8 bytes <: usize) <=. mk_usize 65537
          | _ -> true)

/// Check if `bytes` contains exactly as many bytes of content as encoded by its
/// first two bytes.
/// Returns `Ok(())` if there are no bytes left, and a [`TLSError`] if there are
/// more bytes in the `bytes`.
val check_length_encoding_u16 (bytes: t_Bytes)
    : Prims.Pure (Core_models.Result.t_Result Prims.unit u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result Prims.unit u8 = result in
          match result <: Core_models.Result.t_Result Prims.unit u8 with
          | Core_models.Result.Result_Ok _ ->
            (impl_Bytes__len bytes <: usize) >=. mk_usize 2 &&
            (impl_Bytes__len bytes <: usize) <=. mk_usize 65537
          | _ -> true)

/// Check if `bytes` contains exactly as many bytes of content as encoded by its
/// first three bytes.
/// Returns `Ok(())` if there are no bytes left, and a [`TLSError`] if there are
/// more bytes in the `bytes`.
val check_length_encoding_u24 (bytes: t_Slice u8)
    : Prims.Pure (Core_models.Result.t_Result Prims.unit u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Result.t_Result Prims.unit u8 = result in
          match result <: Core_models.Result.t_Result Prims.unit u8 with
          | Core_models.Result.Result_Ok _ ->
            (Core_models.Slice.impl__len #u8 bytes <: usize) >=. mk_usize 3 &&
            (Core_models.Slice.impl__len #u8 bytes <: usize) <=. mk_usize 16777218
          | _ -> true)
