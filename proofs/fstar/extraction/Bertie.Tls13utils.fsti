module Bertie.Tls13utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Rand.Distr.Distribution in
  let open Rand.Distr.Integer in
  ()

type t_Error = | Error_UnknownCiphersuite : Alloc.String.t_String -> t_Error

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_17:Core.Fmt.t_Debug t_Error

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_18:Core.Clone.t_Clone t_Error

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
    : Prims.Pure (Core.Result.t_Result v_T u8) Prims.l_True (fun _ -> Prims.l_True)

class t_Declassify (v_Self: Type0) (v_T: Type0) = {
  f_declassify_pre:v_Self -> Type0;
  f_declassify_post:v_Self -> v_T -> Type0;
  f_declassify:x0: v_Self
    -> Prims.Pure v_T (f_declassify_pre x0) (fun result -> f_declassify_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:t_Declassify u8 u8

val v_U8 (x: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val v_U16 (x: u16) : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val v_U32 (x: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:t_Declassify u32 u32

/// Bytes used in Bertie.
type t_Bytes = | Bytes : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global -> t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_19:Core.Clone.t_Clone t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_20:Core.Marker.t_StructuralPartialEq t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_21:Core.Cmp.t_PartialEq t_Bytes t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_22:Core.Fmt.t_Debug t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_23:Core.Default.t_Default t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:Core.Convert.t_From t_Bytes (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

/// Declassify these bytes and return a copy of [`u8`].
val impl_Bytes__declassify (self: t_Bytes)
    : Prims.Pure (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Prims.l_True (fun _ -> Prims.l_True)

/// Convert the bytes into raw bytes
val impl_Bytes__into_raw (self: t_Bytes)
    : Prims.Pure (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Prims.l_True (fun _ -> Prims.l_True)

/// Get a reference to the raw bytes.
val impl_Bytes__as_raw (self: t_Bytes)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val impl_Bytes__declassify_array (v_C: usize) (self: t_Bytes)
    : Prims.Pure (Core.Result.t_Result (t_Array u8 v_C) u8) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_5:Core.Convert.t_From t_Bytes (t_Slice u8)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_6 (v_C: usize) : Core.Convert.t_From t_Bytes (t_Array u8 v_C)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_7 (v_C: usize) : Core.Convert.t_From t_Bytes (t_Array u8 v_C)

val u16_as_be_bytes (v_val: u16)
    : Prims.Pure (t_Array u8 (mk_usize 2)) Prims.l_True (fun _ -> Prims.l_True)

val u32_as_be_bytes (v_val: u32)
    : Prims.Pure (t_Array u8 (mk_usize 4)) Prims.l_True (fun _ -> Prims.l_True)

val u32_from_be_bytes (v_val: t_Array u8 (mk_usize 4))
    : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val bytes (x: t_Slice u8) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val bytes1 (x: u8) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val bytes2 (x y: u8) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Ops.Index.t_Index t_Bytes usize =
  {
    f_Output = u8;
    f_index_pre = (fun (self: t_Bytes) (x: usize) -> true);
    f_index_post = (fun (self: t_Bytes) (x: usize) (out: u8) -> true);
    f_index = fun (self: t_Bytes) (x: usize) -> self._0.[ x ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Ops.Index.t_Index t_Bytes (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index_pre = (fun (self: t_Bytes) (x: Core.Ops.Range.t_Range usize) -> true);
    f_index_post = (fun (self: t_Bytes) (x: Core.Ops.Range.t_Range usize) (out: t_Slice u8) -> true);
    f_index = fun (self: t_Bytes) (x: Core.Ops.Range.t_Range usize) -> self._0.[ x ]
  }

/// Create new [`Bytes`].
val impl_Bytes__new: Prims.unit -> Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Create new [`Bytes`].
val impl_Bytes__new_alloc (len: usize) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Generate `len` bytes of `0`.
val impl_Bytes__zeroes (len: usize) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Get the length of these [`Bytes`].
val impl_Bytes__len (self: t_Bytes) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// Add a prefix to these bytes and return it.
val impl_Bytes__prefix (self: t_Bytes) (prefix: t_Slice u8)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Push `x` into these [`Bytes`].
val impl_Bytes__push (self: t_Bytes) (x: u8)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Extend `self` with the slice `x`.
val impl_Bytes__extend_from_slice (self x: t_Bytes)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Extend `self` with the bytes `x`.
val impl_Bytes__append (self x: t_Bytes) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Generate a new [`Bytes`] struct from slice `s`.
val impl_Bytes__from_slice (s: t_Slice u8) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Read a hex string into [`Bytes`].
val impl_Bytes__from_hex (s: string) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Get a slice of the given `range`.
val impl_Bytes__raw_slice (self: t_Bytes) (range: Core.Ops.Range.t_Range usize)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// Get a new copy of the given `range` as [`Bytes`].
val impl_Bytes__slice_range (self: t_Bytes) (range: Core.Ops.Range.t_Range usize)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Get a new copy of the given range `[start..start+len]` as [`Bytes`].
val impl_Bytes__slice (self: t_Bytes) (start len: usize)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Concatenate `other` with these bytes and return a copy as [`Bytes`].
val impl_Bytes__concat (self other: t_Bytes)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Concatenate `other` with these bytes and return a copy as [`Bytes`].
val impl_Bytes__concat_array (v_N: usize) (self: t_Bytes) (other: t_Array u8 v_N)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Update the slice `self[start..start+len] = other[beg..beg+len]` and return
/// a copy as [`Bytes`].
val impl_Bytes__update_slice (self: t_Bytes) (start: usize) (other: t_Bytes) (beg len: usize)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Convert the bool `b` into a Result.
val check (b: bool)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Test if [Bytes] `b1` and `b2` have the same value.
val eq1 (b1 b2: u8) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Parser function to check if [Bytes] `b1` and `b2` have the same value,
/// returning a [TLSError] otherwise.
val check_eq1 (b1 b2: u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Check if [U8] slices `b1` and `b2` are of the same
/// length and agree on all positions.
val eq_slice (b1 b2: t_Slice u8) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Check if [Bytes] slices `b1` and `b2` are of the same
/// length and agree on all positions.
val eq (b1 b2: t_Bytes) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Parse function to check if two slices `b1` and `b2` are of the same
/// length and agree on all positions, returning a [TLSError] otherwise.
val check_eq_slice (b1 b2: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Parse function to check if two slices `b1` and `b2` are of the same
/// length and agree on all positions, returning a [TLSError] otherwise.
val check_eq_with_slice (b1 b2: t_Slice u8) (start v_end: usize)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Parse function to check if [Bytes] slices `b1` and `b2` are of the same
/// length and agree on all positions, returning a [TLSError] otherwise.
val check_eq (b1 b2: t_Bytes)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Compare the two provided byte slices.
/// Returns `Ok(())` when they are equal, and a [`TLSError`] otherwise.
val check_mem (b1 b2: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Attempt to TLS encode the `bytes` with [`u8`] length.
/// On success, return a new [Bytes] slice such that its first byte encodes the
/// length of `bytes` and the remainder equals `bytes`. Return a [TLSError] if
/// the length of `bytes` exceeds what can be encoded in one byte.
val encode_length_u8 (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result t_Bytes u8) Prims.l_True (fun _ -> Prims.l_True)

/// Attempt to TLS encode the `bytes` with [`u16`] length.
/// On success, return a new [Bytes] slice such that its first two bytes encode the
/// big-endian length of `bytes` and the remainder equals `bytes`. Return a [TLSError] if
/// the length of `bytes` exceeds what can be encoded in two bytes.
val encode_length_u16 (bytes: t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_Bytes u8) Prims.l_True (fun _ -> Prims.l_True)

/// Attempt to TLS encode the `bytes` with [`u24`] length.
/// On success, return a new [Bytes] slice such that its first three bytes encode the
/// big-endian length of `bytes` and the remainder equals `bytes`. Return a [TLSError] if
/// the length of `bytes` exceeds what can be encoded in three bytes.
val encode_length_u24 (bytes: t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_Bytes u8) Prims.l_True (fun _ -> Prims.l_True)

/// Check if `bytes[1..]` is at least as long as the length encoded by
/// `bytes[0]` in big-endian order.
/// On success, return the encoded length. Return a [TLSError] if `bytes` is
/// empty or if the encoded length exceeds the length of the remainder of
/// `bytes`.
val length_u8_encoded (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

/// Check if `bytes[2..]` is at least as long as the length encoded by `bytes[0..2]`
/// in big-endian order.
/// On success, return the encoded length. Return a [TLSError] if `bytes` is less than 2
/// bytes long or if the encoded length exceeds the length of the remainder of
/// `bytes`.
val length_u16_encoded_slice (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

/// Check if `bytes[2..]` is at least as long as the length encoded by `bytes[0..2]`
/// in big-endian order.
/// On success, return the encoded length. Return a [TLSError] if `bytes` is less than 2
/// bytes long or if the encoded length exceeds the length of the remainder of
/// `bytes`.
val length_u16_encoded (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

/// Check if `bytes[3..]` is at least as long as the length encoded by `bytes[0..3]`
/// in big-endian order.
/// On success, return the encoded length. Return a [TLSError] if `bytes` is less than 3
/// bytes long or if the encoded length exceeds the length of the remainder of
/// `bytes`.
val length_u24_encoded (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True (fun _ -> Prims.l_True)

val check_length_encoding_u8_slice (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Check if `bytes` contains exactly the TLS `u8` length encoded content.
/// Returns `Ok(())` if there are no bytes left, and a [`TLSError`] if there are
/// more bytes in the `bytes`.
val check_length_encoding_u8 (bytes: t_Bytes)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val check_length_encoding_u16_slice (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Check if `bytes` contains exactly as many bytes of content as encoded by its
/// first two bytes.
/// Returns `Ok(())` if there are no bytes left, and a [`TLSError`] if there are
/// more bytes in the `bytes`.
val check_length_encoding_u16 (bytes: t_Bytes)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

/// Check if `bytes` contains exactly as many bytes of content as encoded by its
/// first three bytes.
/// Returns `Ok(())` if there are no bytes left, and a [`TLSError`] if there are
/// more bytes in the `bytes`.
val check_length_encoding_u24 (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

type t_AppData = | AppData : t_Bytes -> t_AppData

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_24:Core.Marker.t_StructuralPartialEq t_AppData

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_25:Core.Cmp.t_PartialEq t_AppData t_AppData

/// Create new application data from raw bytes.
val impl_AppData__new (b: t_Bytes) : Prims.Pure t_AppData Prims.l_True (fun _ -> Prims.l_True)

/// Convert this application data into raw bytes
val impl_AppData__into_raw (self: t_AppData)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

/// Get a reference to the raw bytes.
val impl_AppData__as_raw (self: t_AppData) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_13:Core.Convert.t_From t_AppData (t_Slice u8)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_14 (v_N: usize) : Core.Convert.t_From t_AppData (t_Array u8 v_N)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_15:Core.Convert.t_From t_AppData (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_16:Core.Convert.t_From t_AppData t_Bytes

val random_bytes (len: usize) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)
