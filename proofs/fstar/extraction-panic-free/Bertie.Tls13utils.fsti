module Bertie.Tls13utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Error = | Error_UnknownCiphersuite : Alloc.String.t_String -> t_Error

unfold
let t_TLSError = u8

unfold
let t_U16 = u16

unfold
let t_U32 = u32

unfold
let t_U8 = u8

let v_APPLICATION_DATA_INSTEAD_OF_HANDSHAKE: u8 = 138uy

let v_CRYPTO_ERROR: u8 = 2uy

let v_DECODE_ERROR: u8 = 142uy

let v_GOT_HANDSHAKE_FAILURE_ALERT: u8 = 141uy

let v_INCORRECT_ARRAY_LENGTH: u8 = 4uy

let v_INCORRECT_STATE: u8 = 128uy

let v_INSUFFICIENT_DATA: u8 = 134uy

let v_INSUFFICIENT_ENTROPY: u8 = 3uy

let v_INVALID_COMPRESSION_LIST: u8 = 136uy

let v_INVALID_SIGNATURE: u8 = 140uy

let v_MISSING_KEY_SHARE: u8 = 139uy

let v_NEGOTIATION_MISMATCH: u8 = 132uy

let v_PARSE_FAILED: u8 = 133uy

let v_PAYLOAD_TOO_LONG: u8 = 130uy

let v_PROTOCOL_VERSION_ALERT: u8 = 137uy

let v_PSK_MODE_MISMATCH: u8 = 131uy

val v_U16 (x: u16) : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val v_U32 (x: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val v_U8 (x: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let v_UNSUPPORTED: u8 = 135uy

let v_UNSUPPORTED_ALGORITHM: u8 = 1uy

let v_ZERO_RTT_DISABLED: u8 = 129uy

val dummy_fn: Prims.unit -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val parse_failed: Prims.unit -> Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

class t_Declassify (v_Self: Type) (v_T: Type) = {
  f_declassify_pre:v_Self -> bool;
  f_declassify_post:v_Self -> v_T -> bool;
  f_declassify:x0: v_Self
    -> Prims.Pure v_T (f_declassify_pre x0) (fun result -> f_declassify_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Declassify u8 u8 =
  {
    f_declassify_pre = (fun (self: u8) -> true);
    f_declassify_post = (fun (self: u8) (out: u8) -> true);
    f_declassify = fun (self: u8) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: t_Declassify u32 u32 =
  {
    f_declassify_pre = (fun (self: u32) -> true);
    f_declassify_post = (fun (self: u32) (out: u32) -> true);
    f_declassify = fun (self: u32) -> self
  }

val eq1 (b1 b2: u8) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val u32_from_be_bytes (v_val: t_Array u8 (sz 4))
    : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val u16_as_be_bytes (v_val: u16)
    : Prims.Pure (t_Array u8 (sz 2)) Prims.l_True (fun _ -> Prims.l_True)

val u32_as_be_bytes (v_val: u32)
    : Prims.Pure (t_Array u8 (sz 4)) Prims.l_True (fun _ -> Prims.l_True)

val check (b: bool)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True
      (fun res -> match res with 
               | Core.Result.Result_Ok l -> b == true
               | _ -> True)


val check_eq1 (b1 b2: u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val length_u16_encoded_slice (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True
      (fun res -> match res with 
               | Core.Result.Result_Ok l -> v l + 2 <= Seq.length bytes
               | _ -> True)

val length_u16_encoded (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True
      (fun res -> match res with 
               | Core.Result.Result_Ok l -> v l <= 65536 /\ v l + 2 <= Seq.length bytes
               | _ -> True)


val length_u24_encoded (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result usize u8)
      Prims.l_True
      (fun res -> match res with 
               | Core.Result.Result_Ok l -> v l <= 16777216 /\ v l + 3 <= Seq.length bytes
               | _ -> True)

val length_u8_encoded (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result usize u8) Prims.l_True
      (fun res -> match res with 
               | Core.Result.Result_Ok l -> v l <= 256 /\ v l + 1 <= Seq.length bytes
               | _ -> True)


val check_length_encoding_u16_slice (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True
      (fun res -> match res with 
               | Core.Result.Result_Ok _ -> 
                 Seq.length bytes >= 2 /\
                 v (Seq.index bytes 0) * 256 + v (Seq.index bytes 1) + 2 == Seq.length bytes
               | _ -> True)

val check_length_encoding_u24 (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True
      (fun res -> match res with 
               | Core.Result.Result_Ok _ -> 
                 Seq.length bytes >= 3 /\
                 v (Seq.index bytes 0) * 65536 + v (Seq.index bytes 1) * 256 + v (Seq.index bytes 2) + 3 == Seq.length bytes
               | _ -> True)

val check_length_encoding_u8_slice (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True 
      (fun res -> match res with 
               | Core.Result.Result_Ok _ -> 
                 Seq.length bytes > 0 /\
                 v (Seq.index bytes 0) + 1 == Seq.length bytes
               | _ -> True)


val eq_slice (b1 b2: t_Slice u8) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val check_eq_slice (b1 b2: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val check_eq_with_slice (b1 b2: t_Slice u8) (start v_end: usize)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True
      (fun res -> match res with 
               | Core.Result.Result_Ok _ -> Seq.length b2 >= v v_end
               | _ -> True)

val check_mem (b1 b2: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val error_string (c: u8) : Prims.Pure Alloc.String.t_String Prims.l_True (fun _ -> Prims.l_True)

val tlserr (#v_T: Type) (err: u8)
    : Prims.Pure (Core.Result.t_Result v_T u8) Prims.l_True
      (fun res -> match res with 
               | Core.Result.Result_Ok _ -> False
               | Core.Result.Result_Err _ -> True)

type t_Bytes = | Bytes : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global -> t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From t_Bytes (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  {
    f_from_pre = (fun (x: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) -> true);
    f_from_post = (fun (x: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (out: t_Bytes) -> true);
    f_from = fun (x: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) -> Bytes x <: t_Bytes
  }

val impl__Bytes__as_raw (self: t_Bytes)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun res -> res == self._0)

val impl__Bytes__declassify (self: t_Bytes)
    : Prims.Pure (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Prims.l_True (fun _ -> Prims.l_True)

val impl__Bytes__into_raw (self: t_Bytes)
    : Prims.Pure (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Prims.l_True (fun _ -> Prims.l_True)

val impl__Bytes__declassify_array (v_C: usize) (self: t_Bytes)
    : Prims.Pure (Core.Result.t_Result (t_Array u8 v_C) u8) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Convert.t_From t_Bytes (t_Slice u8) =
  {
    f_from_pre = (fun (x: t_Slice u8) -> true);
    f_from_post = (fun (x: t_Slice u8) (out: t_Bytes) -> true);
    f_from
    =
    fun (x: t_Slice u8) ->
      Core.Convert.f_into (Alloc.Slice.impl__to_vec x <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (v_C: usize) : Core.Convert.t_From t_Bytes (t_Array u8 v_C) =
  {
    f_from_pre = (fun (x: t_Array u8 v_C) -> true);
    f_from_post = (fun (x: t_Array u8 v_C) (out: t_Bytes) -> true);
    f_from
    =
    fun (x: t_Array u8 v_C) ->
      Core.Convert.f_into (Alloc.Slice.impl__to_vec (Rust_primitives.unsize x <: t_Slice u8)
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7 (v_C: usize) : Core.Convert.t_From t_Bytes (t_Array u8 v_C) =
  {
    f_from_pre = (fun (x: t_Array u8 v_C) -> true);
    f_from_post = (fun (x: t_Array u8 v_C) (out: t_Bytes) -> true);
    f_from
    =
    fun (x: t_Array u8 v_C) ->
      Core.Convert.f_into (Alloc.Slice.impl__to_vec (Rust_primitives.unsize x <: t_Slice u8)
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

val impl__Bytes__append (self x: t_Bytes) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

let impl__Bytes__concat self (other:t_Bytes{Seq.length self._0 + Seq.length other._0 <= max_usize}) = Bytes (concat self._0 other._0)


val impl__Bytes__concat_array (v_N: usize) (self: t_Bytes{Seq.length self._0 + v v_N <= max_usize}) (other: t_Array u8 v_N)
    : Prims.Pure t_Bytes Prims.l_True
      (fun res -> Seq.length res._0 == Seq.length self._0 + v v_N)

val impl__Bytes__extend_from_slice (self x: t_Bytes)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val impl__Bytes__from_hex (s: string) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val impl__Bytes__from_slice (s: t_Slice u8)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

let impl__Bytes__len (self: t_Bytes) = Alloc.Vec.impl_1__len self._0 <: usize

let impl__Bytes__prefix (self: t_Bytes) (prefix: t_Slice u8{Seq.length self._0 + Seq.length prefix <= max_usize}) = 
  Bytes (concat prefix self._0)

val impl__Bytes__new: Prims.unit -> Prims.Pure t_Bytes Prims.l_True (fun res -> Seq.length res._0 == 0)

val impl__Bytes__new_alloc (len: usize) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val impl__Bytes__push (self: t_Bytes) (x: u8)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

let impl__Bytes__raw_slice (self: t_Bytes) (range: Core.Ops.Range.t_Range usize{Core.Ops.Index.f_index_pre self._0 range}) =
    self._0.[ range ] 

val impl__Bytes__slice (self: t_Bytes) (start len: usize)
    : Prims.Pure t_Bytes (v start + v len <= Seq.length self._0)
      (fun res -> Seq.length res._0 == v len)

val impl__Bytes__slice_range (self: t_Bytes) (range: Core.Ops.Range.t_Range usize{Core.Ops.Index.f_index_pre self._0 range})
    : Prims.Pure t_Bytes Prims.l_True 
      (fun res -> res == Bytes (self._0.[ range ]))

val impl__Bytes__zeroes (len: usize) : Prims.Pure t_Bytes Prims.l_True 
    (fun res -> Seq.length res._0 == v len)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Ops.Index.t_Index t_Bytes usize =
  {
    f_Output = u8;
    f_index_pre = (fun (self: t_Bytes) (x: usize) -> x <. (Alloc.Vec.impl_1__len self._0 <: usize));
    f_index_post = (fun (self: t_Bytes) (x: usize) (out: u8) -> true);
    f_index = fun (self: t_Bytes) (x: usize) -> self._0.[ x ]
    }

val impl__Bytes__update_slice (self: t_Bytes) (start: usize) (other: t_Bytes) (beg len: usize)
    : Prims.Pure t_Bytes
      (v start + v len <= Seq.length self._0 /\ v beg + v len <= Seq.length other._0)
      (fun res -> Seq.length res._0 == Seq.length self._0)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Ops.Index.t_Index t_Bytes (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index_pre
    =
    (fun (self: t_Bytes) (x: Core.Ops.Range.t_Range usize) ->
        x.Core.Ops.Range.f_start <=. (Alloc.Vec.impl_1__len self._0 <: usize) &&
        x.Core.Ops.Range.f_end <=. (Alloc.Vec.impl_1__len self._0 <: usize));
    f_index_post = (fun (self: t_Bytes) (x: Core.Ops.Range.t_Range usize) (out: t_Slice u8) -> true);
    f_index = fun (self: t_Bytes) (x: Core.Ops.Range.t_Range usize) -> self._0.[ x ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let upd_22: Rust_primitives.Hax.update_at_tc t_Bytes usize =
  {
    super_index = impl_21;
    update_at = fun s (i:usize{v i < Seq.length s._0}) x -> Bytes (Seq.upd s._0 (v i) x)
  } 


val bytes (x: t_Slice u8) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val bytes1 (x: u8) : Prims.Pure t_Bytes Prims.l_True (fun res -> Seq.length res._0 == 1)

val bytes2 (x y: u8) : Prims.Pure t_Bytes Prims.l_True (fun res -> Seq.length res._0 == 2)

val check_eq (b1 b2: t_Bytes)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True (fun _ -> Prims.l_True)

val check_length_encoding_u16 (bytes: t_Bytes)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True
      (fun res -> match res with 
               | Core.Result.Result_Ok _ -> Seq.length bytes._0 >= 2
               | _ -> True)


val check_length_encoding_u8 (bytes: t_Bytes)
    : Prims.Pure (Core.Result.t_Result Prims.unit u8) Prims.l_True
      (fun res -> match res with 
               | Core.Result.Result_Ok _ -> Seq.length bytes._0 >= 1
               | _ -> True)

val encode_length_u16 (bytes: t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_Bytes u8) 
      Prims.l_True 
      (fun res -> match res with 
               | Core.Result.Result_Ok b -> Seq.length bytes._0 < 65536 /\ Seq.length b._0 == Seq.length bytes._0 + 2
               | _ -> True)

val encode_length_u24 (bytes: t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_Bytes u8) Prims.l_True
      (fun res -> match res with 
               | Core.Result.Result_Ok b -> Seq.length bytes._0 < 16777216 /\ Seq.length b._0 == Seq.length bytes._0 + 3
               | _ -> True)

val encode_length_u8 (bytes: t_Slice u8)
    : Prims.Pure (Core.Result.t_Result t_Bytes u8) Prims.l_True
      (fun res -> match res with 
               | Core.Result.Result_Ok b -> Seq.length bytes < 256 /\ Seq.length b._0 == Seq.length bytes + 1
               | _ -> True)

val eq (b1 b2: t_Bytes) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val random_bytes (len: usize) : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

type t_AppData = | AppData : t_Bytes -> t_AppData

val impl__AppData__as_raw (self: t_AppData)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val impl__AppData__into_raw (self: t_AppData)
    : Prims.Pure t_Bytes Prims.l_True (fun _ -> Prims.l_True)

val impl__AppData__new (b: t_Bytes) : Prims.Pure t_AppData Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Convert.t_From t_AppData (t_Slice u8) =
  {
    f_from_pre = (fun (value: t_Slice u8) -> true);
    f_from_post = (fun (value: t_Slice u8) (out: t_AppData) -> true);
    f_from = fun (value: t_Slice u8) -> AppData (Core.Convert.f_into value) <: t_AppData
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11 (v_N: usize) : Core.Convert.t_From t_AppData (t_Array u8 v_N) =
  {
    f_from_pre = (fun (value: t_Array u8 v_N) -> true);
    f_from_post = (fun (value: t_Array u8 v_N) (out: t_AppData) -> true);
    f_from = fun (value: t_Array u8 v_N) -> AppData (Core.Convert.f_into value) <: t_AppData
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Convert.t_From t_AppData (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  {
    f_from_pre = (fun (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) -> true);
    f_from_post = (fun (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (out: t_AppData) -> true);
    f_from
    =
    fun (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) ->
      AppData (Core.Convert.f_into value) <: t_AppData
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Convert.t_From t_AppData t_Bytes =
  {
    f_from_pre = (fun (value: t_Bytes) -> true);
    f_from_post = (fun (value: t_Bytes) (out: t_AppData) -> true);
    f_from = fun (value: t_Bytes) -> AppData value <: t_AppData
  }
