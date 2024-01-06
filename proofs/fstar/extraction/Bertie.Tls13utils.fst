module Bertie.Tls13utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Error = | Error_UnknownCiphersuite : Alloc.String.t_String -> t_Error

unfold
let t_TLSError = u8

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

let v_UNSUPPORTED: u8 = 135uy

let v_UNSUPPORTED_ALGORITHM: u8 = 1uy

let v_ZERO_RTT_DISABLED: u8 = 129uy

let parse_failed (_: Prims.unit) : u8 = v_PARSE_FAILED

let check (b: bool) : Core.Result.t_Result Prims.unit u8 =
  if b
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8

let error_string (c: u8) : Alloc.String.t_String =
  Alloc.Fmt.format (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize (let list = [""] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list list)
          <:
          t_Slice string)
        (Rust_primitives.unsize (let list =
                [Core.Fmt.Rt.impl_1__new_display c <: Core.Fmt.Rt.t_Argument]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list list)
          <:
          t_Slice Core.Fmt.Rt.t_Argument)
      <:
      Core.Fmt.t_Arguments)

let tlserr
      (#v_T: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Marker.t_Sized v_T)
      (err: u8)
    : Core.Result.t_Result v_T u8 =
  let bt:Backtrace.Capture.t_Backtrace = Backtrace.Capture.impl__Backtrace__new () in
  let _:Prims.unit =
    Std.Io.Stdio.v__print (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize (let list = [""; "\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list list)
            <:
            t_Slice string)
          (Rust_primitives.unsize (let list =
                  [Core.Fmt.Rt.impl_1__new_debug bt <: Core.Fmt.Rt.t_Argument]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list list)
            <:
            t_Slice Core.Fmt.Rt.t_Argument)
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  Core.Result.Result_Err err <: Core.Result.t_Result v_T u8

type t_U16 = | U16 : u16 -> t_U16

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Convert.t_From t_U16 u16 = { f_from = fun (x: u16) -> U16 x <: t_U16 }

let impl__U16__declassify (self: t_U16) : u16 = self._0

type t_U32 = | U32 : u32 -> t_U32

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Convert.t_From t_U32 u32 = { f_from = fun (x: u32) -> U32 x <: t_U32 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Ops.Arith.t_Add t_U32 t_U32 =
  { f_Output = t_U32; f_add = fun (self: t_U32) (y: t_U32) -> U32 (self._0 +! y._0) <: t_U32 }

let impl__U32__declassify (self: t_U32) : u32 = self._0

type t_U8 = | U8 : u8 -> t_U8

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Ops.Bit.t_BitXor t_U8 t_U8 =
  { f_Output = t_U8; f_bitxor = fun (self: t_U8) (rhs: t_U8) -> U8 (self._0 ^. rhs._0) <: t_U8 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From t_U8 u8 = { f_from = fun (x: u8) -> U8 x <: t_U8 }

let impl__U8__declassify (self: t_U8) : u8 = self._0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_From t_U8 u8 = { f_from = fun (x: u8) -> U8 x <: t_U8 }

let eq1 (b1 b2: t_U8) : bool = (impl__U8__declassify b1 <: u8) =. (impl__U8__declassify b2 <: u8)

let check_eq1 (b1 b2: t_U8) : Core.Result.t_Result Prims.unit u8 =
  if eq1 b1 b2
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8

type t_Bytes = | Bytes : Alloc.Vec.t_Vec t_U8 Alloc.Alloc.t_Global -> t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Convert.t_From t_Bytes (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  {
    f_from
    =
    fun (x: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) ->
      Bytes
      (Core.Iter.Traits.Iterator.f_collect (Core.Iter.Traits.Iterator.f_map (Core.Slice.impl__iter (Core.Ops.Deref.f_deref
                      x
                    <:
                    t_Slice u8)
                <:
                Core.Slice.Iter.t_Iter u8)
              (fun x ->
                  let x:u8 = x in
                  Core.Convert.f_into x <: t_U8)
            <:
            Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> t_U8)))
      <:
      t_Bytes
  }

let impl__Bytes__as_raw (self: t_Bytes) : t_Slice t_U8 = Core.Ops.Deref.f_deref self._0

let impl__Bytes__declassify (self: t_Bytes) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Core.Iter.Traits.Iterator.f_collect (Core.Iter.Traits.Iterator.f_map (Core.Slice.impl__iter (Core.Ops.Deref.f_deref
                self._0
              <:
              t_Slice t_U8)
          <:
          Core.Slice.Iter.t_Iter t_U8)
        (fun x ->
            let x:t_U8 = x in
            impl__U8__declassify x <: u8)
      <:
      Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter t_U8) (t_U8 -> u8))

let impl__Bytes__into_raw (self: t_Bytes) : Alloc.Vec.t_Vec t_U8 Alloc.Alloc.t_Global = self._0

let impl__Bytes__declassify_array (self: t_Bytes) : Core.Result.t_Result (t_Array u8 v_C) u8 =
  Core.Result.impl__map_err (Core.Convert.f_try_into (impl__Bytes__declassify self
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      <:
      Core.Result.t_Result (t_Array u8 v_C) (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
    (fun temp_0_ ->
        let _:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = temp_0_ in
        v_INCORRECT_ARRAY_LENGTH)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Convert.t_From t_Bytes (t_Slice u8) =
  {
    f_from
    =
    fun (x: t_Slice u8) ->
      Core.Convert.f_into (Alloc.Slice.impl__to_vec x <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Convert.t_From t_Bytes (t_Slice t_U8) =
  { f_from = fun (x: t_Slice t_U8) -> Bytes (Alloc.Slice.impl__to_vec x) <: t_Bytes }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12 (v_C: usize) : Core.Convert.t_From t_Bytes (t_Array u8 v_C) =
  {
    f_from
    =
    fun (x: t_Array u8 v_C) ->
      Core.Convert.f_into (Alloc.Slice.impl__to_vec (Rust_primitives.unsize x <: t_Slice u8)
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13 (v_C: usize) : Core.Convert.t_From t_Bytes (t_Array u8 v_C) =
  {
    f_from
    =
    fun (x: t_Array u8 v_C) ->
      Core.Convert.f_into (Alloc.Slice.impl__to_vec (Rust_primitives.unsize x <: t_Slice u8)
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

let impl__U32__as_be_bytes (self: t_U32) : t_Bytes =
  Core.Convert.f_into (Alloc.Slice.impl__to_vec (Rust_primitives.unsize (Core.Num.impl__u32__to_be_bytes
                self._0
              <:
              t_Array u8 (sz 4))
          <:
          t_Slice u8)
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let impl__U32__from_be_bytes (x: t_Bytes) : Core.Result.t_Result t_U32 u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist17:t_Array u8 (sz 4) =
        match
          Core.Ops.Try_trait.f_branch (impl__Bytes__declassify_array (sz 4) x
              <:
              Core.Result.t_Result (t_Array u8 (sz 4)) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist16:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_U32 u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist16)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_U32 u8) (t_Array u8 (sz 4))
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_U32 u8) (t_Array u8 (sz 4))
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist18:u32 = Core.Num.impl__u32__from_be_bytes hoist17 in
        let hoist19:t_U32 = U32 hoist18 <: t_U32 in
        Core.Result.Result_Ok hoist19 <: Core.Result.t_Result t_U32 u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_U32 u8)
        (Core.Result.t_Result t_U32 u8))

let impl__U16__as_be_bytes (self: t_U16) : t_Bytes =
  Core.Convert.f_into (Alloc.Slice.impl__to_vec (Rust_primitives.unsize (Core.Num.impl__u16__to_be_bytes
                self._0
              <:
              t_Array u8 (sz 2))
          <:
          t_Slice u8)
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let impl__U16__from_be_bytes (x: t_Bytes) : Core.Result.t_Result t_U16 u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist21:t_Array u8 (sz 2) =
        match
          Core.Ops.Try_trait.f_branch (impl__Bytes__declassify_array (sz 2) x
              <:
              Core.Result.t_Result (t_Array u8 (sz 2)) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist20:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_U16 u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist20)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_U16 u8) (t_Array u8 (sz 2))
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_U16 u8) (t_Array u8 (sz 2))
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist22:u16 = Core.Num.impl__u16__from_be_bytes hoist21 in
        let hoist23:t_U16 = U16 hoist22 <: t_U16 in
        Core.Result.Result_Ok hoist23 <: Core.Result.t_Result t_U16 u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_U16 u8)
        (Core.Result.t_Result t_U16 u8))

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Ops.Index.t_Index t_Bytes usize =
  { f_Output = t_U8; f_index = fun (self: t_Bytes) (x: usize) -> self._0.[ x ] }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Ops.Index.t_Index t_Bytes (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice t_U8;
    f_index = fun (self: t_Bytes) (x: Core.Ops.Range.t_Range usize) -> self._0.[ x ]
  }

let impl__Bytes__as_hex (self: t_Bytes) : Alloc.String.t_String =
  let (strs: Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
    Alloc.String.t_String Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.f_collect (Core.Iter.Traits.Iterator.f_map (Core.Slice.impl__iter (Core.Ops.Deref.f_deref
                  self._0
                <:
                t_Slice t_U8)
            <:
            Core.Slice.Iter.t_Iter t_U8)
          (fun b ->
              let b:t_U8 = b in
              Alloc.Fmt.format (Core.Fmt.impl_2__new_v1_formatted (Rust_primitives.unsize (let list
                          =
                            [""]
                          in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list list)
                      <:
                      t_Slice string)
                    (Rust_primitives.unsize (let list =
                            [
                              Core.Fmt.Rt.impl_1__new_lower_hex (impl__U8__declassify b <: u8)
                              <:
                              Core.Fmt.Rt.t_Argument
                            ]
                          in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list list)
                      <:
                      t_Slice Core.Fmt.Rt.t_Argument)
                    (Rust_primitives.unsize (let list =
                            [
                              Core.Fmt.Rt.impl__Placeholder__new (sz 0)
                                ' '
                                (Core.Fmt.Rt.Alignment_Unknown <: Core.Fmt.Rt.t_Alignment)
                                8ul
                                (Core.Fmt.Rt.Count_Implied <: Core.Fmt.Rt.t_Count)
                                (Core.Fmt.Rt.Count.v_Is (sz 2) <: Core.Fmt.Rt.t_Count)
                              <:
                              Core.Fmt.Rt.t_Placeholder
                            ]
                          in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list list)
                      <:
                      t_Slice Core.Fmt.Rt.t_Placeholder)
                    (Rust_primitives.Hax.failure ""
                        "{ Types.attributes = [];\n  contents =\n  Types.Block {\n    expr =\n    (Some { Types.attributes = [];\n            contents =\n            Types.Call {args = [];\n              fn_span =\n              { Types.filename =\n                (Types.Real\n                   Types.Remapped {\n                     local_path =\n                     (Some \"/Users/franziskus/.rustup/toolchains/nightly-2023-06-02-aarch64-apple-darwin/lib/rustlib/src/rust/library/alloc/src/macros.rs\");\n                     virtual_name =\n                     \"/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/macros.rs\"});\n                hi = { Types.col = \"78\"; line = \"120\" };\n                lo = { Types.col = \"38\"; line = \"120\" } };\n              from_hir_call = true;\n              fun' =\n              { Types.attributes = [];\n                contents =\n                Types.GlobalName {\n                  id =\n                  { Types.index = (2, 9101); krate = \"core\";\n                    path =\n                    [{ Types.data = (Types.TypeNs \"fmt\"); disambiguator = 0 };\n                      { Types.data = (Types.TypeNs \"rt\"); disambiguator = 0 };\n                      { Types.data = Types.Impl; disambiguator = 2 };\n                      { Types.data = (Types.ValueNs \"new\"); disambiguator = 0\n                        }\n                      ]\n                    }};\n                hir_id = None;\n                span =\n                { Types.filename =\n                  (Types.Real\n                     Types.Remapped {\n                       local_path =\n                       (Some \"/Users/franziskus/.rustup/toolchains/nightly-2023-06-02-aarch64-apple-darwin/lib/rustlib/src/rust/library/alloc/src/macros.rs\");\n                       virtual_name =\n                       \"/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/macros.rs\"});\n                  hi = { Types.col = \"78\"; line = \"120\" };\n                  lo = { Types.col = \"38\"; line = \"120\" } };\n                ty =\n                (Types.Arrow\n                   { Types.bound_vars = [];\n                     value =\n                     { Types.abi = Types.Abi {todo = \"Rust\"};\n                       c_variadic = false; inputs = [];\n                       output =\n                       Types.Adt {\n                         def_id =\n                         { Types.index = (2, 9098); krate = \"core\";\n                           path =\n                           [{ Types.data = (Types.TypeNs \"fmt\");\n                              disambiguator = 0 };\n                             { Types.data = (Types.TypeNs \"rt\");\n                               disambiguator = 0 };\n                             { Types.data = (Types.TypeNs \"UnsafeArg\");\n                               disambiguator = 0 }\n                             ]\n                           };\n                         generic_args = []};\n                       unsafety = Types.Unsafe }\n                     })\n                };\n              generic_args = []; impl = None;\n              ty =\n              (Types.Arrow\n                 { Types.bound_vars = [];\n                   value =\n                   { Types.abi = Types.Abi {todo = \"Rust\"};\n                     c_variadic = false; inputs = [];\n                     output =\n                     Types.Adt {\n                       def_id =\n                       { Types.index = (2, 9098); krate = \"core\";\n                         path =\n                         [{ Types.data = (Types.TypeNs \"fmt\");\n                            disambiguator = 0 };\n                           { Types.data = (Types.TypeNs \"rt\");\n                             disambiguator = 0 };\n                           { Types.data = (Types.TypeNs \"UnsafeArg\");\n                             disambiguator = 0 }\n                           ]\n                         };\n                       generic_args = []};\n                     unsafety = Types.Unsafe }\n                   })};\n            hir_id = (Some (\"697\", \"68\"));\n            span =\n            { Types.filename =\n              (Types.Real\n                 Types.Remapped {\n                   local_path =\n                   (Some \"/Users/franziskus/.rustup/toolchains/nightly-2023-06-02-aarch64-apple-darwin/lib/rustlib/src/rust/library/alloc/src/macros.rs\");\n                   virtual_name =\n                   \"/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/macros.rs\"});\n              hi = { Types.col = \"78\"; line = \"120\" };\n              lo = { Types.col = \"38\"; line = \"120\" } };\n            ty =\n            Types.Adt {\n              def_id =\n              { Types.index = (2, 9098); krate = \"core\";\n                path =\n                [{ Types.data = (Types.TypeNs \"fmt\"); disambiguator = 0 };\n                  { Types.data = (Types.TypeNs \"rt\"); disambiguator = 0 };\n                  { Types.data = (Types.TypeNs \"UnsafeArg\");\n                    disambiguator = 0 }\n                  ]\n                };\n              generic_args = []}\n            });\n    opt_destruction_scope = None;\n    region_scope = { Types.data = Types.Node; id = \"69\" };\n    safety_mode = Types.BuiltinUnsafe;\n    span =\n    { Types.filename =\n      (Types.Real\n         Types.Remapped {\n           local_path =\n           (Some \"/Users/franziskus/.rustup/toolchains/nightly-2023-06-02-aarch64-apple-darwin/lib/rustlib/src/rust/library/alloc/src/macros.rs\");\n           virtual_name =\n           \"/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/macros.rs\"});\n      hi = { Types.col = \"78\"; line = \"120\" };\n      lo = { Types.col = \"38\"; line = \"120\" } };\n    stmts = []; targeted_by_break = false};\n  hir_id = (Some (\"697\", \"70\"));\n  span =\n  { Types.filename =\n    (Types.Real\n       Types.Remapped {\n         local_path =\n         (Some \"/Users/franziskus/.rustup/toolchains/nightly-2023-06-02-aarch64-apple-darwin/lib/rustlib/src/rust/library/alloc/src/macros.rs\");\n         virtual_name =\n         \"/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/macros.rs\"});\n    hi = { Types.col = \"78\"; line = \"120\" };\n    lo = { Types.col = \"38\"; line = \"120\" } };\n  ty =\n  Types.Adt {\n    def_id =\n    { Types.index = (2, 9098); krate = \"core\";\n      path =\n      [{ Types.data = (Types.TypeNs \"fmt\"); disambiguator = 0 };\n        { Types.data = (Types.TypeNs \"rt\"); disambiguator = 0 };\n        { Types.data = (Types.TypeNs \"UnsafeArg\"); disambiguator = 0 }]\n      };\n    generic_args = []}\n  }"

                      <:
                      Core.Fmt.Rt.t_UnsafeArg)
                  <:
                  Core.Fmt.t_Arguments)
              <:
              Alloc.String.t_String)
        <:
        Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter t_U8) (t_U8 -> Alloc.String.t_String))
  in
  Alloc.Slice.impl__join (Core.Ops.Deref.f_deref strs <: t_Slice Alloc.String.t_String) ""

let impl__Bytes__concat (self other: t_Bytes) : t_Bytes =
  let res:Alloc.Vec.t_Vec t_U8 Alloc.Alloc.t_Global = Alloc.Vec.impl__new () in
  let res:Alloc.Vec.t_Vec t_U8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice res (Core.Ops.Deref.f_deref self._0 <: t_Slice t_U8)
  in
  let res:Alloc.Vec.t_Vec t_U8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice res (Core.Ops.Deref.f_deref other._0 <: t_Slice t_U8)
  in
  Bytes res <: t_Bytes

let impl__Bytes__extend_from_slice (self x: t_Bytes) : t_Bytes =
  let hax_temp_output, self:(Prims.unit & t_Bytes) =
    (),
    ({
        self with
        _0
        =
        Alloc.Vec.impl_2__extend_from_slice self._0 (Core.Ops.Deref.f_deref x._0 <: t_Slice t_U8)
      }
      <:
      t_Bytes)
    <:
    (Prims.unit & t_Bytes)
  in
  self

let impl__Bytes__from_hex (s: string) : t_Bytes =
  let (s: Alloc.String.t_String):Alloc.String.t_String =
    Core.Iter.Traits.Iterator.f_collect (Core.Str.impl__str__split_whitespace s
        <:
        Core.Str.Iter.t_SplitWhitespace)
  in
  if ((Alloc.String.impl__String__len s <: usize) %! sz 2 <: usize) =. sz 0
  then
    Bytes
    (Core.Option.impl__expect (Core.Iter.Traits.Iterator.f_collect (Core.Iter.Traits.Iterator.f_map (
                  Core.Iter.Traits.Iterator.f_step_by ({
                        Core.Ops.Range.f_start = sz 0;
                        Core.Ops.Range.f_end = Alloc.String.impl__String__len s <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                    (sz 2)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
                (fun i ->
                    let i:usize = i in
                    Core.Option.impl__and_then (Core.Str.impl__str__get (Core.Ops.Deref.f_deref s
                            <:
                            string)
                          ({ Core.Ops.Range.f_start = i; Core.Ops.Range.f_end = i +! sz 2 <: usize }
                            <:
                            Core.Ops.Range.t_Range usize)
                        <:
                        Core.Option.t_Option string)
                      (fun sub ->
                          let sub:string = sub in
                          Core.Option.impl__map (Core.Result.impl__ok (Core.Num.impl__u8__from_str_radix
                                    sub
                                    16ul
                                  <:
                                  Core.Result.t_Result u8 Core.Num.Error.t_ParseIntError)
                              <:
                              Core.Option.t_Option u8)
                            v_U8
                          <:
                          Core.Option.t_Option t_U8)
                    <:
                    Core.Option.t_Option t_U8)
              <:
              Core.Iter.Adapters.Map.t_Map
                (Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
                (usize -> Core.Option.t_Option t_U8))
          <:
          Core.Option.t_Option (Alloc.Vec.t_Vec t_U8 Alloc.Alloc.t_Global))
        "Not a hex string1")
    <:
    t_Bytes
  else
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize
                  (let list = ["internal error: entered unreachable code: Not a hex string2"] in
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

let impl__Bytes__from_slice (s: t_Slice u8) : t_Bytes = Core.Convert.f_into s

let impl__Bytes__is_empty (self: t_Bytes) : bool = Alloc.Vec.impl_1__is_empty self._0

let impl__Bytes__len (self: t_Bytes) : usize = Alloc.Vec.impl_1__len self._0

let impl__Bytes__new (_: Prims.unit) : t_Bytes = Bytes (Alloc.Vec.impl__new ()) <: t_Bytes

let impl__Bytes__push (self: t_Bytes) (x: t_U8) : t_Bytes =
  let hax_temp_output, self:(Prims.unit & t_Bytes) =
    (), ({ self with _0 = Alloc.Vec.impl_1__push self._0 x } <: t_Bytes) <: (Prims.unit & t_Bytes)
  in
  self

let impl__Bytes__slice (self: t_Bytes) (start len: usize) : t_Bytes =
  Core.Convert.f_into (self._0.[ {
          Core.Ops.Range.f_start = start;
          Core.Ops.Range.f_end = start +! len <: usize
        }
        <:
        Core.Ops.Range.t_Range usize ]
      <:
      t_Slice t_U8)

let impl__Bytes__slice_range (self: t_Bytes) (range: Core.Ops.Range.t_Range usize) : t_Bytes =
  Core.Convert.f_into (self._0.[ range ] <: t_Slice t_U8)

let impl__Bytes__update_slice (self: t_Bytes) (start: usize) (other: t_Bytes) (beg len: usize)
    : t_Bytes =
  let res:t_Bytes = Core.Clone.f_clone self in
  let res:t_Bytes =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = len
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      res
      (fun res i ->
          let res:t_Bytes = res in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
            (start +! i <: usize)
            (other.[ beg +! i <: usize ] <: t_U8)
          <:
          t_Bytes)
  in
  res

let impl__Bytes__with_capacity (len: usize) : t_Bytes =
  Bytes (Alloc.Vec.impl__with_capacity len) <: t_Bytes

let impl__Bytes__zeroes (len: usize) : t_Bytes =
  Bytes (Alloc.Vec.from_elem (U8 0uy <: t_U8) len) <: t_Bytes

let bytes (x: t_Slice u8) : t_Bytes = Core.Convert.f_into x

let bytes1 (x: u8) : t_Bytes =
  Core.Convert.f_into (let list = [x] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list list)

let bytes2 (x y: u8) : t_Bytes =
  Core.Convert.f_into (let list = [x; y] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
      Rust_primitives.Hax.array_of_list list)

let encode_length_u16 (bytes: t_Bytes) : Core.Result.t_Result t_Bytes u8 =
  let len:usize = impl__Bytes__len bytes in
  if len >=. sz 65536
  then Core.Result.Result_Err v_PAYLOAD_TOO_LONG <: Core.Result.t_Result t_Bytes u8
  else
    let len:t_Bytes = impl__U16__as_be_bytes (U16 (cast (len <: usize) <: u16) <: t_U16) in
    let lenb:t_Bytes = impl__Bytes__new () in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 0 ] <: t_U8) in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 1 ] <: t_U8) in
    let lenb:t_Bytes = impl__Bytes__extend_from_slice lenb bytes in
    Core.Result.Result_Ok lenb <: Core.Result.t_Result t_Bytes u8

let encode_length_u24 (bytes: t_Bytes) : Core.Result.t_Result t_Bytes u8 =
  let len:usize = impl__Bytes__len bytes in
  if len >=. sz 16777216
  then Core.Result.Result_Err v_PAYLOAD_TOO_LONG <: Core.Result.t_Result t_Bytes u8
  else
    let len:t_Bytes = impl__U32__as_be_bytes (U32 (cast (len <: usize) <: u32) <: t_U32) in
    let lenb:t_Bytes = impl__Bytes__new () in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 1 ] <: t_U8) in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 2 ] <: t_U8) in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 3 ] <: t_U8) in
    let lenb:t_Bytes = impl__Bytes__extend_from_slice lenb bytes in
    Core.Result.Result_Ok lenb <: Core.Result.t_Result t_Bytes u8

let encode_length_u8 (bytes: t_Bytes) : Core.Result.t_Result t_Bytes u8 =
  let len:usize = impl__Bytes__len bytes in
  if len >=. sz 256
  then Core.Result.Result_Err v_PAYLOAD_TOO_LONG <: Core.Result.t_Result t_Bytes u8
  else
    let lenb:t_Bytes = impl__Bytes__new () in
    let lenb:t_Bytes =
      impl__Bytes__push lenb (Core.Convert.f_into (cast (len <: usize) <: u8) <: t_U8)
    in
    let lenb:t_Bytes = impl__Bytes__extend_from_slice lenb bytes in
    Core.Result.Result_Ok lenb <: Core.Result.t_Result t_Bytes u8

let eq (b1 b2: t_Bytes) : bool =
  if (impl__Bytes__len b1 <: usize) <>. (impl__Bytes__len b2 <: usize)
  then false
  else
    let (b: bool):bool = true in
    let b:bool =
      Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = impl__Bytes__len b1 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Core.Ops.Range.t_Range usize)
        b
        (fun b i ->
            let b:bool = b in
            let i:usize = i in
            if ~.(eq1 (b1.[ i ] <: t_U8) (b2.[ i ] <: t_U8) <: bool) <: bool
            then
              let b:bool = false in
              b
            else b)
    in
    b

let check_eq (b1 b2: t_Bytes) : Core.Result.t_Result Prims.unit u8 =
  let b:bool = eq b1 b2 in
  if b
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8

let check_mem (b1 b2: t_Bytes) : Core.Result.t_Result Prims.unit u8 =
  if ((impl__Bytes__len b2 <: usize) %! (impl__Bytes__len b1 <: usize) <: usize) <>. sz 0
  then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8
  else
    let b:bool = false in
    let b:bool =
      Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end
                =
                (impl__Bytes__len b2 <: usize) /! (impl__Bytes__len b1 <: usize) <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Core.Ops.Range.t_Range usize)
        b
        (fun b i ->
            let b:bool = b in
            let i:usize = i in
            if
              eq b1
                (impl__Bytes__slice_range b2
                    ({
                        Core.Ops.Range.f_start = i *! (impl__Bytes__len b1 <: usize) <: usize;
                        Core.Ops.Range.f_end
                        =
                        (i +! sz 1 <: usize) *! (impl__Bytes__len b1 <: usize) <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  t_Bytes)
              <:
              bool
            then
              let b:bool = true in
              b
            else b)
    in
    if b
    then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
    else Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8

let length_u16_encoded (bytes: t_Bytes) : Core.Result.t_Result usize u8 =
  if (impl__Bytes__len bytes <: usize) <. sz 2
  then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
  else
    let l0:usize = cast (impl__U8__declassify (bytes.[ sz 0 ] <: t_U8) <: u8) <: usize in
    let l1:usize = cast (impl__U8__declassify (bytes.[ sz 1 ] <: t_U8) <: u8) <: usize in
    let l:usize = (l0 *! sz 256 <: usize) +! l1 in
    if ((impl__Bytes__len bytes <: usize) -! sz 2 <: usize) <. l
    then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
    else Core.Result.Result_Ok l <: Core.Result.t_Result usize u8

let check_length_encoding_u16 (bytes: t_Bytes) : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist211:usize =
        match
          Core.Ops.Try_trait.f_branch (length_u16_encoded bytes <: Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist210:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist210)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) usize
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist212:usize = hoist211 +! sz 2 in
        let hoist213:bool = hoist212 <>. (impl__Bytes__len bytes <: usize) in
        if hoist213
        then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8
        else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

let length_u24_encoded (bytes: t_Bytes) : Core.Result.t_Result usize u8 =
  if (impl__Bytes__len bytes <: usize) <. sz 3
  then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
  else
    let l0:usize = cast (impl__U8__declassify (bytes.[ sz 0 ] <: t_U8) <: u8) <: usize in
    let l1:usize = cast (impl__U8__declassify (bytes.[ sz 1 ] <: t_U8) <: u8) <: usize in
    let l2:usize = cast (impl__U8__declassify (bytes.[ sz 2 ] <: t_U8) <: u8) <: usize in
    let l:usize = ((l0 *! sz 65536 <: usize) +! (l1 *! sz 256 <: usize) <: usize) +! l2 in
    if ((impl__Bytes__len bytes <: usize) -! sz 3 <: usize) <. l
    then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
    else Core.Result.Result_Ok l <: Core.Result.t_Result usize u8

let check_length_encoding_u24 (bytes: t_Bytes) : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist234:usize =
        match
          Core.Ops.Try_trait.f_branch (length_u24_encoded bytes <: Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist233:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist233)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) usize
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist235:usize = hoist234 +! sz 3 in
        let hoist236:bool = hoist235 <>. (impl__Bytes__len bytes <: usize) in
        if hoist236
        then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8
        else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

let length_u8_encoded (bytes: t_Bytes) : Core.Result.t_Result usize u8 =
  if impl__Bytes__is_empty bytes
  then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
  else
    let l:usize = cast (impl__U8__declassify (bytes.[ sz 0 ] <: t_U8) <: u8) <: usize in
    if ((impl__Bytes__len bytes <: usize) -! sz 1 <: usize) <. l
    then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
    else Core.Result.Result_Ok l <: Core.Result.t_Result usize u8

let check_length_encoding_u8 (bytes: t_Bytes) : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist238:usize =
        match
          Core.Ops.Try_trait.f_branch (length_u8_encoded bytes <: Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist237:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist237)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) usize
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) usize
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist239:usize = hoist238 +! sz 1 in
        let hoist240:bool = hoist239 <>. (impl__Bytes__len bytes <: usize) in
        if hoist240
        then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8
        else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
        (Core.Result.t_Result Prims.unit u8))

let random_bytes (len: usize) : t_Bytes =
  Core.Convert.f_into (Core.Iter.Traits.Iterator.f_collect (Core.Iter.Traits.Iterator.f_map ({
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = len
              }
              <:
              Core.Ops.Range.t_Range usize)
            (fun temp_0_ ->
                let _:usize = temp_0_ in
                Rand.random () <: u8)
          <:
          Core.Iter.Adapters.Map.t_Map (Core.Ops.Range.t_Range usize) (usize -> u8))
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

type t_AppData = | AppData : t_Bytes -> t_AppData

let impl__AppData__as_raw (self: t_AppData) : t_Bytes = self._0

let impl__AppData__into_raw (self: t_AppData) : t_Bytes = self._0

let impl__AppData__new (b: t_Bytes) : t_AppData = AppData b <: t_AppData

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core.Convert.t_From t_AppData (t_Slice u8) =
  { f_from = fun (value: t_Slice u8) -> AppData (Core.Convert.f_into value) <: t_AppData }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21 (v_N: usize) : Core.Convert.t_From t_AppData (t_Array u8 v_N) =
  { f_from = fun (value: t_Array u8 v_N) -> AppData (Core.Convert.f_into value) <: t_AppData }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Convert.t_From t_AppData (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  {
    f_from
    =
    fun (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) ->
      AppData (Core.Convert.f_into value) <: t_AppData
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Convert.t_From t_AppData t_Bytes =
  { f_from = fun (value: t_Bytes) -> AppData value <: t_AppData }
