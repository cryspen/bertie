module Bertie.Tls13utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let t_TLSError = u8

let v_UNSUPPORTED_ALGORITHM: u8 = 1uy

let v_CRYPTO_ERROR: u8 = 2uy

let v_INSUFFICIENT_ENTROPY: u8 = 3uy

let v_INCORRECT_ARRAY_LENGTH: u8 = 4uy

let v_INCORRECT_STATE: u8 = 128uy

let v_ZERO_RTT_DISABLED: u8 = 129uy

let v_PAYLOAD_TOO_LONG: u8 = 130uy

let v_PSK_MODE_MISMATCH: u8 = 131uy

let v_NEGOTIATION_MISMATCH: u8 = 132uy

let v_PARSE_FAILED: u8 = 133uy

let v_INSUFFICIENT_DATA: u8 = 134uy

let v_UNSUPPORTED: u8 = 135uy

let v_INVALID_COMPRESSION_LIST: u8 = 136uy

let v_PROTOCOL_VERSION_ALERT: u8 = 137uy

let v_APPLICATION_DATA_INSTEAD_OF_HANDSHAKE: u8 = 138uy

let v_MISSING_KEY_SHARE: u8 = 139uy

let v_INVALID_SIGNATURE: u8 = 140uy

let v_GOT_HANDSHAKE_FAILURE_ALERT: u8 = 141uy

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
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized v_T)
      (err: u8)
    : Core.Result.t_Result v_T u8 =
  let bt:Backtrace.Capture.t_Backtrace = Backtrace.Capture.impl__Backtrace__new in
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
  Core.Result.Result_Err err

class t_Declassify (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_891745436:t_Declassify v_Self;
  f_T:Type;
  f_T:Core.Marker.t_Sized i0.f_T;
  f_declassify:v_Self -> i0.f_T
}

type t_U8 = | U8 : u8 -> t_U8

let impl: Core.Ops.Bit.t_BitXor t_U8 t_U8 =
  { f_Output = t_U8; f_bitxor = fun (self: t_U8) (rhs: t_U8) -> U8 (self._0 ^. rhs._0) }

let impl_1: Core.Convert.t_From t_U8 u8 = { f_from = fun (x: u8) -> U8 x }

let impl_Declassify_for_U8: t_Declassify t_U8 =
  { f_T = u8; f_declassify = fun (self: t_U8) -> self._0 }

let impl_3: Core.Convert.t_From t_U8 u8 = { f_from = fun (x: u8) -> U8 x }

type t_U16 = | U16 : u16 -> t_U16

let impl_4: Core.Convert.t_From t_U16 u16 = { f_from = fun (x: u16) -> U16 x }

type t_U32 = | U32 : u32 -> t_U32

let impl_5: Core.Convert.t_From t_U32 u32 = { f_from = fun (x: u32) -> U32 x }

let impl_6: Core.Ops.Arith.t_Add t_U32 t_U32 =
  { f_Output = t_U32; f_add = fun (self: t_U32) (y: t_U32) -> U32 (self._0 +! y._0) }

type t_Bytes = | Bytes : Alloc.Vec.t_Vec t_U8 Alloc.Alloc.t_Global -> t_Bytes

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
              (fun x -> Core.Convert.f_into x <: t_U8)
            <:
            Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> t_U8)))
  }

let impl_Declassify_for_Bytes: t_Declassify t_Bytes =
  {
    f_T = Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global;
    f_declassify
    =
    fun (self: t_Bytes) ->
      Core.Iter.Traits.Iterator.f_collect (Core.Iter.Traits.Iterator.f_map (Core.Slice.impl__iter (Core.Ops.Deref.f_deref
                    self._0
                  <:
                  t_Slice t_U8)
              <:
              Core.Slice.Iter.t_Iter t_U8)
            (fun x -> f_declassify x <: u8)
          <:
          Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter t_U8) (t_U8 -> u8))
  }

let impl__Bytes__declassify_array (self: t_Bytes) : Core.Result.t_Result (t_Array u8 v_C) u8 =
  Core.Result.impl__map_err (Core.Convert.f_try_into (f_declassify self
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      <:
      Core.Result.t_Result (t_Array u8 v_C) (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
    (fun _ -> v_INCORRECT_ARRAY_LENGTH)

let impl_10: Core.Convert.t_From t_Bytes (t_Slice u8) =
  {
    f_from
    =
    fun (x: t_Slice u8) ->
      Core.Convert.f_into (Alloc.Slice.impl__to_vec x <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

let impl_11: Core.Convert.t_From t_Bytes (t_Slice t_U8) =
  { f_from = fun (x: t_Slice t_U8) -> Bytes (Alloc.Slice.impl__to_vec x) }

let impl_12 (#v_C: usize) : Core.Convert.t_From t_Bytes (t_Array u8 v_C) =
  {
    f_from
    =
    fun (x: t_Array u8 v_C) ->
      Core.Convert.f_into (Alloc.Slice.impl__to_vec (Rust_primitives.unsize x <: t_Slice u8)
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

let impl_13 (#v_C: usize) : Core.Convert.t_From t_Bytes (t_Array u8 v_C) =
  {
    f_from
    =
    fun (x: t_Array u8 v_C) ->
      Core.Convert.f_into (Alloc.Slice.impl__to_vec (Rust_primitives.unsize x <: t_Slice u8)
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

let impl__U32__from_be_bytes (x: t_Bytes) : Core.Result.t_Result t_U32 u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist395:t_Array u8 (sz 4) =
        match
          Core.Ops.Try_trait.f_branch (impl__Bytes__declassify_array x
              <:
              Core.Result.t_Result (t_Array u8 (sz 4)) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist394:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_U32 u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist394)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist396:u32 = Core.Num.impl__u32__from_be_bytes hoist395 in
        let hoist397:t_U32 = U32 hoist396 in
        Core.Result.Result_Ok hoist397))

let impl__U32__to_be_bytes (self: t_U32) : t_Bytes =
  Core.Convert.f_into (Alloc.Slice.impl__to_vec (Rust_primitives.unsize (Core.Num.impl__u32__to_be_bytes
                self._0
              <:
              t_Array u8 (sz 4))
          <:
          t_Slice u8)
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let impl__U32__declassify (self: t_U32) : u32 = self._0

let impl__U16__from_be_bytes (x: t_Bytes) : Core.Result.t_Result t_U16 u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist399:t_Array u8 (sz 2) =
        match
          Core.Ops.Try_trait.f_branch (impl__Bytes__declassify_array x
              <:
              Core.Result.t_Result (t_Array u8 (sz 2)) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist398:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_U16 u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist398)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist400:u16 = Core.Num.impl__u16__from_be_bytes hoist399 in
        let hoist401:t_U16 = U16 hoist400 in
        Core.Result.Result_Ok hoist401))

let impl__U16__to_be_bytes (self: t_U16) : t_Bytes =
  Core.Convert.f_into (Alloc.Slice.impl__to_vec (Rust_primitives.unsize (Core.Num.impl__u16__to_be_bytes
                self._0
              <:
              t_Array u8 (sz 2))
          <:
          t_Slice u8)
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let impl__U16__declassify (self: t_U16) : u16 = self._0

let bytes (x: t_Slice u8) : t_Bytes = Core.Convert.f_into x

let bytes1 (x: u8) : t_Bytes =
  Core.Convert.f_into (let list = [x] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list list)

let bytes2 (x y: u8) : t_Bytes =
  Core.Convert.f_into (let list = [x; y] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
      Rust_primitives.Hax.array_of_list list)

let impl_16: Core.Ops.Index.t_Index t_Bytes usize =
  { f_Output = t_U8; f_index = fun (self: t_Bytes) (x: usize) -> self._0.[ x ] }

let impl_17: Core.Ops.Index.t_Index t_Bytes (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice t_U8;
    f_index = fun (self: t_Bytes) (x: Core.Ops.Range.t_Range usize) -> self._0.[ x ]
  }

let impl__Bytes__new: t_Bytes = Bytes Alloc.Vec.impl__new

let impl__Bytes__zeroes (len: usize) : t_Bytes = Bytes (Alloc.Vec.from_elem (U8 0uy) len)

let impl__Bytes__with_capacity (len: usize) : t_Bytes = Bytes (Alloc.Vec.impl__with_capacity len)

let impl__Bytes__len (self: t_Bytes) : usize = Alloc.Vec.impl_1__len self._0

let impl__Bytes__push (self: t_Bytes) (x: t_U8) : t_Bytes =
  let output, self:(Prims.unit & t_Bytes) =
    (), { self with _0 = Alloc.Vec.impl_1__push self._0 x }
  in
  self

let impl__Bytes__extend_from_slice (self x: t_Bytes) : t_Bytes =
  let output, self:(Prims.unit & t_Bytes) =
    (),
    {
      self with
      _0 = Alloc.Vec.impl_2__extend_from_slice self._0 (Core.Ops.Deref.f_deref x._0 <: t_Slice t_U8)
    }
  in
  self

let impl__Bytes__from_slice (s: t_Slice u8) : t_Bytes = Core.Convert.f_into s

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
                      })
                    (sz 2)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
                (fun i ->
                    Core.Option.impl__and_then (Core.Str.impl__str__get (Core.Ops.Deref.f_deref s
                            <:
                            string)
                          ({ Core.Ops.Range.f_start = i; Core.Ops.Range.f_end = i +! sz 2 <: usize }
                          )
                        <:
                        Core.Option.t_Option string)
                      (fun sub ->
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
  else Core.Option.impl__expect Core.Option.Option_None "Not a hex string2"

let impl__Bytes__to_hex (self: t_Bytes) : Alloc.String.t_String =
  let (strs: Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
    Alloc.String.t_String Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.f_collect (Core.Iter.Traits.Iterator.f_map (Core.Slice.impl__iter (Core.Ops.Deref.f_deref
                  self._0
                <:
                t_Slice t_U8)
            <:
            Core.Slice.Iter.t_Iter t_U8)
          (fun b ->
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
                              Core.Fmt.Rt.impl_1__new_lower_hex (f_declassify b <: u8)
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
                                Core.Fmt.Rt.Alignment_Unknown
                                8ul
                                Core.Fmt.Rt.Count_Implied
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
                        "{ Types.attributes = [];\n  contents =\n  Types.Block {\n    expr =\n    (Some { Types.attributes = [];\n            contents =\n            Types.Call {args = [];\n              fn_span =\n              { Types.filename =\n                (Types.Real\n                   Types.Remapped {\n                     local_path =\n                     (Some \"/Users/franziskus/.rustup/toolchains/nightly-2023-06-02-aarch64-apple-darwin/lib/rustlib/src/rust/library/alloc/src/macros.rs\");\n                     virtual_name =\n                     \"/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/macros.rs\"});\n                hi = { Types.col = \"78\"; line = \"120\" };\n                lo = { Types.col = \"38\"; line = \"120\" } };\n              from_hir_call = true;\n              fun' =\n              { Types.attributes = [];\n                contents =\n                Types.GlobalName {\n                  id =\n                  { Types.index = (2, 9101); krate = \"core\";\n                    path =\n                    [{ Types.data = (Types.TypeNs \"fmt\"); disambiguator = 0 };\n                      { Types.data = (Types.TypeNs \"rt\"); disambiguator = 0 };\n                      { Types.data = Types.Impl; disambiguator = 2 };\n                      { Types.data = (Types.ValueNs \"new\"); disambiguator = 0\n                        }\n                      ]\n                    }};\n                hir_id = None;\n                span =\n                { Types.filename =\n                  (Types.Real\n                     Types.Remapped {\n                       local_path =\n                       (Some \"/Users/franziskus/.rustup/toolchains/nightly-2023-06-02-aarch64-apple-darwin/lib/rustlib/src/rust/library/alloc/src/macros.rs\");\n                       virtual_name =\n                       \"/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/macros.rs\"});\n                  hi = { Types.col = \"78\"; line = \"120\" };\n                  lo = { Types.col = \"38\"; line = \"120\" } };\n                ty =\n                (Types.Arrow\n                   { Types.bound_vars = [];\n                     value =\n                     { Types.abi = Types.Abi {todo = \"Rust\"};\n                       c_variadic = false; inputs = [];\n                       output =\n                       Types.Adt {\n                         def_id =\n                         { Types.index = (2, 9098); krate = \"core\";\n                           path =\n                           [{ Types.data = (Types.TypeNs \"fmt\");\n                              disambiguator = 0 };\n                             { Types.data = (Types.TypeNs \"rt\");\n                               disambiguator = 0 };\n                             { Types.data = (Types.TypeNs \"UnsafeArg\");\n                               disambiguator = 0 }\n                             ]\n                           };\n                         generic_args = []};\n                       unsafety = Types.Unsafe }\n                     })\n                };\n              impl = None;\n              ty =\n              (Types.Arrow\n                 { Types.bound_vars = [];\n                   value =\n                   { Types.abi = Types.Abi {todo = \"Rust\"};\n                     c_variadic = false; inputs = [];\n                     output =\n                     Types.Adt {\n                       def_id =\n                       { Types.index = (2, 9098); krate = \"core\";\n                         path =\n                         [{ Types.data = (Types.TypeNs \"fmt\");\n                            disambiguator = 0 };\n                           { Types.data = (Types.TypeNs \"rt\");\n                             disambiguator = 0 };\n                           { Types.data = (Types.TypeNs \"UnsafeArg\");\n                             disambiguator = 0 }\n                           ]\n                         };\n                       generic_args = []};\n                     unsafety = Types.Unsafe }\n                   })};\n            hir_id = (Some (\"399\", \"68\"));\n            span =\n            { Types.filename =\n              (Types.Real\n                 Types.Remapped {\n                   local_path =\n                   (Some \"/Users/franziskus/.rustup/toolchains/nightly-2023-06-02-aarch64-apple-darwin/lib/rustlib/src/rust/library/alloc/src/macros.rs\");\n                   virtual_name =\n                   \"/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/macros.rs\"});\n              hi = { Types.col = \"78\"; line = \"120\" };\n              lo = { Types.col = \"38\"; line = \"120\" } };\n            ty =\n            Types.Adt {\n              def_id =\n              { Types.index = (2, 9098); krate = \"core\";\n                path =\n                [{ Types.data = (Types.TypeNs \"fmt\"); disambiguator = 0 };\n                  { Types.data = (Types.TypeNs \"rt\"); disambiguator = 0 };\n                  { Types.data = (Types.TypeNs \"UnsafeArg\");\n                    disambiguator = 0 }\n                  ]\n                };\n              generic_args = []}\n            });\n    opt_destruction_scope = None;\n    region_scope = { Types.data = Types.Node; id = \"69\" };\n    safety_mode = Types.BuiltinUnsafe;\n    span =\n    { Types.filename =\n      (Types.Real\n         Types.Remapped {\n           local_path =\n           (Some \"/Users/franziskus/.rustup/toolchains/nightly-2023-06-02-aarch64-apple-darwin/lib/rustlib/src/rust/library/alloc/src/macros.rs\");\n           virtual_name =\n           \"/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/macros.rs\"});\n      hi = { Types.col = \"78\"; line = \"120\" };\n      lo = { Types.col = \"38\"; line = \"120\" } };\n    stmts = []; targeted_by_break = false};\n  hir_id = (Some (\"399\", \"70\"));\n  span =\n  { Types.filename =\n    (Types.Real\n       Types.Remapped {\n         local_path =\n         (Some \"/Users/franziskus/.rustup/toolchains/nightly-2023-06-02-aarch64-apple-darwin/lib/rustlib/src/rust/library/alloc/src/macros.rs\");\n         virtual_name =\n         \"/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/macros.rs\"});\n    hi = { Types.col = \"78\"; line = \"120\" };\n    lo = { Types.col = \"38\"; line = \"120\" } };\n  ty =\n  Types.Adt {\n    def_id =\n    { Types.index = (2, 9098); krate = \"core\";\n      path =\n      [{ Types.data = (Types.TypeNs \"fmt\"); disambiguator = 0 };\n        { Types.data = (Types.TypeNs \"rt\"); disambiguator = 0 };\n        { Types.data = (Types.TypeNs \"UnsafeArg\"); disambiguator = 0 }]\n      };\n    generic_args = []}\n  }"

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

let impl__Bytes__slice_range (self: t_Bytes) (r: Core.Ops.Range.t_Range usize) : t_Bytes =
  Core.Convert.f_into (self._0.[ {
          Core.Ops.Range.f_start = r.Core.Ops.Range.f_start;
          Core.Ops.Range.f_end = r.Core.Ops.Range.f_end
        } ]
      <:
      t_Slice t_U8)

let impl__Bytes__slice (self: t_Bytes) (start len: usize) : t_Bytes =
  Core.Convert.f_into (self._0.[ {
          Core.Ops.Range.f_start = start;
          Core.Ops.Range.f_end = start +! len <: usize
        } ]
      <:
      t_Slice t_U8)

let impl__Bytes__concat (self x: t_Bytes) : t_Bytes =
  let res:Alloc.Vec.t_Vec t_U8 Alloc.Alloc.t_Global = Alloc.Vec.impl__new in
  let res:Alloc.Vec.t_Vec t_U8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice res (Core.Ops.Deref.f_deref self._0 <: t_Slice t_U8)
  in
  let res:Alloc.Vec.t_Vec t_U8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice res (Core.Ops.Deref.f_deref x._0 <: t_Slice t_U8)
  in
  Bytes res

let impl__Bytes__update_slice (self: t_Bytes) (st: usize) (src: t_Bytes) (beg len: usize) : t_Bytes =
  let res:t_Bytes = Core.Clone.f_clone self in
  let res:t_Bytes =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = len
            })
        <:
        Core.Ops.Range.t_Range usize)
      res
      (fun res i ->
          Rust_primitives.Hax.update_at res (st +! i <: usize) (src.[ beg +! i <: usize ] <: t_U8)
          <:
          t_Bytes)
  in
  res

let check (b: bool) : Core.Result.t_Result Prims.unit u8 =
  if b then Core.Result.Result_Ok () else Core.Result.Result_Err parse_failed

let eq1 (b1 b2: t_U8) : bool = (f_declassify b1 <: u8) =. (f_declassify b2 <: u8)

let check_eq1 (b1 b2: t_U8) : Core.Result.t_Result Prims.unit u8 =
  if eq1 b1 b2 then Core.Result.Result_Ok () else Core.Result.Result_Err parse_failed

let eq (b1 b2: t_Bytes) : bool =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (impl__Bytes__len b1 <: usize) <>. (impl__Bytes__len b2 <: usize) <: bool
      then Core.Ops.Control_flow.ControlFlow_Continue false
      else
        let (b: bool):bool = true in
        let b:bool =
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = impl__Bytes__len b1 <: usize
                  })
              <:
              Core.Ops.Range.t_Range usize)
            b
            (fun b i ->
                if ~.(eq1 (b1.[ i ] <: t_U8) (b2.[ i ] <: t_U8) <: bool) <: bool
                then
                  let b:bool = false in
                  b
                else b)
        in
        let* hoist402:Rust_primitives.Hax.t_Never = Core.Ops.Control_flow.ControlFlow.v_Break b in
        Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist402))

let check_eq (b1 b2: t_Bytes) : Core.Result.t_Result Prims.unit u8 =
  let b:bool = eq b1 b2 in
  if b then Core.Result.Result_Ok () else Core.Result.Result_Err parse_failed

let check_mem (b1 b2: t_Bytes) : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        ((impl__Bytes__len b2 <: usize) %! (impl__Bytes__len b1 <: usize) <: usize) <>. sz 0 <: bool
      then Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Err (parse_failed <: u8))
      else
        let b:bool = false in
        let b:bool =
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end
                    =
                    (impl__Bytes__len b2 <: usize) /! (impl__Bytes__len b1 <: usize) <: usize
                  })
              <:
              Core.Ops.Range.t_Range usize)
            b
            (fun b i ->
                if
                  eq b1
                    (impl__Bytes__slice_range b2
                        ({
                            Core.Ops.Range.f_start = i *! (impl__Bytes__len b1 <: usize) <: usize;
                            Core.Ops.Range.f_end
                            =
                            (i +! sz 1 <: usize) *! (impl__Bytes__len b1 <: usize) <: usize
                          })
                      <:
                      t_Bytes)
                  <:
                  bool
                then
                  let b:bool = true in
                  b
                else b)
        in
        let* hoist403:Rust_primitives.Hax.t_Never =
          Core.Ops.Control_flow.ControlFlow.v_Break (if b
              then Core.Result.Result_Ok ()
              else Core.Result.Result_Err (parse_failed <: u8))
        in
        Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist403))

let lbytes1 (b: t_Bytes) : Core.Result.t_Result t_Bytes u8 =
  let len:usize = impl__Bytes__len b in
  if len >=. sz 256
  then Core.Result.Result_Err v_PAYLOAD_TOO_LONG
  else
    let lenb:t_Bytes = impl__Bytes__new in
    let lenb:t_Bytes = impl__Bytes__push lenb (Core.Convert.f_into (cast len <: u8) <: t_U8) in
    let lenb:t_Bytes = impl__Bytes__extend_from_slice lenb b in
    Core.Result.Result_Ok lenb

let lbytes2 (b: t_Bytes) : Core.Result.t_Result t_Bytes u8 =
  let len:usize = impl__Bytes__len b in
  if len >=. sz 65536
  then Core.Result.Result_Err v_PAYLOAD_TOO_LONG
  else
    let (len: t_Bytes):t_Bytes = impl__U16__to_be_bytes (U16 (cast len <: u16)) in
    let lenb:t_Bytes = impl__Bytes__new in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 0 ] <: t_U8) in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 1 ] <: t_U8) in
    let lenb:t_Bytes = impl__Bytes__extend_from_slice lenb b in
    Core.Result.Result_Ok lenb

let lbytes3 (b: t_Bytes) : Core.Result.t_Result t_Bytes u8 =
  let len:usize = impl__Bytes__len b in
  if len >=. sz 16777216
  then Core.Result.Result_Err v_PAYLOAD_TOO_LONG
  else
    let (len: t_Bytes):t_Bytes = impl__U32__to_be_bytes (U32 (cast len <: u32)) in
    let lenb:t_Bytes = impl__Bytes__new in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 1 ] <: t_U8) in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 2 ] <: t_U8) in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 3 ] <: t_U8) in
    let lenb:t_Bytes = impl__Bytes__extend_from_slice lenb b in
    Core.Result.Result_Ok lenb

let check_lbytes1 (b: t_Bytes) : Core.Result.t_Result usize u8 =
  if (impl__Bytes__len b <: usize) <. sz 1
  then Core.Result.Result_Err parse_failed
  else
    let l:usize = cast (f_declassify (b.[ sz 0 ] <: t_U8)) <: usize in
    if ((impl__Bytes__len b <: usize) -! sz 1 <: usize) <. l
    then Core.Result.Result_Err parse_failed
    else Core.Result.Result_Ok l

let check_lbytes2 (b: t_Bytes) : Core.Result.t_Result usize u8 =
  if (impl__Bytes__len b <: usize) <. sz 2
  then Core.Result.Result_Err parse_failed
  else
    let l0:usize = cast (f_declassify (b.[ sz 0 ] <: t_U8)) <: usize in
    let l1:usize = cast (f_declassify (b.[ sz 1 ] <: t_U8)) <: usize in
    let l:usize = (l0 *! sz 256 <: usize) +! l1 in
    if ((impl__Bytes__len b <: usize) -! sz 2 <: usize) <. l
    then Core.Result.Result_Err parse_failed
    else Core.Result.Result_Ok l

let check_lbytes3 (b: t_Bytes) : Core.Result.t_Result usize u8 =
  if (impl__Bytes__len b <: usize) <. sz 3
  then Core.Result.Result_Err parse_failed
  else
    let l0:usize = cast (f_declassify (b.[ sz 0 ] <: t_U8)) <: usize in
    let l1:usize = cast (f_declassify (b.[ sz 1 ] <: t_U8)) <: usize in
    let l2:usize = cast (f_declassify (b.[ sz 2 ] <: t_U8)) <: usize in
    let l:usize = ((l0 *! sz 65536 <: usize) +! (l1 *! sz 256 <: usize) <: usize) +! l2 in
    if ((impl__Bytes__len b <: usize) -! sz 3 <: usize) <. l
    then Core.Result.Result_Err parse_failed
    else Core.Result.Result_Ok l

let check_lbytes1_full (b: t_Bytes) : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist405:usize =
        match Core.Ops.Try_trait.f_branch (check_lbytes1 b <: Core.Result.t_Result usize u8) with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist404:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist404)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist406:usize = hoist405 +! sz 1 in
        let hoist407:bool = hoist406 <>. (impl__Bytes__len b <: usize) in
        if hoist407 then Core.Result.Result_Err parse_failed else Core.Result.Result_Ok ()))

let check_lbytes2_full (b: t_Bytes) : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist409:usize =
        match Core.Ops.Try_trait.f_branch (check_lbytes2 b <: Core.Result.t_Result usize u8) with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist408:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist408)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist410:usize = hoist409 +! sz 2 in
        let hoist411:bool = hoist410 <>. (impl__Bytes__len b <: usize) in
        if hoist411 then Core.Result.Result_Err parse_failed else Core.Result.Result_Ok ()))

let check_lbytes3_full (b: t_Bytes) : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist413:usize =
        match Core.Ops.Try_trait.f_branch (check_lbytes3 b <: Core.Result.t_Result usize u8) with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist412:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist412)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist414:usize = hoist413 +! sz 3 in
        let hoist415:bool = hoist414 <>. (impl__Bytes__len b <: usize) in
        if hoist415 then Core.Result.Result_Err parse_failed else Core.Result.Result_Ok ()))

type t_HandshakeData = | HandshakeData : t_Bytes -> t_HandshakeData

let handshake_data (b: t_Bytes) : t_HandshakeData = HandshakeData b

let handshake_data_bytes (hd: t_HandshakeData) : t_Bytes = Core.Clone.f_clone hd._0

let handshake_data_len (p: t_HandshakeData) : usize = impl__Bytes__len p._0

let handshake_concat (msg1 msg2: t_HandshakeData) : t_HandshakeData =
  let HandshakeData m1:t_HandshakeData = msg1 in
  let HandshakeData m2:t_HandshakeData = msg2 in
  let m1:t_Bytes =
    {
      m1 with
      _0 = Alloc.Vec.impl_2__extend_from_slice m1._0 (Core.Ops.Deref.f_deref m2._0 <: t_Slice t_U8)
    }
  in
  HandshakeData m1

type t_AppData = | AppData : t_Bytes -> t_AppData

let app_data (b: t_Bytes) : t_AppData = AppData b

let app_data_bytes (a: t_AppData) : t_Bytes = a._0

let random_bytes (len: usize) : t_Bytes =
  Core.Convert.f_into (Core.Iter.Traits.Iterator.f_collect (Core.Iter.Traits.Iterator.f_map ({
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = len
              })
            (fun _ -> Rand.random <: u8)
          <:
          Core.Iter.Adapters.Map.t_Map (Core.Ops.Range.t_Range usize) (usize -> u8))
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)