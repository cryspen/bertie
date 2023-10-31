module Bertie
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let parse_failed: u8 =
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
  Bertie.Tls13utils.v_PARSE_FAILED