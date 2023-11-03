module Bertie.Tls13utils.Non_hax
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let impl: Core.Ops.Index.t_IndexMut Bertie.Tls13utils.t_Bytes usize =
  {
    f_index_mut
    =
    fun (self: Bertie.Tls13utils.t_Bytes) (i: usize) ->
      Rust_primitives.Hax.failure ""
        "{\n        let output: &mut bertie::tls13utils::t_U8 = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (deref(core::ops::index::f_index_mut(\n                        &mut (proj_bertie::tls13utils::_0(self)),\n                        i,\n                    ))),\n                ))\n            }))\n        };\n        Tuple2(self, output)\n    }"

  }

let impl_1: Core.Ops.Index.t_IndexMut Bertie.Tls13utils.t_Bytes (Core.Ops.Range.t_Range usize) =
  {
    f_index_mut
    =
    fun (self: Bertie.Tls13utils.t_Bytes) (x: Core.Ops.Range.t_Range usize) ->
      Rust_primitives.Hax.failure ""
        "{\n        let output: &mut [bertie::tls13utils::t_U8] = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (deref(core::ops::index::f_index_mut(\n                        &mut (proj_bertie::tls13utils::_0(self)),\n                        x,\n                    ))),\n                ))\n            }))\n        };\n        Tuple2(self, output)\n    }"

  }