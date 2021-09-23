From Perennial.goose_lang Require Import lang.
From Perennial.goose_lang Require Export ffi.grove_ffi.
Existing Instances grove_op grove_model grove_ty.
Existing Instances grove_semantics grove_interp.
Existing Instance goose_groveGS.
(* Now that the TC parameter is fixed, we can make this a coercion. *)
Coercion Var' (s: string) := Var s.
