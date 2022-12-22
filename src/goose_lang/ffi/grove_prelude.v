From Perennial.goose_lang Require Import lang.
From Perennial.goose_lang Require Export ffi.grove_ffi.
#[global]
Existing Instances grove_op grove_model grove_ty.
#[global]
Existing Instances grove_semantics grove_interp.
#[global]
Existing Instances goose_groveGS goose_groveNodeGS.
(* Now that the TC parameter is fixed, we can make this a coercion. Sadly,
[Var'] gets replaced by [Var] on the first substitution, so printing terms still
prints that [Var] -- but we barely look at those parts of the terms anyway. *)
Section coerce.
  Context {ext: ffi_syntax}.
  Coercion Var' (s: string) : (@expr ext) := Var s.
End coerce.
