From Perennial.goose_lang Require Import lang.
From Perennial.goose_lang Require Export ffi.disk.
Existing Instances disk.disk_op disk.disk_model disk.disk_ty.
Existing Instances disk.disk_semantics disk.disk_interp.
Existing Instance goose_diskGS.
(* Now that the TC parameter is fixed, we can make this a coercion. Sadly,
[Var'] gets replaced by [Var] on the first substitution, so printing terms still
prints that [Var] -- but we barely look at those parts of the terms anyway. *)
Coercion Var' (s: string) := Var s.
