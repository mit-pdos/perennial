From Perennial.goose_lang Require Import lang.
From Perennial.goose_lang Require Export ffi.disk.
Existing Instances disk.disk_op disk.disk_model disk.disk_ty.
Existing Instances disk.disk_semantics disk.disk_interp.
Existing Instance diskG0.
(* Now that the TC parameter is fixed, we can make this a coercion. *)
Coercion Var' (s: string) := Var s.
