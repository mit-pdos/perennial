From Perennial.goose_lang Require Import lang.
From Perennial.goose_lang Require ffi.disk.
Existing Instances disk.disk_op disk.disk_model disk.disk_ty.
Existing Instances disk.disk_semantics disk.disk_interp.
Coercion Var' (s: string) := Var s.
