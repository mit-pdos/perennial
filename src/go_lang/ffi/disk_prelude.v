From Perennial.go_lang Require Import lang.
From Perennial.go_lang Require ffi.disk.
Existing Instances disk.disk_op disk.disk_ty.
Coercion Var' (s: string) := Var s.
