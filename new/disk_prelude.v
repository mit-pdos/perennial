From Perennial.goose_lang Require Import lang.
From Perennial.goose_lang Require Import ffi.disk_ffi.impl.
#[global]
Existing Instances disk_op disk_model.
Coercion Var' (s: string) := Var s.
