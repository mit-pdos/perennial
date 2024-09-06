From Perennial.goose_lang Require Import lang typing.
From Perennial.goose_lang Require Export ffi.disk_ffi.typed_impl.
From Perennial.goose_lang Require Export ffi.disk.
#[global]
Existing Instances disk_op disk_model disk_ty.
#[global]
Existing Instances disk_semantics disk_interp.
#[global]
Existing Instance goose_diskGS.
Export disk.
