From iris.algebra Require Export auth gmap frac agree excl vector.

From Perennial.algebra Require Export big_op.

From Perennial.Helpers Require Export Tactics List ListLen BigOp Transitions iris ipm.

From Perennial.program_logic Require Export ghost_var.
From Perennial.goose_lang Require Export proofmode wpc_proofmode array.
From Perennial.goose_lang Require Export into_val.
From Perennial.goose_lang.lib Require Export
     persistent_readonly slice struct loop lock control map.typed_map.
From Perennial.goose_lang Require Export ffi.disk.
From Perennial.goose_lang Require Export ffi.disk_prelude.

From iris_string_ident Require Export ltac2_string_ident.

Export uPred.

Global Set Default Proof Using "Type".
Global Set Printing Projections.

Existing Instance diskG0.

Global Opaque load_ty store_ty.

Global Remove Hints fractional.frame_fractional : typeclass_instances.
Global Remove Hints fractional.into_sep_fractional : typeclass_instances.
