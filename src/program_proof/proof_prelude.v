From iris.algebra Require Export auth gmap frac agree excl vector list.

From Perennial.Helpers Require Export BigOp.

From Perennial.program_logic Require Export ghost_var.
From Perennial.goose_lang Require Export proofmode wpc_proofmode array.
From Perennial.goose_lang Require Export readonly.
From Perennial.goose_lang.lib Require Export slice map struct loop lock.
From Perennial.goose_lang Require Export ffi.disk.
From Perennial.goose_lang Require Export ffi.disk_prelude.

Export uPred.

Global Set Default Proof Using "Type".
Global Set Printing Projections.

Existing Instance diskG0.

Notation length := List.length.
