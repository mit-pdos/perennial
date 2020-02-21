From iris.algebra Require Export auth gmap frac agree excl vector.

From Perennial.Helpers Require Export BigOp.

From Perennial.goose_lang Require Export proofmode wpc_proofmode.
From Perennial.goose_lang Require Export readonly.
From Perennial.goose_lang.lib Require Export slice map struct spin_lock loop.
From Perennial.goose_lang Require Export locks.
From Perennial.goose_lang Require Export ffi.disk.
From Perennial.goose_lang Require Export ffi.disk_prelude.

Export uPred.

Global Set Default Proof Using "Type".
Global Set Printing Projections.

Existing Instance diskG0.
