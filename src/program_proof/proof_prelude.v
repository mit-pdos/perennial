From iris.proofmode Require Export coq_tactics reduction.
From iris.algebra Require Export auth gmap frac agree excl vector.
From Perennial.goose_lang Require Export wpc_proofmode.
From Perennial.goose_lang Require Export basic_triples.
From Perennial.goose_lang Require Export map_triples.
From Perennial.goose_lang Require Export slice.
From Perennial.goose_lang Require Export locks.
From Perennial.goose_lang Require Export ffi.disk.
From Perennial.goose_lang Require Export ffi.disk_prelude.
From Perennial.goose_lang Require Export lib.spin_lock.
Export uPred.

Global Set Default Proof Using "Type".
Global Set Printing Projections.

Existing Instance diskG0.
