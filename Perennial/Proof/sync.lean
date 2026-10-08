/-
The `sync` proofs: `base cond once mutex rwmutex_guard waitgroup
waitgroup_join`. `rwmutex_guard` imports the low-level `rwmutex` proofs
(`sync.rwmutex.*`, meant to be used qualified) and `sema`, so they are
available too.
-/
module

public import Perennial.Proof.sync_proof.base
public import Perennial.Proof.sync_proof.cond
public import Perennial.Proof.sync_proof.once
public import Perennial.Proof.sync_proof.mutex
public import Perennial.Proof.sync_proof.rwmutex_guard
public import Perennial.Proof.sync_proof.waitgroup
public import Perennial.Proof.sync_proof.waitgroup_join

@[expose] public section
