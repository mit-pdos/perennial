/-
The `sync` proofs: `base cond once mutex rwmutex_guard waitgroup
waitgroup_join`. `rwmutex_guard` imports the low-level `rwmutex` proofs
(`sync.rwmutex.*`, meant to be used qualified) and `sema`, so they are
available too.
-/
import Perennial.Proof.sync_proof.base
import Perennial.Proof.sync_proof.cond
import Perennial.Proof.sync_proof.once
import Perennial.Proof.sync_proof.mutex
import Perennial.Proof.sync_proof.rwmutex_guard
import Perennial.Proof.sync_proof.waitgroup
import Perennial.Proof.sync_proof.waitgroup_join
