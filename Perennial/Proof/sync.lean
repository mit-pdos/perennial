/-
Port of `new/proof/sync.v`: the `sync` proofs.

Rocq exports `base cond once mutex rwmutex_guard waitgroup waitgroup_join`;
`rwmutex_guard`, `waitgroup` and `waitgroup_join` are not ported yet, so this
exports the low-level `rwmutex` (and `sema`) instead.
-/
import Perennial.Proof.sync_proof.base
import Perennial.Proof.sync_proof.cond
import Perennial.Proof.sync_proof.once
import Perennial.Proof.sync_proof.mutex
import Perennial.Proof.sync_proof.sema
import Perennial.Proof.sync_proof.rwmutex
