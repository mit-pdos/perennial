/-
The proofs of the Go `sync` package: the shared definitions (`Base`, `SemaDefs`, `CondDefs`,
`OnceDefs`, `RWMutexDefs` with the low-level `RWMutex` protocol, `sync.rwmutex.*`, meant to be
used qualified, `RWMutexGuard` with the guarded interface, `WaitGroupDefs`, `WaitGroupJoin`,
`WaitGroupTokJoin`, `RWMutexThreads` with the reader tokens in a thread pool, `PoolDefs` with
`isPool` and the model of `Pool`'s state),
the linked results (`Link`), `sync.wp_<F>` for each function or method `F` (the low-level
`RWMutex` specs as `sync.rwmutex.RWMutex.wp_<M>`), and what is derived from them (`Results`:
the guarded `RWMutex` specs `sync.RWMutex.wp_<M>`, `Cond.wp_Wait_with`, the `Locker`
instances, the `WaitGroup` join idiom `sync.join.*` and its thread-token variant `sync.tokJoin.*`).
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.SemaDefs
public import Perennial.Proof.sync.CondDefs
public import Perennial.Proof.sync.OnceDefs
public import Perennial.Proof.sync.RWMutexDefs
public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.Proof.sync.RWMutexThreads
public import Perennial.Proof.sync.WaitGroupDefs
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.sync.WaitGroupTokJoin
public import Perennial.Proof.sync.PoolDefs
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.Results

@[expose] public section
