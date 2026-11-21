/-
Manually written proof support for `sync`: the typed points-to of `sync.Mutex`, a struct
whose underlying type is that of the Go model `goose/model/mutex` (`TrustedCode/sync.lean`),
comes from the model's generated proofs.
-/
module

public import Perennial.Code.sync
public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.model.mutex

@[expose] public section
