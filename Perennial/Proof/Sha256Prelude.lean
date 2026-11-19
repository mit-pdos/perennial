/-
The proof prelude for proofs about code that uses the SHA-256 extension (`crypto/sha256`): its
definition and specs. The proofs assume `[HasSha256 ok]` for the run's filter `ok`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GooseLang.Ext.Sha256.Impl
public import Perennial.GooseLang.Ext.Sha256.Specs
