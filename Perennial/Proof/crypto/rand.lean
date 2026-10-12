/-
The proofs of the Go `crypto/rand` package: the shared definitions (`Base`: `isPkgInit`,
`isInitialized`) and the linked results (`Link`), `crypto.rand.wp_initialize'` and
`crypto.rand.wp_Int`.
-/
module

public import Perennial.Proof.crypto.rand.Base
public import Perennial.Proof.crypto.rand.Link

@[expose] public section
