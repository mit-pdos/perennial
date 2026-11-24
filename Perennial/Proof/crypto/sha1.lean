/-
The proofs of the Go `crypto/sha1` package: the shared definitions (`Base`) and the linked
results (`Link`), `crypto/sha1.wp_<F>` for each function `F`.
-/
module

public import Perennial.Proof.crypto.sha1.Base
public import Perennial.Proof.crypto.sha1.Link
public import Perennial.Proof.crypto.sha1.Fips180

@[expose] public section
