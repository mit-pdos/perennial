/-
The proofs of the Go `time` package: the shared definitions (`Base`, `PtrMethods`), the linked
results (`Link`), `time.wp_<F>` for each function `F`, and what is derived from them
(`Results`).
-/
module

public import Perennial.Proof.time.Base
public import Perennial.Proof.time.PtrMethods
public import Perennial.Proof.time.Link
public import Perennial.Proof.time.Results

@[expose] public section
