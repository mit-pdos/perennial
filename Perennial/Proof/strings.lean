/-
The proofs of the Go `strings` package: the shared definitions (`Base`, and `BuilderDefs` for
`strings.Builder`) and the linked results (`Link`), `strings.wp_<F>` for each function `F` and
`strings.Builder.wp_<M>` for each method `M` of `Builder`.
-/
module

public import Perennial.Proof.strings.Base
public import Perennial.Proof.strings.BuilderDefs
public import Perennial.Proof.strings.Link

@[expose] public section
