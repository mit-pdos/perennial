/-
The proofs of the Go `math/rand` package: the shared definitions (`Base`) and the linked results
(`Link`), `math.rand.wp_<F>` for each function `F` (the top-level `Int63`, `Int31`, `Int63n`,
`Int31n` and `Intn`, over the global generator).
-/
module

public import Perennial.Proof.math.rand.Base
public import Perennial.Proof.math.rand.Link

@[expose] public section
