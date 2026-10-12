/-
The proofs of the Go `math/big` package: the shared definitions (`Base`: `isPkgInit`,
`natValue`, `ownInt`), the linked results (`Link`), `math.big.wp_<F>` for each function `F`,
and what is derived from them (`Results`: `math.big.wp_Int64`).
-/
module

public import Perennial.Proof.math.big.Base
public import Perennial.Proof.math.big.Link
public import Perennial.Proof.math.big.Results

@[expose] public section
