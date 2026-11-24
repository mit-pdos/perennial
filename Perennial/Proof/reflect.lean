/-
The proofs of the Go `reflect` package: the shared definitions (`Base`), the vocabulary of the
specs (`Values`: `reflType`, `reflPtr`, `reflElem`, `reflNew`), the linked results (`Link`),
`reflect.wp_<F>` for each function `F`, and the results in the vocabulary (`Results`).
-/
module

public import Perennial.Proof.reflect.Base
public import Perennial.Proof.reflect.Values
public import Perennial.Proof.reflect.Link
public import Perennial.Proof.reflect.Results

@[expose] public section
