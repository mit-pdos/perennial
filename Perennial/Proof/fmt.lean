/-
The proofs of the Go `fmt` package: the shared definitions (`Base`: `isPkgInit`, `SprintfOut`,
the decimals of the integer directives, `ArgsWf`), the specs of the helpers of the model of
`Sprintf` (`SprintfModel`), and the linked results (`Link`), `fmt.wp_<F>` for each function `F`.
-/
module

public import Perennial.Proof.fmt.Base
public import Perennial.Proof.fmt.SprintfModel
public import Perennial.Proof.fmt.Link

@[expose] public section
