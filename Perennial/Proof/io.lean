/-
The proofs of the Go `io` package: the shared definitions (`Base`, its `isPkgInit`; `Reader`,
the contract of an `io.Reader`; `Multi`, the readers of a `MultiReader`), the linked results
(`Link`), `io.wp_<F>` for each function `F` (`ReadAtLeast`, `ReadFull`, `MultiReader`, ...), and
`Results` (a `*multiReader` is a reader).
-/
module

public import Perennial.Proof.io.Base
public import Perennial.Proof.io.Reader
public import Perennial.Proof.io.Multi
public import Perennial.Proof.io.Link
public import Perennial.Proof.io.Results

@[expose] public section
