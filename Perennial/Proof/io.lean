/-
The proofs of the Go `io` package: the shared definitions (`Base`, its `isPkgInit`; `Reader`,
the contract of an `io.Reader`) and the linked results (`Link`), `io.wp_<F>` for each function
`F` (`ReadAtLeast`, `ReadFull`, ...).
-/
module

public import Perennial.Proof.io.Base
public import Perennial.Proof.io.Reader
public import Perennial.Proof.io.Link

@[expose] public section
