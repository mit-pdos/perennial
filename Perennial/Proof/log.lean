/-
The proofs of the Go `log` package: the shared definitions (`Base`, its `isPkgInit`) and the
linked results (`Link`), `log.wp_initialize'`, `log.wp_Printf` and `log.wp_Println`.
-/
module

public import Perennial.Proof.log.Base
public import Perennial.Proof.log.Link

@[expose] public section
