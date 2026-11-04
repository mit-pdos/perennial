/-
The proofs of the Go `internal/syscall/unix` package: the shared definitions (`Base`, its `isPkgInit`) and the
linked results (`Link`), `internal.syscall.unix.wp_initialize'`.
-/
module

public import Perennial.Proof.internal.syscall.unix.Base
public import Perennial.Proof.internal.syscall.unix.Link

@[expose] public section
