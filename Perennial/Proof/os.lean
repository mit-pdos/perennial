/-
The proofs of the Go `os` package: the specs of the trusted models its initializer runs
(`Models`) and the linked results (`Link`): `os.wp_Exit`. `os`'s initializer is proved by its
clients.
-/
module

public import Perennial.Proof.os.Models
public import Perennial.Proof.os.Link

@[expose] public section
