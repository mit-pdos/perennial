/-
The proofs of `github.com/mit-pdos/gokv/grove_ffi`, the Go functions over the Grove extension's
network, files and clocks: the shared definitions (`Base`: `isListener`, `isConnection`) and the
linked results (`Link`), `github_com.mit_pdos.gokv.grove_ffi.wp_<F>` for each function `F`.
-/
module

public import Perennial.Proof.github_com.mit_pdos.gokv.grove_ffi.Base
public import Perennial.Proof.github_com.mit_pdos.gokv.grove_ffi.Link

@[expose] public section
