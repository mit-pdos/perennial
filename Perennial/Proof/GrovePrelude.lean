/-
The proof prelude for code that uses the Grove FFI
(`github.com/mit-pdos/gokv/grove_ffi`).

`Perennial.GrovePrelude` makes `grove_op`/`grove_model` instances; here we add
`grove_semantics` and `grove_interp`. (`gooseGroveGS` and `gooseGroveNodeGS` are
`abbrev`s that the Grove specs use explicitly, as for the disk FFI in
`Perennial.Proof.DiskPrelude`.)
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GrovePrelude
public import Perennial.GooseLang.Ffi.GroveFfi.GroveFfi

@[expose] public section

noncomputable section

namespace Perennial

attribute [instance] grove_semantics grove_interp

end Perennial
