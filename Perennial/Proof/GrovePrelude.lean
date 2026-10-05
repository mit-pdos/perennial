/-
Port of `new/proof/grove_prelude.v`: the proof prelude for code that uses the
Grove FFI (`github.com/mit-pdos/gokv/grove_ffi`).

Rocq exports `proof_prelude`, `atomic_fupd` and `New.grove_prelude`, and makes
`grove_semantics`, `grove_interp`, `gooseGroveGS` and `gooseGroveNodeGS`
global instances. In Lean, `Perennial.GrovePrelude` makes `grove_op`/`grove_model`
instances; here we add `grove_semantics` and `grove_interp`. (`gooseGroveGS` and
`gooseGroveNodeGS` are `abbrev`s that the Grove specs use explicitly, as for the
disk FFI in `Perennial.Proof.DiskPrelude`.) `atomic_fupd` is not ported. Rocq's
`Z_scope_test` has no Lean counterpart.
-/
import Perennial.Proof.ProofPrelude
import Perennial.GrovePrelude
import Perennial.GooseLang.Ffi.GroveFfi.GroveFfi

namespace Perennial

attribute [instance] grove_semantics grove_interp

end Perennial
