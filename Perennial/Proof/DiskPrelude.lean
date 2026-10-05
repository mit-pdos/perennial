/-
Port of `new/proof/disk_prelude.v`: the proof prelude for code that uses the
disk FFI (`github.com/goose-lang/primitive/disk`).

Rocq makes `disk_semantics`, `disk_interp` and `gooseDiskGS` global instances
(on top of `New.disk_prelude`, which makes `disk_op`/`disk_model` global). In
Lean, `Perennial.DiskPrelude` makes `disk_op`/`disk_model` instances; here we
add `disk_semantics` and `disk_interp`. (`gooseDiskGS` is an `abbrev` that
the disk specs use explicitly.) `atomic_fupd` is not ported.
-/
import Perennial.Proof.ProofPrelude
import Perennial.DiskPrelude
import Perennial.GooseLang.Ffi.DiskFfi.Specs

namespace Perennial

attribute [instance] disk_semantics disk_interp

end Perennial
