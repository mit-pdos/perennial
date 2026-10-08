/-
The proof prelude for code that uses the
disk FFI (`github.com/goose-lang/primitive/disk`).

`Perennial.DiskPrelude` makes `disk_op`/`disk_model` instances; here we
add `disk_semantics` and `disk_interp`. (`gooseDiskGS` is an `abbrev` that
the disk specs use explicitly.)
-/
import Perennial.Proof.ProofPrelude
import Perennial.DiskPrelude
import Perennial.GooseLang.Ffi.DiskFfi.Specs

namespace Perennial

attribute [instance] disk_semantics disk_interp

end Perennial
