/-
Makes the disk FFI the global FFI, for code that
uses `github.com/goose-lang/primitive/disk`.
-/
import Perennial.GooseLang.Ffi.DiskFfi.Impl

namespace Perennial

attribute [instance] disk_op disk_model

end Perennial
