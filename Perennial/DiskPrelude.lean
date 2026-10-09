/-
Makes the disk FFI the global FFI, for code that
uses `github.com/goose-lang/primitive/disk`.
-/
module

public import Perennial.GooseLang.Ffi.DiskFfi.Impl

@[expose] public section

noncomputable section

namespace Perennial

attribute [instance] disk_op disk_model

end Perennial
