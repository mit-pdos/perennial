/-
Makes the Grove FFI the global FFI, for code
that uses `github.com/mit-pdos/gokv/grove_ffi`.
-/
module

public import Perennial.GooseLang.Ffi.GroveFfi.Impl

@[expose] public section

namespace Perennial

attribute [instance] grove_op grove_model

end Perennial
