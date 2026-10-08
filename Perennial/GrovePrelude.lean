/-
Makes the Grove FFI the global FFI, for code
that uses `github.com/mit-pdos/gokv/grove_ffi`.
-/
import Perennial.GooseLang.Ffi.GroveFfi.Impl

namespace Perennial

attribute [instance] grove_op grove_model

end Perennial
