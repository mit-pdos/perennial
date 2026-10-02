/-
Port of `new/grove_prelude.v`: makes the Grove FFI the global FFI, for code
that uses `github.com/mit-pdos/gokv/grove_ffi`.
-/
import Perennial.GooseLang.Ffi.GroveFfi.Impl

namespace Perennial

attribute [instance] grove_op grove_model

end Perennial
