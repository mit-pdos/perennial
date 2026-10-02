/-
Port of `new/trusted_code/fmt.v`. Rocq defines these at top level; here they
are in namespace `fmt`, as the generated package.
-/
import Perennial.Golang.Defn.Pre

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace fmt
section code
variable [ffi_syntax]

-- FIXME: Returns some stuff
def «Printⁱᵐᵖˡ» : val :=
  λ: "format" "a",
    Panic "unimplemented"

-- FIXME: Returns some stuff
def «Printfⁱᵐᵖˡ» : val :=
  λ: "a",
    Panic "unimplemented"

end code
end fmt

end Perennial
