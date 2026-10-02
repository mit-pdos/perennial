/-
Port of `new/trusted_code/log.v`. Rocq defines these at top level; here they
are in namespace `log`, as the generated package.
-/
import Perennial.Golang.Defn.Pre

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace log
section code
variable [ffi_syntax] [GoGlobalContext]

def «Printfⁱᵐᵖˡ» : val :=
  λ: "format" "vs", #()

def «Printlnⁱᵐᵖˡ» : val :=
  λ: "vs", #()

end code
end log

end Perennial
