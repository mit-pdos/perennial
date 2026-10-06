/-
Port of `new/trusted_code/runtime.v`. Rocq defines `Goschedⁱᵐᵖˡ` at top level;
here it is in namespace `runtime`, as the generated package.
-/
import Perennial.Golang.Defn.Pre

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace runtime
section code
variable [FfiSyntax] [GoGlobalContext]

def «Goschedⁱᵐᵖˡ» : val :=
  λ: <>,
    #()

end code
end runtime

end Perennial
