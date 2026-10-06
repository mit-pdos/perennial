/-
Port of `new/trusted_code/internal/synctest.v` (namespace
`internal.synctest`, as the generated package).
-/
import Perennial.Golang.Defn.Pre

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace internal.synctest
section code
variable [FfiSyntax] [GoGlobalContext]

def «Runⁱᵐᵖˡ» : val := λ: "f", Panic "not supported"

def «IsInBubbleⁱᵐᵖˡ» : val := λ: <>, #false

end code
end internal.synctest

end Perennial
