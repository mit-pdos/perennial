/-
Trusted code for the Go `fmt` package, in namespace `fmt` (as the generated
package).
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace fmt
section code
variable [FfiSyntax] [GoGlobalContext]

-- FIXME: Returns some stuff
def Print.impl : val :=
  λ: "format" "a",
    Panic "unimplemented"

/-- `Printf(format, a...)`: writes to standard output, which is not modelled, and returns the
number of bytes written and an error; the model returns `(0, nil)`, and `wp_Printf` says nothing
of either. -/
def Printf.impl : val :=
  λ: "format" "a", (#(W64 0), #GoInterface.nil)

end code
end fmt

end Perennial
