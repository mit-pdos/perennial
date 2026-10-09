/-
Trusted code for the Go `fmt` package, in namespace `fmt` (as the generated
package).
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.Code.errors

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace fmt
section code
variable [FfiSyntax] [GoGlobalContext]

/-- `Errorf(format, a...)`: returns an error whose `Error()` is the formatted string. The model
does not format: it ignores the arguments `a` and returns `errors.New(format)`, an
`*errors.errorString` whose `Error()` is `format` itself. So it does not model `%w` (Go returns
a `*fmt.wrapError`/`*fmt.wrapErrors` that `errors.Unwrap`/`errors.Is` see through), the
formatted text, or any method the arguments' `Error()`/`String()` would call during
formatting. `wp_Errorf` only promises a non-nil error whose `Error()` returns some string. -/
noncomputable def Errorf.impl : val :=
  λ: "format" "a", FuncResolve errors.New [] #() "format"

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
