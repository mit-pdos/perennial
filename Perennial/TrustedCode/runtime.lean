/-
Trusted code for `runtime`. `Gosched.impl` is in namespace `runtime`, as the
generated package.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace runtime
section code
variable [FfiSyntax] [GoGlobalContext]

def Gosched.impl : val :=
  λ: <>,
    #()

end code
end runtime

end Perennial
