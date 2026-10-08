/-
Trusted definitions of `log`, in namespace `log` like the generated package.
-/
import Perennial.Golang.Defn.Pre

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace log
section code
variable [FfiSyntax] [GoGlobalContext]

def Printf.impl : val :=
  λ: "format" "vs", #()

def Println.impl : val :=
  λ: "vs", #()

end code
end log

end Perennial
