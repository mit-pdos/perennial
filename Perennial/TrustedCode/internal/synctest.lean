/-
Trusted model of `internal/synctest` (namespace `internal.synctest`, as the
generated package).
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace internal.synctest
section code
variable [FfiSyntax] [GoGlobalContext]

def Run.impl : val := λ: "f", Panic "not supported"

def IsInBubble.impl : val := λ: <>, #false

end code
end internal.synctest

end Perennial
