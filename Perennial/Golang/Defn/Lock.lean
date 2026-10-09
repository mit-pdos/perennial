/-
A spin lock on a boolean location: `trylock`, `lock` and `unlock`.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

namespace Perennial

namespace lock
section code
variable [FfiSyntax] [GoGlobalContext]

def trylock : val :=
  λ: "m", Snd (CmpXchg "m" #false #true)

set_option linter.iris.dupNamespace false in
def lock : val :=
  rec: "lock" "m" :=
    if: Snd (CmpXchg "m" #false #true) then
      #()
    else
      "lock" "m"

def unlock : val :=
  λ: "m", exceptionDo (do: CmpXchg "m" #true #false ;;; return: #())

end code
end lock

attribute [irreducible] lock.trylock lock.lock lock.unlock

end Perennial
