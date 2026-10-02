/-
Port of `new/golang/defn/lock.v`.
-/
import Perennial.Golang.Defn.Pre

namespace Perennial

namespace lock
section code
variable [ffi_syntax] [GoGlobalContext]

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
  λ: "m", exception_do (do: CmpXchg "m" #true #false ;;; return: #())

end code
end lock

attribute [irreducible] lock.trylock lock.lock lock.unlock

end Perennial
