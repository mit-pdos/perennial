/-
A spin lock on a boolean location: `trylock`, `lock` and `unlock` (the lock of `go.mutex`,
`Mutex.lean`).
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

/-- Unlocking an unlocked lock is stuck (Go: `fatal error: sync: unlock of unlocked
mutex`). -/
def unlock : val :=
  λ: "m", exceptionDo
    (do: (if: Snd (CmpXchg "m" #true #false) then #()
          else Panic "sync: unlock of unlocked mutex") ;;; return: #())

end code
end lock

attribute [irreducible] lock.trylock lock.lock lock.unlock


end Perennial
