/-
A spin lock on a boolean location: `trylock`, `lock` and `unlock`.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

namespace Perennial

namespace lock
section code
variable [GooseExts] [GoGlobalContext]

def trylock : val :=
  λ: "m", Snd (CmpXchg "m" #false #true)

set_option linter.iris.dupNamespace false in
def lock : val :=
  rec: "lock" "m" :=
    if: Snd (CmpXchg "m" #false #true) then
      #()
    else
      "lock" "m"

/-- Unlocks the lock; stuck if it is not locked, where Go's `Mutex.Unlock` ends the program
with `fatal("sync: unlock of unlocked mutex")` (`internal/sync/mutex.go`, `unlockSlow`),
which `recover` cannot catch. -/
def unlock : val :=
  λ: "m", if: Snd (CmpXchg "m" #true #false) then #()
    else Panic "sync: unlock of unlocked mutex"

end code
end lock

attribute [irreducible] lock.trylock lock.lock lock.unlock

end Perennial
