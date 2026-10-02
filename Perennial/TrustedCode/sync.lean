/-
Port of `new/trusted_code/sync.v` (namespace `sync`, as the generated
package).
-/
import Perennial.Golang.Defn.Pre
import Perennial.Golang.Defn.Lock

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace sync

section code
variable [ffi_syntax] [GoGlobalContext]

def «Mutexⁱᵐᵖˡ» : go.type := go.bool

def «Mutex__TryLockⁱᵐᵖˡ» : val :=
  λ: "m" <>, lock.trylock "m"

def «Mutex__Lockⁱᵐᵖˡ» : val :=
  λ: "m" <>, lock.lock "m"

def «Mutex__Unlockⁱᵐᵖˡ» : val :=
  λ: "m" <>, lock.unlock "m"

def «runtime_notifyListAddⁱᵐᵖˡ» : val :=
  λ: "l", Convert go.int go.uint32 ArbitraryInt
def «runtime_notifyListWaitⁱᵐᵖˡ» : val :=
  λ: "l" "t", #()
def «runtime_notifyListNotifyAllⁱᵐᵖˡ» : val :=
  λ: "l", #()
def «runtime_notifyListNotifyOneⁱᵐᵖˡ» : val :=
  λ: "l", #()
def «runtime_notifyListCheckⁱᵐᵖˡ» : val :=
  λ: "l", #()

/-
inspired by runtime/sema.go:272:
```
func cansemacquire(addr *uint32) bool {
   for {
       v := atomic.Load(addr)
       if v == 0 {
           return false
       }
       if atomic.Cas(addr, v, v-1) {
           return true
       }
   }
}
```
-/
def «runtime_Semacquireⁱᵐᵖˡ» : val :=
  λ: "addr", exception_do
    (for: (λ: <>, #true) ; (λ: <>, #()) := λ: <>,
       let: "v" := Load "addr" in
       (if: "v" =⟨go.uint32⟩ #(W32 0) then
          continue: #()
        else
          do: #()
       ) ;;;
       (if: Snd (CmpXchg "addr" "v" ("v" -⟨go.uint32⟩ #(W32 1))) then
          return: #()
        else
          do: #())
    )

def «runtime_Semreleaseⁱᵐᵖˡ» : val :=
  λ: "addr" "_handoff" "_skipframes", AtomicAdd "addr" #(W32 1) ;; #()

/-- differs from runtime_Semacquire only in the park "reason", used for
internal concurrency testing -/
def «runtime_SemacquireWaitGroupⁱᵐᵖˡ» : val :=
  λ: "addr" "_synctestDurable", (FuncResolve "sync.runtime_Semacquire" []) #() "addr"

def «runtime_SemacquireRWMutexRⁱᵐᵖˡ» : val :=
  λ: "addr" "_lifo" "_skipframes", (FuncResolve "sync.runtime_Semacquire" []) #() "addr"

def «runtime_SemacquireRWMutexⁱᵐᵖˡ» : val :=
  λ: "addr" "_lifo" "_skipframes", (FuncResolve "sync.runtime_Semacquire" []) #() "addr"

end code

namespace Mutex
abbrev t := Bool
end Mutex

end sync

end Perennial
