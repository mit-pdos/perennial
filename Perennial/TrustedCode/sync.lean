/-
Port of `new/trusted_code/sync.v` (namespace `sync`, as the generated
package).

Lean addition (not in Rocq): `copyChecker` and its `check` method are trusted
here (Rocq axiomatizes them: `copyChecker.t` is an axiom type and `check` has no
body, so `wp_copyChecker__check` was admitted, with a false statement). See
`«copyCheckerⁱᵐᵖˡ»` below.
-/
import Perennial.Golang.Defn.Pre
import Perennial.Golang.Defn.Lock

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace sync

section code
variable [ffi_syntax] [GoGlobalContext]

@[reducible] def «Mutexⁱᵐᵖˡ» : go.type := go.bool

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

/-- Lean addition. `copyChecker` is a `uintptr` (sync/cond.go:
`type copyChecker uintptr`) that is only ever `0` or its own address
`uintptr(unsafe.Pointer(c))`. goose supports neither `uintptr` nor
pointer-to-integer conversions, so it is modeled as an `unsafe.Pointer` (a
`loc`): `0` is `null`, and `uintptr(unsafe.Pointer(c))` is `c` itself. -/
@[reducible] def «copyCheckerⁱᵐᵖˡ» : go.type := «unsafe».Pointer

/-- Lean addition. Model of (sync/cond.go)
```
func (c *copyChecker) check() {
	if uintptr(*c) != uintptr(unsafe.Pointer(c)) &&
		!atomic.CompareAndSwapUintptr((*uintptr)(c), 0, uintptr(unsafe.Pointer(c))) &&
		uintptr(*c) != uintptr(unsafe.Pointer(c)) {
		panic("sync.Cond is copied")
	}
}
```
The two reads of `*c` are plain loads in Go (racing with the CAS; the sync
package is exempt from the race detector); they are modeled as (atomic)
`Load`s. -/
def «copyChecker__checkⁱᵐᵖˡ» : val :=
  λ: "c" <>,
    if: Load "c" =⟨«unsafe».Pointer⟩ "c" then #()
    else if: Snd (CmpXchg "c" #null "c") then #()
    else if: Load "c" =⟨«unsafe».Pointer⟩ "c" then #()
    else Panic "sync.Cond is copied"

end code

namespace copyChecker
/-- Lean addition: see `«copyCheckerⁱᵐᵖˡ»`. -/
abbrev t := loc
end copyChecker

namespace Mutex
abbrev t := Bool
end Mutex

end sync

end Perennial
