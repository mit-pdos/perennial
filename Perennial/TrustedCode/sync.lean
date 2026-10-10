/-
Trusted definitions of `sync` (namespace `sync`, as the generated package).

`copyChecker` and its `check` method are given trusted definitions here (rather
than axiomatized, which would leave `copyChecker.wp_check` unprovable). See
`copyChecker.underlying` below.
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.Golang.Defn.Lock

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace sync

section code
variable [FfiSyntax] [GoGlobalContext]

@[reducible] def Mutex.underlying : go.GoType := go.bool

def Mutex.TryLock.impl : val :=
  λ: "m" <>, lock.trylock "m"

def Mutex.Lock.impl : val :=
  λ: "m" <>, lock.lock "m"

def Mutex.Unlock.impl : val :=
  λ: "m" <>, lock.unlock "m"

def runtime_notifyListAdd.impl : val :=
  λ: "l", Convert go.int go.uint32 ArbitraryInt
def runtime_notifyListWait.impl : val :=
  λ: "l" "t", #()
def runtime_notifyListNotifyAll.impl : val :=
  λ: "l", #()
def runtime_notifyListNotifyOne.impl : val :=
  λ: "l", #()
def runtime_notifyListCheck.impl : val :=
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
def runtime_Semacquire.impl : val :=
  λ: "addr", exceptionDo
    (for: (λ: <>, #true) ; (λ: <>, #()) := λ: <>,
       let: "v" := AtomicWord 4 .load "addr" #() in
       (if: "v" =⟨go.uint32⟩ #(W32 0) then
          continue: #()
        else
          do: #()
       ) ;;;
       (if: Snd (AtomicWord 4 .cmpxchg "addr" ("v", "v" -⟨go.uint32⟩ #(W32 1))) then
          return: #()
        else
          do: #())
    )

def runtime_Semrelease.impl : val :=
  λ: "addr" "_handoff" "_skipframes", AtomicWord 4 .add "addr" #(W32 1) ;; #()

/-- differs from runtime_Semacquire only in the park "reason", used for
internal concurrency testing -/
def runtime_SemacquireWaitGroup.impl : val :=
  λ: "addr" "_synctestDurable", (FuncResolve "sync.runtime_Semacquire" []) #() "addr"

def runtime_SemacquireRWMutexR.impl : val :=
  λ: "addr" "_lifo" "_skipframes", (FuncResolve "sync.runtime_Semacquire" []) #() "addr"

def runtime_SemacquireRWMutex.impl : val :=
  λ: "addr" "_lifo" "_skipframes", (FuncResolve "sync.runtime_Semacquire" []) #() "addr"

/-- `copyChecker` is a `uintptr` (sync/cond.go:
`type copyChecker uintptr`) that is only ever `0` or its own address
`uintptr(unsafe.Pointer(c))`. goose supports neither `uintptr` nor
pointer-to-integer conversions, so it is modeled as an `unsafe.Pointer` (a
`loc`): `0` is `null`, and `uintptr(unsafe.Pointer(c))` is `c` itself. -/
@[reducible] def copyChecker.underlying : go.GoType := «unsafe».Pointer

/-- Model of (sync/cond.go)
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
def copyChecker.check.impl : val :=
  λ: "c" <>,
    if: Load "c" =⟨«unsafe».Pointer⟩ "c" then #()
    else if: Snd (CmpXchg "c" #null "c") then #()
    else if: Load "c" =⟨«unsafe».Pointer⟩ "c" then #()
    else Panic "sync.Cond is copied"

end code

/-- See `copyChecker.underlying`. -/
abbrev copyChecker := Loc

abbrev Mutex := Bool

end sync

end Perennial
