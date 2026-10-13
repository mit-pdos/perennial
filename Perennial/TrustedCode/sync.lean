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

/-- The lock model's type (`go.mutex`, `Golang/Defn/Mutex.lean`): gc's size and alignment
(8, 4), the lock in its first cell. -/
@[reducible] def Mutex.underlying : go.GoType := go.mutex

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
       let: "v" := LoadN (.word 4) "addr" in
       (if: "v" =⟨go.uint32⟩ #(W32 0) then
          continue: #()
        else
          do: #()
       ) ;;;
       (if: Snd (CmpXchgN (.word 4) "addr" ("v", "v" -⟨go.uint32⟩ #(W32 1))) then
          return: #()
        else
          do: #())
    )

def runtime_Semrelease.impl : val :=
  λ: "addr" "_handoff" "_skipframes", AddN (.word 4) "addr" #(W32 1) ;; #()

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
`uintptr(unsafe.Pointer(c))`. It is modeled as an `unsafe.Pointer` (a `loc`):
`0` is `null`, and `uintptr(unsafe.Pointer(c))` is `c` itself.

Goose translates the real `check`, but in the semantics each `uintptr(p)` is a fresh
unspecified address (`go.UnsafeSemantics.convert_pointer_to_uintptr`: Go may move a
goroutine's stack between two conversions), so the translation may panic at every
call. Go's check relies on the address being fixed, which the runtime gives a `Cond`:
its methods pass `&c.notify` to the runtime (`runtime_notifyListAdd`, …, linknamed),
so a `Cond` escapes and lives on the heap, which gc does not move. The model is that
fixed address. -/
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
package is exempt from the race detector); they are modeled as atomic loads
(`LoadN`): an aligned 8-byte load on amd64 does not tear. -/
def copyChecker.check.impl : val :=
  λ: "c" <>,
    if: LoadN (.cell 8) "c" =⟨«unsafe».Pointer⟩ "c" then #()
    else if: Snd (CmpXchgN (.cell 8) "c" (#null, "c")) then #()
    else if: LoadN (.cell 8) "c" =⟨«unsafe».Pointer⟩ "c" then #()
    else Panic "sync.Cond is copied"

end code

/-- See `copyChecker.underlying`. -/
abbrev copyChecker := Loc

abbrev Mutex := MutexState

end sync

end Perennial
