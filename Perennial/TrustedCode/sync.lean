/-
Trusted definitions of `sync` (namespace `sync`, as the generated package).

`copyChecker` and its `check` method are given trusted definitions here (rather
than axiomatized, which would leave `copyChecker.wp_check` unprovable). See
`copyChecker.underlying` below.
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.Golang.Defn.Lock
public import Perennial.Code.github_com.mit_pdos.perennial.goose.model.pool

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace sync

section code
variable [GooseExts] [GoGlobalContext]

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

/-- `runtime_registerPoolCleanup` (sync/pool.go), a linkname to the runtime (runtime/mgc.go):

```go
func sync_runtime_registerPoolCleanup(f func()) {
	poolcleanup = f
}
```

The GC calls `poolcleanup` at the start of each cycle. The model has no GC, and `Pool`'s methods
are not translated (see `Pool.Get.impl`), so no translated code observes the pool state it
clears. -/
def runtime_registerPoolCleanup.impl : val :=
  λ: "cleanup", #()

/-- The state of the `sync.Pool` at `p`: a `*pool.Pool` of the Go model
`github.com/mit-pdos/perennial/goose/model/pool`, kept in `p`'s field `local` (an
`unsafe.Pointer`; Go keeps its per-P pools there). The zero `Pool` has `local = nil`; the
first call installs a new, empty model pool with a compare-and-swap, and every call returns
what `local` holds after it. Not a Go function: a helper of `Pool.Put.impl` and
`Pool.Get.impl`. -/
noncomputable def Pool.state : val :=
  λ: "p",
    let: "new" := GoAlloc github_com.mit_pdos.perennial.goose.model.pool.Pool.ty
      (GoZeroVal github_com.mit_pdos.perennial.goose.model.pool.Pool.ty #()) in
    let: "r" := CmpXchg (StructFieldRef (go.GoType.Named go!"sync.Pool" []) go!"local" "p")
      #null "new" in
    if: Snd "r" then "new" else Fst "r"

/-- Model of `Pool.Put` (sync/pool.go):
```go
func (p *Pool) Put(x any) {
	if x == nil {
		return
	}
	if race.Enabled { ... }
	l, _ := p.pin()
	if l.private == nil {
		l.private = x
	} else {
		l.shared.pushHead(x)
	}
	runtime_procUnpin()
	...
}
```
The per-P pools (`pin`, `runtime_procPin`, the lock-free `poolChain` of `poolDequeue`s
reached by pointer arithmetic on `unsafe.Pointer`s, the victim cache cleared by the GC) are
replaced by the model pool of `Pool.state`, whose `Put` adds `x` or drops it
(`goose/model/pool`). -/
noncomputable def Pool.Put.impl : val :=
  λ: "p" "x",
    if: "x" =⟨go.any⟩ #GoInterface.nil then #()
    else
      (MethodResolve (go.PointerType github_com.mit_pdos.perennial.goose.model.pool.Pool.ty)
        go!"Put") (Pool.state "p") "x"

/-- Model of `Pool.Get` (sync/pool.go):
```go
func (p *Pool) Get() any {
	if race.Enabled { ... }
	l, pid := p.pin()
	x := l.private
	l.private = nil
	if x == nil {
		x, _ = l.shared.popHead()
		if x == nil {
			x = p.getSlow(pid)
		}
	}
	runtime_procUnpin()
	...
	if x == nil && p.New != nil {
		x = p.New()
	}
	return x
}
```
The search of the per-P pools and the victim cache, up to `runtime_procUnpin()`, is the model
pool's `Get` (`Pool.state`), which removes and returns an arbitrary element or returns `nil`,
even when the pool is not empty; the rest is Go's. -/
noncomputable def Pool.Get.impl : val :=
  λ: "p" <>,
    let: "x" := (MethodResolve
      (go.PointerType github_com.mit_pdos.perennial.goose.model.pool.Pool.ty) go!"Get")
      (Pool.state "p") #() in
    if: ("x" =⟨go.any⟩ #GoInterface.nil) &&
        ((![go.FunctionType (go.signature.Signature [] false [go.any])]
            (StructFieldRef (go.GoType.Named go!"sync.Pool" []) go!"New" "p"))
          ≠⟨go.FunctionType (go.signature.Signature [] false [go.any])⟩ #func.nil) then
      (![go.FunctionType (go.signature.Signature [] false [go.any])]
        (StructFieldRef (go.GoType.Named go!"sync.Pool" []) go!"New" "p")) #()
    else "x"

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
       let: "v" := LoadBytes 4 "addr" in
       (if: "v" =⟨go.uint32⟩ #(W32 0) then
          continue: #()
        else
          do: #()
       ) ;;;
       (if: Snd (CmpXchgBytes 4 "addr" ("v", "v" -⟨go.uint32⟩ #(W32 1))) then
          return: #()
        else
          do: #())
    )

def runtime_Semrelease.impl : val :=
  λ: "addr" "_handoff" "_skipframes", AddBytes 4 "addr" #(W32 1) ;; #()

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
