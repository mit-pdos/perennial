/-
Trusted definitions of `sync` (namespace `sync`, as the generated package).

`copyChecker` and its `check` method are given trusted definitions here (rather
than axiomatized, which would leave `copyChecker.wp_check` unprovable). See
`copyChecker.underlying` below.

`WaitGroup.Add` is a trusted model (`WaitGroup.Add.impl` below): Go's code, as Goose
translates it, except that its counter update is `waitGroupStateAddAssume`, an atomic add
that **assumes the `int32` counter does not overflow**, a model assumption like `append`'s
(`sumAssumeNoOverflowSigned`). See `waitGroupStateAddAssume`.
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.Golang.Defn.Lock
public import Perennial.Golang.Defn
public import Perennial.Code.sync.atomic
public import Perennial.Code.internal.race
public import Perennial.Code.internal.synctest

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

/-- **Model assumption: the `WaitGroup` counter does not overflow.** `WaitGroup.Add(delta)`
adds `uint64(delta) << 32` to `wg.state` atomically (`state.Add`), whose high 32 bits are the
counter, an `int32`; Go panics ("sync: negative WaitGroup counter") when the result is negative,
which includes a counter pushed past `2^31 - 1`. The model assumes that this overflow does not
happen, as `append` assumes its length does not overflow (`sumAssumeNoOverflowSigned`,
`Golang/Defn/Slice.lean`) and `strings.Join` its total length (`TrustedCode/strings.lean`): a
program that keeps `2^31` goroutines pending on one wait group has long run out of memory.

The update is a compare-and-swap loop on `addr` (a `*atomic.Uint64`) adding `x`: it loads the
state `s`, `assume`s that the counter `int32(s >> 32)` plus the counter delta `int32(x >> 32)`
is at most `2^31 - 1` (computed as `int`, so the check cannot overflow), and replaces `s` by
`s + x` if the state is still `s`, else retries; it returns the new state. When the assumption
holds, this is Go's atomic add. The assumption is checked on the value the compare-and-swap
replaces, so it is atomic with the add, as a logically atomic spec of `Add` needs: an `assume`
after Go's atomic add would come too late, since the overflowed counter would already be
visible to other goroutines (whose `Done` would then panic). -/
def waitGroupStateAddAssume : val :=
  rec: "loop" "addr" "x" :=
    let: "s" := (MethodResolve (go.GoType.PointerType sync.atomic.Uint64.ty) go!"Load") "addr" #() in
    assume ((Convert go.int32 go.int (Convert go.uint64 go.int32 ("s" >>⟨go.uint64⟩ #(W64 32))) +⟨go.int⟩
        Convert go.int32 go.int (Convert go.uint64 go.int32 ("x" >>⟨go.uint64⟩ #(W64 32))))
      ≤⟨go.int⟩ #(W64 (2 ^ 31 - 1))) ;;
    if: (MethodResolve (go.GoType.PointerType sync.atomic.Uint64.ty) go!"CompareAndSwap") "addr" "s"
          ("s" +⟨go.uint64⟩ "x")
    then "s" +⟨go.uint64⟩ "x"
    else "loop" "addr" "x"

/-- Go's `WaitGroup.Add` (`waitgroup.go:77:22`), as Goose translates it (the generated term,
copied verbatim), with one change: `wg.state.Add(uint64(delta) << 32)` is
`waitGroupStateAddAssume`, the add that assumes the counter does not overflow. Parameterized by
the package's own names, which are defined after this file (`Code/sync.lean`): the
`WaitGroup` type `wgTy`, `waitGroupBubbleFlag`, and the function names `runtime_Semrelease` and
`fatal` (`WaitGroup.Add.impl` instantiates them; `sync.WaitGroup.Add.impl_eq` restates it with the
generated names). -/
noncomputable def WaitGroup.Add.implWith (wgTy : go.GoType) (bubbleFlag : val) (semrelease fatal_ : GoString) :
    val :=
  (LamV "wg"
  (Lam "delta"
  (App (Val wrapDefer)
  (Lam "$defer"
  (Let "wg" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType wgTy)))) (Var "wg"))
  (Let "delta" (App (Val (GoInstruction (GoAlloc go.int))) (Var "delta"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #false)
  (Let "bubbled" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoOp GoShiftl go.uint64))) (Pair (App (Val (GoInstruction (Convert go.int go.uint64))) (App (Val (GoInstruction (GoLoad go.int))) (Var "delta"))) (App (Val (GoInstruction (Convert go.untypedInt go.uint64))) (Val #(32 : Int)))))
  (App (App (Val waitGroupStateAddAssume) (App (Val (GoInstruction (StructFieldRef wgTy go!"state"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType wgTy)))) (Var "wg")))) (Var "$a0")))
  (Let "state" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.uint64 go.int32))) (App (Val (GoInstruction (GoOp GoShiftr go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "state")) (App (Val (GoInstruction (Convert go.untypedInt go.uint64))) (Val #(32 : Int))))))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.int32))) (App (Val (GoInstruction (GoZeroVal go.int32))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.uint64 go.uint32))) (App (Val (GoInstruction (GoOp GoAnd go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "state")) (Val #(W64 2147483647)))))
  (Let "w" (App (Val (GoInstruction (GoAlloc go.uint32))) (App (Val (GoInstruction (GoZeroVal go.uint32))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (App (Val doFor) (Lam BAnon
  (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint32))) (Pair (App (Val (GoInstruction (GoLoad go.uint32))) (Var "w")) (Val #(W32 0))))))) (Lam BAnon
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (StructFieldRef wgTy go!"sema"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType wgTy)))) (Var "wg")))
  (Let "$a1" (Val #false)
  (Let "$a2" (Val #(W64 0))
  (App (App (App (App (Val (GoInstruction (FuncResolve semrelease []))) (Val #())) (Var "$a0")) (Var "$a1")) (Var "$a2"))))))))
  (Lam BAnon
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint32))) (Pair (Var "w") (App (Val (GoInstruction (GoOp GoSub go.uint32))) (Pair (App (Val (GoInstruction (GoLoad go.uint32))) (Var "w")) (Val #(W32 1)))))))))))
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "bubbled"))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType wgTy)))) (Var "wg"))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.internal.synctest.Disassociate [wgTy]))) (Val #())) (Var "$a0"))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (Let "$a0" (Val #(W64 0))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.sync.atomic.Uint64.ty) go!"Store"))) (App (Val (GoInstruction (StructFieldRef wgTy go!"state"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType wgTy)))) (Var "wg")))) (Var "$a0")))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.sync.atomic.Uint64.ty) go!"Load"))) (App (Val (GoInstruction (StructFieldRef wgTy go!"state"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType wgTy)))) (Var "wg")))) (Val #())) (App (Val (GoInstruction (GoLoad go.uint64))) (Var "state"))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (Convert go.string (go.GoType.InterfaceType [])))) (Val #(go!"sync: WaitGroup misuse: Add called concurrently with Wait")))
  (App (App (Val (GoInstruction (FuncResolve go.panic []))) (Val #())) (Var "$a0"))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoGt go.int32))) (Pair (App (Val (GoInstruction (GoLoad go.int32))) (Var "v")) (Val #(W32 0)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.uint32))) (Pair (App (Val (GoInstruction (GoLoad go.uint32))) (Var "w")) (Val #(W32 0))))))
  (App (Val doReturn)
  (Val #()))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint32))) (Pair (App (Val (GoInstruction (GoLoad go.uint32))) (Var "w")) (Val #(W32 0))))) (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "delta")) (Val #(W64 0)))) (Val #false)) (App (Val (GoInstruction (GoOp GoEquals go.int32))) (Pair (App (Val (GoInstruction (GoLoad go.int32))) (Var "v")) (App (Val (GoInstruction (Convert go.int go.int32))) (App (Val (GoInstruction (GoLoad go.int))) (Var "delta"))))) (Val #false)))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (Convert go.string (go.GoType.InterfaceType [])))) (Val #(go!"sync: WaitGroup misuse: Add called concurrently with Wait")))
  (App (App (Val (GoInstruction (FuncResolve go.panic []))) (Val #())) (Var "$a0"))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.int32))) (Pair (App (Val (GoInstruction (GoLoad go.int32))) (Var "v")) (Val #(W32 0)))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (Convert go.string (go.GoType.InterfaceType [])))) (Val #(go!"sync: negative WaitGroup counter")))
  (App (App (Val (GoInstruction (FuncResolve go.panic []))) (Val #())) (Var "$a0"))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (If (Val _root_.Perennial.internal.race.Enabled) (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "delta")) (Val #(W64 0)))) (Val #false)) (App (Val (GoInstruction (GoOp GoEquals go.int32))) (Pair (App (Val (GoInstruction (GoLoad go.int32))) (Var "v")) (App (Val (GoInstruction (Convert go.int go.int32))) (App (Val (GoInstruction (GoLoad go.int))) (Var "delta"))))) (Val #false)))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (Convert (go.GoType.PointerType go.uint32) «unsafe».Pointer))) (App (Val (GoInstruction (StructFieldRef wgTy go!"sema"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType wgTy)))) (Var "wg"))))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.internal.race.Read []))) (Val #())) (Var "$a0"))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint32))) (Pair (Var "w") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int32))) (Pair (Var "v") (Var "$r0")))))))))
  (If (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair (App (Val (GoInstruction (GoOp GoAnd go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "state")) (App (Val (GoInstruction (Convert go.untypedInt go.uint64))) (Val bubbleFlag)))) (Val #(W64 0))))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "bubbled"))) (Val #false))
  (App (Val doExecute)
  (Let "$a0" (Val #(go!"sync: WaitGroup.Add called from inside and outside synctest bubble"))
  (App (App (Val (GoInstruction (FuncResolve fatal_ []))) (Val #())) (Var "$a0"))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "state") (Var "$r0")))))))))
  (If (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.internal.synctest.IsInBubble []))) (Val #())) (Val #()))
  (Let "$sw" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType wgTy)))) (Var "wg"))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.internal.synctest.Associate [wgTy]))) (Val #())) (Var "$a0")))
  (If (App (Val (GoInstruction (GoOp GoEquals _root_.Perennial.internal.synctest.Association.ty))) (Pair (Var "$sw") (Val _root_.Perennial.internal.synctest.Unbubbled)))
  (App (Val doExecute)
  (Val #()))
  (If (App (Val (GoInstruction (GoOp GoEquals _root_.Perennial.internal.synctest.Association.ty))) (Pair (Var "$sw") (Val _root_.Perennial.internal.synctest.OtherBubble)))
  (App (Val doExecute)
  (Let "$a0" (Val #(go!"sync: WaitGroup.Add called from multiple synctest bubbles"))
  (App (App (Val (GoInstruction (FuncResolve fatal_ []))) (Val #())) (Var "$a0"))))
  (If (App (Val (GoInstruction (GoOp GoEquals _root_.Perennial.internal.synctest.Association.ty))) (Pair (Var "$sw") (Val _root_.Perennial.internal.synctest.CurrentBubble)))
  (Let "$r0" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (Convert go.untypedInt go.uint64))) (Val bubbleFlag))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.sync.atomic.Uint64.ty) go!"Or"))) (App (Val (GoInstruction (StructFieldRef wgTy go!"state"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType wgTy)))) (Var "wg")))) (Var "$a0")))
  (Let "state" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "state")) (Val #(W64 0))))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair (App (Val (GoInstruction (GoOp GoAnd go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "state")) (App (Val (GoInstruction (Convert go.untypedInt go.uint64))) (Val bubbleFlag)))) (Val #(W64 0)))) (Val #false)))
  (App (Val doExecute)
  (Let "$a0" (Val #(go!"sync: WaitGroup.Add called from inside and outside synctest bubble"))
  (App (App (Val (GoInstruction (FuncResolve fatal_ []))) (Val #())) (Var "$a0"))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "state") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "bubbled") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "bubbled") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (Val _root_.Perennial.internal.race.Enabled))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (Let "$f" (App (Val (GoInstruction (FuncResolve _root_.Perennial.internal.race.Enable []))) (Val #()))
  (App (Val (GoInstruction (GoStore deferType))) (Pair (Var "$defer") (Let "$oldf" (App (Val (GoInstruction (GoLoad deferType))) (Var "$defer"))
  (Lam BAnon
  (Seq (App (Var "$f") (Val #()))
  (App (Var "$oldf") (Val #())))))))))))
  (App (Val doExecute)
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.internal.race.Disable []))) (Val #())) (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "delta")) (Val #(W64 0)))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (Convert (go.GoType.PointerType wgTy) «unsafe».Pointer))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType wgTy)))) (Var "wg")))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.internal.race.ReleaseMerge []))) (Val #())) (Var "$a0"))))
  (App (Val doExecute)
  (Val #()))))
  (App (Val doExecute)
  (Val #())))))))))))

/-- `WaitGroup.Add`: see `WaitGroup.Add.implWith` and `waitGroupStateAddAssume`. -/
noncomputable def WaitGroup.Add.impl : val :=
  WaitGroup.Add.implWith (go.GoType.Named go!"sync.WaitGroup" []) #(2147483648 : Int)
    go!"sync.runtime_Semrelease" go!"sync.fatal"

end code

/-- See `copyChecker.underlying`. -/
abbrev copyChecker := Loc

abbrev Mutex := Bool

end sync

end Perennial
