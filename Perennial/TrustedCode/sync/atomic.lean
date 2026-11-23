/-
Trusted code for the Go `sync/atomic` package (namespace `sync.atomic`, as the
generated package).

`Value` (Go: `struct { v any }`) is translated by goose. Its methods are trusted:
they call `runtime_procPin`/`runtime_procUnpin` (external functions, which goose
rejects) and reinterpret the field `v` as two `unsafe.Pointer` words
(`(*efaceWords)(unsafe.Pointer(v))`), a memory layout the semantics does not
have (an interface value is one heap value). They are modeled as atomic
operations on the field `v` of the receiver; the zero `Value` holds
the `nil` interface, as in Go:
* `Load`: an atomic load of `v`.
* `Store(val)`, `Swap(new)` (value.go, lines 47-83 and 90-127): if the new value is `nil`,
  `Panic`; else an atomic swap of `v`, then `Panic` if the old value is non-`nil` and of another
  dynamic type than the new one (`TypeOfEq`). Go checks the type before it stores the data
  word, and the type word never changes once set; the model checks after its swap, which only
  differs from Go in executions where the thread is stuck anyway (and checking before the swap
  would not be atomic).
* `CompareAndSwap(old, new)` (lines 134-188): `Panic` if `new` is `nil`, or if `old` is
  non-`nil` and of another dynamic type than `new` (line 141). Then a load of `v`, `cur`:
  - `cur` empty: `false` if `old` is non-`nil` (line 147); else a compare-and-swap from `nil`,
    whose failure (another first store won, line 60) is Go's next iteration: `Panic` if the
    value now stored has another type than `new`, else `false` (`i != old`, line 183);
  - `cur` non-empty: `Panic` if its type is not `new`'s (line 171); `false` if `cur != old`
    (Go's interface comparison, which panics on equal non-comparable dynamic types, line 183);
    else a compare-and-swap of `v` from `cur`, which may also fail spuriously (`ArbitraryInt`):
    Go's final `CompareAndSwapPointer` on the data word fails if another store, even of an
    equal value, happened since the load (line 186).

A copy of a `Value` (Go forbids copying one after first use) reads the cell in one step, whereas
gc reads its two words separately and, racing with a first store, can see them torn.

The integer functions (`LoadUint64`, ..., `CompareAndSwapInt32`) are the byte atomics of
their width (`LoadBytes 8`, ...): each acts on the integer's little-endian bytes in one step,
at any address. A misaligned atomic load or store can tear in gc (`docs/KNOWN_LIMITATIONS.md`);
only `unsafe` can produce a misaligned integer.

`Panic msg` is stuck (`wp_PanicOp`), whereas Go's panics here are ordinary,
recoverable panics; and a `nil` receiver, where Go panics on the dereference,
is stuck too (there is no points-to for the field). So the model is less
defined than Go on all these paths (a proof must show they are unreachable), and
agrees with Go elsewhere.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace sync.atomic
section code
variable [GooseExts] [GoGlobalContext]

def LoadUint64.impl : val :=
  λ: "addr", LoadBytes 8 "addr"
def StoreUint64.impl : val :=
  λ: "addr" "val", SwapBytes 8 "addr" "val" ;; #()
def SwapUint64.impl : val :=
  λ: "addr" "val", SwapBytes 8 "addr" "val"
def AddUint64.impl : val :=
  λ: "addr" "val", AddBytes 8 "addr" "val"
def CompareAndSwapUint64.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchgBytes 8 "addr" ("old", "new"))

def LoadInt64.impl : val :=
  λ: "addr", LoadBytes 8 "addr"
def StoreInt64.impl : val :=
  λ: "addr" "val", SwapBytes 8 "addr" "val" ;; #()
def SwapInt64.impl : val :=
  λ: "addr" "val", SwapBytes 8 "addr" "val"
def AddInt64.impl : val :=
  λ: "addr" "val", AddBytes 8 "addr" "val"
def CompareAndSwapInt64.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchgBytes 8 "addr" ("old", "new"))

def LoadUint32.impl : val :=
  λ: "addr", LoadBytes 4 "addr"
def StoreUint32.impl : val :=
  λ: "addr" "val", SwapBytes 4 "addr" "val" ;; #()
def SwapUint32.impl : val :=
  λ: "addr" "val", SwapBytes 4 "addr" "val"
def AddUint32.impl : val :=
  λ: "addr" "val", AddBytes 4 "addr" "val"
def CompareAndSwapUint32.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchgBytes 4 "addr" ("old", "new"))

def LoadInt32.impl : val :=
  λ: "addr", LoadBytes 4 "addr"
def StoreInt32.impl : val :=
  λ: "addr" "val", SwapBytes 4 "addr" "val" ;; #()
def SwapInt32.impl : val :=
  λ: "addr" "val", SwapBytes 4 "addr" "val"
def AddInt32.impl : val :=
  λ: "addr" "val", AddBytes 4 "addr" "val"
def CompareAndSwapInt32.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchgBytes 4 "addr" ("old", "new"))

def LoadPointer.impl : val :=
  λ: "addr", Load "addr"
def StorePointer.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val" ;; #()
def SwapPointer.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val"
def CompareAndSwapPointer.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new")

def Value.Load.impl : val :=
  λ: "v" <>, Load (StructFieldRef (go.GoType.Named go!"sync/atomic.Value" []) go!"v" "v")

def Value.Store.impl : val :=
  λ: "v" "val",
    if: "val" =⟨go.any⟩ #GoInterface.nil then
      Panic "sync/atomic: store of nil value into Value"
    else
      let: "old" := AtomicSwap (StructFieldRef (go.GoType.Named go!"sync/atomic.Value" []) go!"v" "v") "val" in
      if: "old" =⟨go.any⟩ #GoInterface.nil then #()
      else if: TypeOfEq ("old", "val") then #()
      else Panic "sync/atomic: store of inconsistently typed value into Value"

def Value.Swap.impl : val :=
  λ: "v" "new",
    if: "new" =⟨go.any⟩ #GoInterface.nil then
      Panic "sync/atomic: swap of nil value into Value"
    else
      let: "old" := AtomicSwap (StructFieldRef (go.GoType.Named go!"sync/atomic.Value" []) go!"v" "v") "new" in
      if: "old" =⟨go.any⟩ #GoInterface.nil then "old"
      else if: TypeOfEq ("old", "new") then "old"
      else Panic "sync/atomic: swap of inconsistently typed value into Value"

def Value.CompareAndSwap.impl : val :=
  λ: "v" "old" "new",
    if: "new" =⟨go.any⟩ #GoInterface.nil then
      Panic "sync/atomic: compare and swap of nil value into Value"
    else
      (if: "old" =⟨go.any⟩ #GoInterface.nil then #()
       else if: TypeOfEq ("old", "new") then #()
       else Panic "sync/atomic: compare and swap of inconsistently typed values") ;;
      let: "cur" := Load (StructFieldRef (go.GoType.Named go!"sync/atomic.Value" []) go!"v" "v") in
      if: "cur" =⟨go.any⟩ #GoInterface.nil then
        if: "old" =⟨go.any⟩ #GoInterface.nil then
          let: "r" := CmpXchg (StructFieldRef (go.GoType.Named go!"sync/atomic.Value" []) go!"v" "v") #GoInterface.nil "new" in
          if: Snd "r" then #true
          else if: TypeOfEq (Fst "r", "new") then #false
          else Panic "sync/atomic: compare and swap of inconsistently typed value into Value"
        else #false
      else
        (if: TypeOfEq ("cur", "new") then #()
         else Panic "sync/atomic: compare and swap of inconsistently typed value into Value") ;;
        if: "cur" =⟨go.any⟩ "old" then
          (if: ArbitraryInt =⟨go.uint64⟩ #(W64 0) then Snd (CmpXchg (StructFieldRef (go.GoType.Named go!"sync/atomic.Value" []) go!"v" "v") "cur" "new")
           else #false)
        else #false

/-- `Pointer[T].Load` (`return (*T)(LoadPointer(&x.v))`) without the conversion of the loaded
`unsafe.Pointer` to `*T`, which the semantics makes stuck for a non-plain `T` (it does not track
where a pointer came from). `x.v` only ever holds a `*T`: `Store`, `Swap` and
`CompareAndSwap` are the only writers. -/
def Pointer.Load.impl (T : go.GoType) : val :=
  λ: "x" <>,
    (FuncResolve go!"sync/atomic.LoadPointer" []) #()
      (StructFieldRef (go.GoType.Named go!"sync/atomic.Pointer" [T]) go!"v" "x")

/-- `Pointer[T].Swap` (`return (*T)(SwapPointer(&x.v, unsafe.Pointer(new)))`) without the
conversion of the old `unsafe.Pointer` to `*T`, as for `Pointer.Load`. -/
def Pointer.Swap.impl (T : go.GoType) : val :=
  λ: "x" "new",
    (FuncResolve go!"sync/atomic.SwapPointer" []) #()
      (StructFieldRef (go.GoType.Named go!"sync/atomic.Pointer" [T]) go!"v" "x")
      (Convert (go.PointerType T) «unsafe».Pointer "new")

end code

end sync.atomic

end Perennial
