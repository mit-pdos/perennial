/-
Trusted code for the Go `sync/atomic` package (namespace `sync.atomic`, as the
generated package).

The integer operations are the atomic operations of the base language (`LoadN`, `SwapN`,
`AddN`, `CmpXchgN`) on the integer's little-endian bytes (`Encoding.word`), the pointer
operations on a pointer's cells (`Encoding.cell 8`). They are stuck at an address that is
not aligned to the size: on amd64 such an access is not atomic (it may tear across a
cache line), and Go requires the alignment (`sync/atomic`, "Bugs"; a misaligned 64-bit
atomic faults on several platforms).

`Value` (Go: `struct { v any }`) is translated by goose. Its methods are trusted:
they call `runtime_procPin`/`runtime_procUnpin` (external functions, which goose
rejects) and reinterpret the field `v` as two `unsafe.Pointer` words
(`(*efaceWords)(unsafe.Pointer(v))`), a memory layout the semantics does not
have (an interface value is one value in its 16 cells, `Encoding.cell 16`). They are modeled as atomic
operations on the field `v` of the receiver; the zero `Value` holds
the `nil` interface, as in Go:
* `Load`: an atomic load of `v`.
* `Store(val)`, `Swap(new)`: if the new value is `nil`, `Panic` (Go panics); else an
  atomic swap of `v`. Go also panics when the new value's dynamic type differs
  from the stored value's; the model cannot compare dynamic types, so after
  swapping into a non-empty cell it may `Panic` (`ArbitraryInt`), even when the
  types agree. So specs of `Store`/`Swap` must show that the cell is empty (`nil`).
* `CompareAndSwap(old, new)`: `Panic` if `new` is `nil`; may `Panic` (as above) if
  `old` or the stored value is non-`nil`, or if they are not comparable (Go's
  `i != old`, through the interface comparison); may fail spuriously (Go's final
  `CompareAndSwapPointer` on the data word fails if another store of an equal
  value happened in between); otherwise an atomic compare-and-swap of `v`.

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
variable [FfiSyntax] [GoGlobalContext]

def LoadUint64.impl : val :=
  λ: "addr", LoadN (.word 8) "addr"
def StoreUint64.impl : val :=
  λ: "addr" "val", SwapN (.word 8) "addr" "val" ;; #()
def SwapUint64.impl : val :=
  λ: "addr" "val", SwapN (.word 8) "addr" "val"
def AddUint64.impl : val :=
  λ: "addr" "val", AddN (.word 8) "addr" "val"
def CompareAndSwapUint64.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchgN (.word 8) "addr" ("old", "new"))

def LoadInt64.impl : val :=
  λ: "addr", LoadN (.word 8) "addr"
def StoreInt64.impl : val :=
  λ: "addr" "val", SwapN (.word 8) "addr" "val" ;; #()
def SwapInt64.impl : val :=
  λ: "addr" "val", SwapN (.word 8) "addr" "val"
def AddInt64.impl : val :=
  λ: "addr" "val", AddN (.word 8) "addr" "val"
def CompareAndSwapInt64.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchgN (.word 8) "addr" ("old", "new"))

def LoadUint32.impl : val :=
  λ: "addr", LoadN (.word 4) "addr"
def StoreUint32.impl : val :=
  λ: "addr" "val", SwapN (.word 4) "addr" "val" ;; #()
def SwapUint32.impl : val :=
  λ: "addr" "val", SwapN (.word 4) "addr" "val"
def AddUint32.impl : val :=
  λ: "addr" "val", AddN (.word 4) "addr" "val"
def CompareAndSwapUint32.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchgN (.word 4) "addr" ("old", "new"))

def LoadInt32.impl : val :=
  λ: "addr", LoadN (.word 4) "addr"
def StoreInt32.impl : val :=
  λ: "addr" "val", SwapN (.word 4) "addr" "val" ;; #()
def SwapInt32.impl : val :=
  λ: "addr" "val", SwapN (.word 4) "addr" "val"
def AddInt32.impl : val :=
  λ: "addr" "val", AddN (.word 4) "addr" "val"
def CompareAndSwapInt32.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchgN (.word 4) "addr" ("old", "new"))

def LoadPointer.impl : val :=
  λ: "addr", LoadN (.cell 8) "addr"
def StorePointer.impl : val :=
  λ: "addr" "val", SwapN (.cell 8) "addr" "val" ;; #()
def SwapPointer.impl : val :=
  λ: "addr" "val", SwapN (.cell 8) "addr" "val"
def CompareAndSwapPointer.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchgN (.cell 8) "addr" ("old", "new"))

def Value.Load.impl : val :=
  λ: "v" <>, LoadN (.cell 16) (StructFieldRef (go.GoType.Named go!"sync/atomic.Value" []) go!"v" "v")

def Value.Store.impl : val :=
  λ: "v" "val",
    if: "val" =⟨go.any⟩ #GoInterface.nil then
      Panic "sync/atomic: store of nil value into Value"
    else
      let: "old" := SwapN (.cell 16) (StructFieldRef (go.GoType.Named go!"sync/atomic.Value" []) go!"v" "v") "val" in
      if: "old" =⟨go.any⟩ #GoInterface.nil then #()
      else if: ArbitraryInt =⟨go.uint64⟩ #(W64 0) then #()
      else Panic "sync/atomic: store of inconsistently typed value into Value"

def Value.Swap.impl : val :=
  λ: "v" "new",
    if: "new" =⟨go.any⟩ #GoInterface.nil then
      Panic "sync/atomic: swap of nil value into Value"
    else
      let: "old" := SwapN (.cell 16) (StructFieldRef (go.GoType.Named go!"sync/atomic.Value" []) go!"v" "v") "new" in
      if: "old" =⟨go.any⟩ #GoInterface.nil then "old"
      else if: ArbitraryInt =⟨go.uint64⟩ #(W64 0) then "old"
      else Panic "sync/atomic: swap of inconsistently typed value into Value"

def Value.CompareAndSwap.impl : val :=
  λ: "v" "old" "new",
    if: "new" =⟨go.any⟩ #GoInterface.nil then
      Panic "sync/atomic: compare and swap of nil value into Value"
    else
      (if: "old" =⟨go.any⟩ #GoInterface.nil then #()
       else if: ArbitraryInt =⟨go.uint64⟩ #(W64 0) then #()
       else Panic "sync/atomic: compare and swap of inconsistently typed values") ;;
      let: "cur" := LoadN (.cell 16) (StructFieldRef (go.GoType.Named go!"sync/atomic.Value" []) go!"v" "v") in
      (if: "cur" =⟨go.any⟩ #GoInterface.nil then #()
       else if: ArbitraryInt =⟨go.uint64⟩ #(W64 0) then #()
       else Panic "sync/atomic: compare and swap of inconsistently typed value into Value") ;;
      if: "cur" =⟨go.any⟩ "old" then
        (if: ArbitraryInt =⟨go.uint64⟩ #(W64 0) then Snd (CmpXchgN (.cell 16) (StructFieldRef (go.GoType.Named go!"sync/atomic.Value" []) go!"v" "v") ("cur", "new"))
         else #false)
      else #false

end code

end sync.atomic

end Perennial
