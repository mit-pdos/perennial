/-
Trusted code for the Go `sync/atomic` package (namespace `sync.atomic`, as the
generated package).

The integer operations are `AtomicWord`s on the integer's little-endian bytes (an integer
is a word of byte cells), as plain loads and stores of integers are.

`Value` (Go: `struct { v any }`, whose methods reinterpret `v` as two
`unsafe.Pointer`s, `efaceWords`) is modeled as an atomic cell holding an `any`
(`Value.underlying := go.any`, `Value := GoInterface`; the zero `Value` is the
`nil` interface, as in Go). Its methods:
* `Load`: an atomic load of the cell.
* `Store(val)`, `Swap(new)`: panic if the new value is `nil` (as Go does), else an
  atomic swap. Go also panics when the new value's dynamic type differs from the
  stored value's; the model cannot compare dynamic types, so after swapping into a
  non-empty cell it may panic (`ArbitraryInt`). This over-approximates Go's panics
  (the model behaves as Go up to the first inconsistently typed store, where it
  may panic), so specs of `Store`/`Swap` must show that the cell is empty (`nil`).
* `CompareAndSwap(old, new)`: panics if `new` is `nil`; may panic (as above) if
  `old` or the stored value is non-`nil`, or if they are not comparable (Go's
  `i != old`, through the interface comparison); may fail spuriously (Go's final
  `CompareAndSwapPointer` on the data word fails if another store of an equal
  value happened in between); otherwise an atomic compare-and-swap.
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
  λ: "addr", AtomicWord 8 .load "addr" #()
def StoreUint64.impl : val :=
  λ: "addr" "val", AtomicWord 8 .swap "addr" "val" ;; #()
def SwapUint64.impl : val :=
  λ: "addr" "val", AtomicWord 8 .swap "addr" "val"
def AddUint64.impl : val :=
  λ: "addr" "val", AtomicWord 8 .add "addr" "val"
def CompareAndSwapUint64.impl : val :=
  λ: "addr" "old" "new",
    Snd (AtomicWord 8 .cmpxchg "addr" ("old", "new"))

def LoadInt64.impl : val :=
  λ: "addr", AtomicWord 8 .load "addr" #()
def StoreInt64.impl : val :=
  λ: "addr" "val", AtomicWord 8 .swap "addr" "val" ;; #()
def SwapInt64.impl : val :=
  λ: "addr" "val", AtomicWord 8 .swap "addr" "val"
def AddInt64.impl : val :=
  λ: "addr" "val", AtomicWord 8 .add "addr" "val"
def CompareAndSwapInt64.impl : val :=
  λ: "addr" "old" "new",
    Snd (AtomicWord 8 .cmpxchg "addr" ("old", "new"))

def LoadUint32.impl : val :=
  λ: "addr", AtomicWord 4 .load "addr" #()
def StoreUint32.impl : val :=
  λ: "addr" "val", AtomicWord 4 .swap "addr" "val" ;; #()
def SwapUint32.impl : val :=
  λ: "addr" "val", AtomicWord 4 .swap "addr" "val"
def AddUint32.impl : val :=
  λ: "addr" "val", AtomicWord 4 .add "addr" "val"
def CompareAndSwapUint32.impl : val :=
  λ: "addr" "old" "new",
    Snd (AtomicWord 4 .cmpxchg "addr" ("old", "new"))

def LoadInt32.impl : val :=
  λ: "addr", AtomicWord 4 .load "addr" #()
def StoreInt32.impl : val :=
  λ: "addr" "val", AtomicWord 4 .swap "addr" "val" ;; #()
def SwapInt32.impl : val :=
  λ: "addr" "val", AtomicWord 4 .swap "addr" "val"
def AddInt32.impl : val :=
  λ: "addr" "val", AtomicWord 4 .add "addr" "val"
def CompareAndSwapInt32.impl : val :=
  λ: "addr" "old" "new",
    Snd (AtomicWord 4 .cmpxchg "addr" ("old", "new"))

def LoadPointer.impl : val :=
  λ: "addr", Load "addr"
def StorePointer.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val" ;; #()
def SwapPointer.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val"
def CompareAndSwapPointer.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new")

/-- See the file header. -/
@[reducible] def Value.underlying : go.GoType := go.any

def Value.Load.impl : val :=
  λ: "v" <>, Load "v"

def Value.Store.impl : val :=
  λ: "v" "val",
    if: "val" =⟨go.any⟩ #GoInterface.nil then
      Panic "sync/atomic: store of nil value into Value"
    else
      let: "old" := AtomicSwap "v" "val" in
      if: "old" =⟨go.any⟩ #GoInterface.nil then #()
      else if: ArbitraryInt =⟨go.uint64⟩ #(W64 0) then #()
      else Panic "sync/atomic: store of inconsistently typed value into Value"

def Value.Swap.impl : val :=
  λ: "v" "new",
    if: "new" =⟨go.any⟩ #GoInterface.nil then
      Panic "sync/atomic: swap of nil value into Value"
    else
      let: "old" := AtomicSwap "v" "new" in
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
      let: "cur" := Load "v" in
      (if: "cur" =⟨go.any⟩ #GoInterface.nil then #()
       else if: ArbitraryInt =⟨go.uint64⟩ #(W64 0) then #()
       else Panic "sync/atomic: compare and swap of inconsistently typed value into Value") ;;
      if: "cur" =⟨go.any⟩ "old" then
        (if: ArbitraryInt =⟨go.uint64⟩ #(W64 0) then Snd (CmpXchg "v" "cur" "new")
         else #false)
      else #false

end code

abbrev Value [FfiSyntax] := GoInterface

end sync.atomic

end Perennial
