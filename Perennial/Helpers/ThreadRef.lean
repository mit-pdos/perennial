/-
Mutable state of a tactic that must not be shared between the declarations of a
file: `ThreadRef`, a mutable cell per thread.

Lean elaborates the bodies of a file's declarations in parallel (`Elab.async`),
each on one thread from its start to its end, in the same process. A tactic's
state kept in a plain `IO.Ref` (`initialize r : IO.Ref α`) is therefore shared by
the tactics running in other declarations at the same time: they read it, reset
it and add to it, so what a tactic does depends on the scheduling (a full build
on a loaded machine fails where the same file built alone passes). Such state
is a `ThreadRef` instead; a flag that only scopes a nested call is better an
option (`withOptions`), which is local to the call.
-/
module

public import Lean

@[expose] public section

namespace Perennial

/-- A mutable cell per thread (see the module docstring), with the operations of
`IO.Ref`. A thread's cell starts as `init`. -/
structure ThreadRef (α : Type) where
  cells : IO.Ref (Std.HashMap UInt64 α)
  init : α

namespace ThreadRef

variable {α : Type}

instance [Nonempty α] : Nonempty (ThreadRef α) :=
  ⟨⟨Classical.ofNonempty, Classical.ofNonempty⟩⟩

def new (init : α) : BaseIO (ThreadRef α) := do
  return { cells := ← IO.mkRef {}, init }

/-- This thread's value. -/
def get (r : ThreadRef α) : BaseIO α := do
  let tid ← IO.getTID
  return (← r.cells.get).getD tid r.init

def set (r : ThreadRef α) (a : α) : BaseIO Unit := do
  let tid ← IO.getTID
  r.cells.modify (·.insert tid a)

/-- Update this thread's value (in place: it is taken out of the map first). -/
def modify (r : ThreadRef α) (f : α → α) : BaseIO Unit := do
  let tid ← IO.getTID
  r.cells.modify fun m =>
    let a := m.getD tid r.init
    let m := m.erase tid
    m.insert tid (f a)

end ThreadRef

end Perennial
