/-
The filesystem extension of GooseLang [Trusted definitions!].

A node's durable filesystem: a map from file names to contents, with
whole-file operations.

* `ReadOp f` returns the entire contents of the file `f`. Reading a file that
  does not exist is stuck (the model is less defined than Go, whose read
  returns an error).
* `WriteOp (f, data)` replaces the entire contents of the file `f` by `data`,
  creating it if it does not exist. The write is atomic and durable: once it
  returns, a crash keeps it, and a crash never exposes a partial write.
* Crashes (`ExtSemantics.crash`): the files survive unchanged.
* Neither operation changes the heap; file names and contents are passed and
  returned as Go values (`#f`, `#data`).
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

inductive FsOp where
  | ReadOp | WriteOp
deriving DecidableEq, Inhabited

instance : Pos.Countable FsOp where
  encode o := Pos.Countable.encode (match o with | .ReadOp => (0 : Nat) | .WriteOp => 1)
  decode p := match (Pos.Countable.decode p : Option Nat) with
    | some 0 => some .ReadOp | some 1 => some .WriteOp | _ => none
  decode_encode o := by cases o <;> simp [Pos.Countable.decode_encode]

/-- The files of a node: name to contents. -/
abbrev FsState := GMap GoString (List w8)

instance : Inhabited FsState := ⟨∅⟩

/-- The filesystem extension. It has no values of its own and no global state. -/
@[reducible] def fsExt : GooseExt where
  Op := FsOp
  Val := Empty
  LocalState := FsState
  GlobalState := Unit

section fs
variable [GooseExts] [ElemExt fsExt] [GoGlobalContext]

/-- The step relation of the filesystem. -/
def FsStep (op : FsOp) (v : val) (h : GMap Loc (NonAtomic val)) (fs : FsState) (_g : Unit)
    (e' : Expr) (h' : GMap Loc (NonAtomic val)) (fs' : FsState) (_g' : Unit) : Prop :=
  h' = h ∧
  match op with
  | .ReadOp => ∃ (f : GoString) (data : List w8),
      v = #f ∧ fs !! f = some data ∧ e' = Val (#data) ∧ fs' = fs
  | .WriteOp => ∃ (f : GoString) (data : List w8),
      v = PairV (#f) (#data) ∧ e' = Val (#()) ∧ fs' = <[f := data]> fs

end fs

/-- On a crash, the files survive unchanged. -/
instance fs_semantics : ExtSemantics fsExt where
  step := FsStep
  crash fs fs' := fs' = fs

end Perennial
