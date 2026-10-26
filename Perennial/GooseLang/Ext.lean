/-
GooseLang extensions [Trusted definitions!].

An extension adds primitive operations to GooseLang, with state of their own: a
durable disk, a network, clocks. Extensions compose: a program runs against a
closed list of extensions, in the style of iris's `BundledGFunctors`.

* `GooseExt` is one extension: the types of its operations (`Op`), of the opaque
  values its operations return (`Val`), and of its per-node (`LocalState`) and
  shared (`GlobalState`) state.
* `GooseExts` is the closed list `exts` of extensions that a program runs
  against. Code and proofs are generic over it. Its operations `ExtsOp exts` are
  the sum of the extensions' operations (`ExternalOp`), its values `ExtsVal exts`
  the sum of their values (`ExtV`), and its states the products of their
  states (`state.world`, `GlobalState.globalWorld`).
* `ElemExt E` says that `E` is in the list (as iris's `ElemG`): code and proofs
  about one extension assume only that, and the list is fixed when a program
  is closed off by an adequacy theorem.
* The semantics of an extension (`ExtSemantics`, `Lang.lean`) and its ghost
  state (`ExtInterp`, `Lifting.lean`) are classes on the extension, and the
  closed list's (`GooseSemantics`, `GooseInterp`) are tuples of them, one per
  extension of the list (`ExtTuple`).

`ExtIn E l` is a position of `E` in `l`. The operations, values and states of
`l` are nested sums and products along `l`, so that a position injects into
them and projects out of them by recursion, without casts.
-/
module

public import Perennial.Std.Countable

@[expose] public section

namespace Perennial

/-- An extension of GooseLang: its operations, values and state. -/
structure GooseExt where
  /-- The primitive operations (`ExternalOp`). -/
  Op : Type
  /-- The opaque values the operations return (`ExtV`), e.g. sockets. -/
  Val : Type
  /-- The per-node state, e.g. a disk. -/
  LocalState : Type
  /-- The state shared between nodes, e.g. the network. -/
  GlobalState : Type
  [op_countable : Pos.Countable Op]
  [val_countable : Pos.Countable Val]
  [localState_inhabited : Inhabited LocalState]
  [globalState_inhabited : Inhabited GlobalState]

attribute [instance] GooseExt.op_countable GooseExt.val_countable
  GooseExt.localState_inhabited GooseExt.globalState_inhabited

/-- A position of the extension `E` in the list `l`. -/
inductive ExtIn (E : GooseExt) : List GooseExt → Type 1
  | here {l : List GooseExt} : ExtIn E (E :: l)
  | there {E' : GooseExt} {l : List GooseExt} : ExtIn E l → ExtIn E (E' :: l)

/-! ## Tuples over a list of extensions -/

universe u

/-- A `C E` for each extension `E` of `l`. -/
def ExtTuple (C : GooseExt → Type u) : List GooseExt → Type u
  | [] => PUnit
  | E :: l => C E × ExtTuple C l

instance ExtTuple.inhabited {C : GooseExt → Type u} [∀ E, Inhabited (C E)] :
    (l : List GooseExt) → Inhabited (ExtTuple C l)
  | [] => ⟨PUnit.unit⟩
  | E :: l => have := ExtTuple.inhabited (C := C) l; inferInstanceAs (Inhabited (C E × _))

namespace ExtIn
variable {E : GooseExt} {C : GooseExt → Type u}

/-- The component of `E`. -/
def get : {l : List GooseExt} → ExtIn E l → ExtTuple C l → C E
  | _ :: _, .here, t => t.1
  | _ :: _, .there m, t => m.get t.2

/-- Replace the component of `E`. -/
def set : {l : List GooseExt} → ExtIn E l → ExtTuple C l → C E → ExtTuple C l
  | _ :: _, .here, t, x => (x, t.2)
  | _ :: _, .there m, t, x => (t.1, m.set t.2 x)

@[simp] theorem get_set {l : List GooseExt} (m : ExtIn E l) (t : ExtTuple C l) (x : C E) :
    m.get (m.set t x) = x := by
  induction m with
  | here => rfl
  | there m ih => exact ih _

@[simp] theorem set_get {l : List GooseExt} (m : ExtIn E l) (t : ExtTuple C l) :
    m.set t (m.get t) = t := by
  induction m with
  | here => rfl
  | there m ih => exact congrArg (t.1, ·) (ih _)

end ExtIn

/-! ## Operations and values of a list of extensions -/

/-- The operations of the extensions of `l`. -/
def ExtsOp : List GooseExt → Type
  | [] => Empty
  | E :: l => E.Op ⊕ ExtsOp l

/-- The values of the extensions of `l`. -/
def ExtsVal : List GooseExt → Type
  | [] => Empty
  | E :: l => E.Val ⊕ ExtsVal l

/-- The local states of the extensions of `l`. -/
abbrev ExtsLocalState (l : List GooseExt) : Type := ExtTuple GooseExt.LocalState l

/-- The global states of the extensions of `l`. -/
abbrev ExtsGlobalState (l : List GooseExt) : Type := ExtTuple GooseExt.GlobalState l

instance countableEmpty : Pos.Countable Empty where
  encode e := e.elim
  decode _ := none
  decode_encode e := e.elim

noncomputable instance ExtsOp.countable : (l : List GooseExt) → Pos.Countable (ExtsOp l)
  | [] => countableEmpty
  | E :: l => have := ExtsOp.countable l; inferInstanceAs (Pos.Countable (E.Op ⊕ _))

noncomputable instance ExtsVal.countable : (l : List GooseExt) → Pos.Countable (ExtsVal l)
  | [] => countableEmpty
  | E :: l => have := ExtsVal.countable l; inferInstanceAs (Pos.Countable (E.Val ⊕ _))

namespace ExtIn
variable {E : GooseExt}

/-- The operation `o` of `E`, as an operation of `l`. -/
def injOp : {l : List GooseExt} → ExtIn E l → E.Op → ExtsOp l
  | _ :: _, .here, o => .inl o
  | _ :: _, .there m, o => .inr (m.injOp o)

/-- The value `v` of `E`, as a value of `l`. -/
def injVal : {l : List GooseExt} → ExtIn E l → E.Val → ExtsVal l
  | _ :: _, .here, v => .inl v
  | _ :: _, .there m, v => .inr (m.injVal v)

theorem injVal_inj {l : List GooseExt} (m : ExtIn E l) {v v' : E.Val}
    (h : m.injVal v = m.injVal v') : v = v' := by
  induction m with
  | here => exact Sum.inl.inj h
  | there m ih => exact ih (Sum.inr.inj h)

end ExtIn

/-- The extension of an operation of `l`, its position and the operation. -/
def ExtsOp.decode : (l : List GooseExt) → ExtsOp l → (E : GooseExt) × ExtIn E l × E.Op
  | [], o => o.elim
  | E :: _, .inl o => ⟨E, .here, o⟩
  | _ :: l, .inr o =>
    let d := ExtsOp.decode l o
    ⟨d.1, .there d.2.1, d.2.2⟩

@[simp] theorem ExtsOp.decode_injOp {E : GooseExt} {l : List GooseExt} (m : ExtIn E l)
    (o : E.Op) : ExtsOp.decode l (m.injOp o) = ⟨E, m, o⟩ := by
  induction m with
  | here => rfl
  | @there E' l m ih =>
    show (⟨(ExtsOp.decode l (m.injOp o)).1, .there (ExtsOp.decode l (m.injOp o)).2.1,
      (ExtsOp.decode l (m.injOp o)).2.2⟩ : (E : GooseExt) × ExtIn E (E' :: l) × E.Op) = _
    rw [ih]

/-! ## The closed list of extensions -/

/-- The list of extensions that a program runs against. Code and proofs are
generic over it; it is fixed by the instance of an adequacy theorem. -/
class GooseExts where
  exts : List GooseExt

export GooseExts (exts)

/-- The extension `E` is in the list of extensions (as iris's `ElemG`). -/
class ElemExt [GooseExts] (E : GooseExt) where
  mem : ExtIn E exts

section elem
variable [GooseExts]

/-- The operation `o` of the extension `E`. -/
abbrev extOp (E : GooseExt) [ElemExt E] (o : E.Op) : ExtsOp exts := ElemExt.mem.injOp o

/-- The value `v` of the extension `E`. -/
abbrev extVal (E : GooseExt) [ElemExt E] (v : E.Val) : ExtsVal exts := ElemExt.mem.injVal v

/-- The local state of the extension `E`. -/
abbrev extLocal (E : GooseExt) [ElemExt E] (w : ExtsLocalState exts) : E.LocalState :=
  ElemExt.mem.get w

/-- The global state of the extension `E`. -/
abbrev extGlobal (E : GooseExt) [ElemExt E] (w : ExtsGlobalState exts) : E.GlobalState :=
  ElemExt.mem.get w

end elem

end Perennial
