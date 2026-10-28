/-
GooseLang extensions [Trusted definitions!].

An extension adds primitive operations to GooseLang, with state of their own: a
durable disk, a network, clocks. Extensions compose: a program runs against a
closed list of extensions, in the style of iris's `BundledGFunctors`.

* `GooseExt` is one extension: its name, the type of the opaque values its
  operations return (`Val`), and the types of its per-node (`LocalState`) and
  shared (`GlobalState`) state. Its operations are named by strings
  (`ExternalOp ext op e`: the extension's name and the operation's).
* The syntax names an extension's operations by strings and its values by the
  extension's name and their encoding (`ExtCode`, `extVal E v`), so that code
  and values do not depend on the list of extensions: the model of a Go
  function implemented with an extension needs nothing but the extension's
  name.
* `GooseExts` is the closed list `exts` of extensions that a program runs
  against. Its states are the products of the extensions' states
  (`state.world`, `GlobalState.globalWorld`). An `ExternalOp` steps with the
  first extension of the list of its name (`extNamed`), by that extension's
  step of the operation's name.
* `ElemExt E` is the proposition that `E` is the extension of the list named
  `E.name` (as iris's `ElemG`): proofs about one extension assume only that, and
  the list is fixed when a program is closed off by an adequacy theorem, where
  it holds by computation. Its position in the list (`ElemExt.mem`) is derived
  from it.
* The semantics of an extension (`ExtSemantics`, `Lang.lean`) and its ghost
  state (`ExtInterp`, `Lifting.lean`) are classes on the extension, and the
  closed list's (`GooseSemantics`, `GooseInterp`) are tuples of them, one per
  extension of the list (`ExtTuple`).

`ExtIn E l` is a position of `E` in `l`. The states of `l` are nested products
along `l`, so that a position projects out of them by recursion, without casts.
-/
module

public import Perennial.Std.Countable

@[expose] public section

namespace Perennial

/-- An extension of GooseLang: its operations, values and state. -/
structure GooseExt where
  /-- The name, by convention the path of the Go package it implements: the
  syntax names the extension's operations and values by it. -/
  name : String
  /-- The opaque values the operations return (`ExtV`), e.g. sockets. -/
  Val : Type
  /-- The per-node state, e.g. a disk. -/
  LocalState : Type
  /-- The state shared between nodes, e.g. the network. -/
  GlobalState : Type
  [val_countable : Pos.Countable Val]
  [localState_inhabited : Inhabited LocalState]
  [globalState_inhabited : Inhabited GlobalState]

attribute [instance] GooseExt.val_countable
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

/-! ## States of a list of extensions -/

/-- The local states of the extensions of `l`. -/
abbrev ExtsLocalState (l : List GooseExt) : Type := ExtTuple GooseExt.LocalState l

/-- The global states of the extensions of `l`. -/
abbrev ExtsGlobalState (l : List GooseExt) : Type := ExtTuple GooseExt.GlobalState l

instance countableEmpty : Pos.Countable Empty where
  encode e := e.elim
  decode _ := none
  decode_encode e := e.elim

/-! ## Opaque values: named and encoded -/

/-- An opaque value of an extension, in the syntax: the extension's name and the encoding of
the value (`extVal`). -/
structure ExtCode where
  ext : String
  code : Pos
deriving DecidableEq

noncomputable instance ExtCode.countable : Pos.Countable ExtCode :=
  .ofInjective (fun c => Pos.Countable.encode (c.ext, c.code)) (fun a b h => by
    have h' : (a.ext, a.code) = (b.ext, b.code) := Pos.encode_inj h
    cases a; cases b; cases h'; rfl)

/-- The value `v` of the extension `E`. -/
abbrev extVal (E : GooseExt) (v : E.Val) : ExtCode := ⟨E.name, Pos.Countable.encode v⟩

theorem extVal_inj {E : GooseExt} {v v' : E.Val} (h : extVal E v = extVal E v') : v = v' :=
  Pos.encode_inj (ExtCode.mk.inj h).2

/-! ## Extensions by name -/

/-- The first extension of `l` named `n`. -/
def extNamed : List GooseExt → String → Option GooseExt
  | [], _ => none
  | E :: l, n => if E.name = n then some E else extNamed l n

/-- The position in `l` of the first extension named `n`. -/
def ExtIn.ofNamed : {l : List GooseExt} → {n : String} → {E : GooseExt} →
    extNamed l n = some E → ExtIn E l
  | E' :: l, n, E, h =>
    if hn : E'.name = n then
      have hE : E' = E := by simpa [extNamed, hn] using h
      hE ▸ .here
    else .there (ExtIn.ofNamed (l := l) (n := n) (E := E) (by simpa [extNamed, hn] using h))

/-! ## The closed list of extensions -/

/-- The list of extensions that a program runs against. Code and proofs are
generic over it; it is fixed by the instance of an adequacy theorem. -/
class GooseExts where
  exts : List GooseExt

export GooseExts (exts)

/-- `ExtCode` as the syntax holds it (`ExtV`). The syntax (`Expr`, `val`, the evaluation
contexts) keeps the list of extensions as a parameter, although it no longer depends on it, so
that its signature, and the terms the proof mode builds over it, are those of a syntax that
did. -/
abbrev ExtCodeIn [GooseExts] : Type := ExtCode

/-- `E` is the extension of the list named `E.name` (as iris's `ElemG`). -/
class ElemExt [GooseExts] (E : GooseExt) : Prop where
  registered : extNamed exts E.name = some E

section elem
variable [GooseExts]

/-- The position of `E` in the list of extensions. -/
def ElemExt.mem {E : GooseExt} (h : ElemExt E) : ExtIn E exts := ExtIn.ofNamed h.registered

/-- The local state of the extension `E`. -/
abbrev extLocal (E : GooseExt) [h : ElemExt E] (w : ExtsLocalState exts) : E.LocalState :=
  h.mem.get w

/-- The global state of the extension `E`. -/
abbrev extGlobal (E : GooseExt) [h : ElemExt E] (w : ExtsGlobalState exts) : E.GlobalState :=
  h.mem.get w

end elem

end Perennial
