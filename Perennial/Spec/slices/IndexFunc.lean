/-
`slices.IndexFunc`'s spec.
-/
module

public import Perennial.Proof.slices.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

/-- `f` answers on every element of `xs` with a `b` such that `P x b` (persistently, with no
resources): the premise of `IndexFunc` and `ContainsFunc` on their predicate argument. With
`P x b := b = p x`, `f` computes the pure predicate `p`; with `P x b := True`, any `f` that
returns. -/
def slices.funcAnswers {V : Type} (P : V → Bool → Prop) (xs : List V) (f : GoFunc) :
    IProp GF :=
  iprop(□ ∀ x : V, ⌜x ∈ xs⌝ -∗
    {{ True }} (App (Val #f) (Val #x)) {{ (b : Bool), RET #b; ⌜P x b⌝ }})

instance slices.funcAnswers_persistent {V : Type} (P : V → Bool → Prop)
    (xs : List V) (f : GoFunc) : Persistent (slices.funcAnswers (GF := GF) P xs f) := by
  unfold slices.funcAnswers; infer_instance

/-- `slices.IndexFunc(s, f)` (Go: `for i := range s { if f(s[i]) { return i } }; return -1`),
for any slice type `S` of elements `Et`: `f` is called on the elements in order until it answers
`true`; the result is the index `i` of that element (every element before it answered `false`),
or `-1` if every element answered `false`. `s` is only read. -/
abbrev slices.IndexFunc.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {Et : go.GoType}
    [IntoValTyped (GF := GF) V Et] {S : go.GoType} [S ↓u go.SliceType Et]
    (s : GoSlice) (dq : DFrac) (xs : List V) (f : GoFunc) (P : V → Bool → Prop),
    {{ s ↦*{dq} xs ∗ slices.funcAnswers (GF := GF) P xs f }}
      (App (App (Val #(functions slices.IndexFunc [S, Et])) (Val #s)) (Val #f))
    {{ (i : w64), RET #i;
        s ↦*{dq} xs ∗
        ⌜(sint.Z i = -1 ∧ ∀ x ∈ xs, P x false) ∨
          (0 ≤ sint.Z i ∧ ∃ x, xs[(sint.Z i).toNat]? = some x ∧ P x true ∧
            ∀ (j : Nat) (y : V), j < (sint.Z i).toNat → xs[j]? = some y → P y false)⌝ }}

end spec

end Perennial
