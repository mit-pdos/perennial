/-
`errors.is`'s spec (the tree walk of `Is`).
-/
module

public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- `is(err, target, c)` (the tree walk of `Is`): it returns an answer of Go's walk of the tree
(`IsWalk c I U target err`, over the relations `I` and `U` of the tree's methods). For `c`
(`target`'s type is comparable), `target` is a non-nil error that `==` compares with the tree's
errors of its type (`ComparableErr`: a pointer, an `Errno`, ...), so that `err == target` does not
panic. -/
abbrev errors.is.spec : Prop :=
  ∀ (S : GoError → Prop) (I : GoInterfaceOk → Bool → Prop)
    (U : GoInterfaceOk → List GoError → Prop) (err target : GoError) (c : Bool),
    S err →
    (c = true → ∃ tii, target = interface.ok tii ∧ ComparableErr S tii) →
    {{ errorWalkTree (GF := GF) S I U target }}
      (App (App (App (Val (@! is')) (Val #err)) (Val #target)) (Val #c))
    {{ (b : Bool), RET #b; ⌜IsWalk c I U target err b⌝ }}

end spec

end Perennial
