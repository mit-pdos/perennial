/-
`strings.NewReplacer`'s spec.
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `strings.NewReplacer(oldnew...)`, for an even number of strings (it panics on an odd
one): a new `Replacer` holding a copy of them. -/
abbrev strings.NewReplacer.spec : Prop :=
  ∀ (oldnew : GoSlice) (ss : List GoString) (dq : DFrac),
  ss.length % 2 = 0 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ oldnew ↦*{dq} ss }}
      (App (Val (@! NewReplacer)) (Val #oldnew))
    {{ (r : Loc), RET #r; oldnew ↦*{dq} ss ∗ strings.ownReplacer r ss }}

end spec

end Perennial
