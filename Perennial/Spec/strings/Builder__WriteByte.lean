/-
`strings.Builder.WriteByte`'s spec.
-/
module

public import Perennial.Proof.strings.BuilderBasics

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

/-- `b.WriteByte(c)`: appends the byte `c`; returns a nil error. -/
abbrev strings.Builder.WriteByte.spec : Prop :=
  ∀ (l : Loc) (s : GoString) (c : w8),
    {{ strings.ownBuilder (GF := GF) l s }}
      (App (Val (l @!! go.GoType.PointerType strings.Builder.ty @!! go!"WriteByte")) (Val #c))
    {{ RET #interface.nil; strings.ownBuilder l (s ++ [c]) }}

end spec

end Perennial
