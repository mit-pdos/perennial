/-
`strings.Builder.WriteString`'s spec.
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

/-- `b.WriteString(x)`: appends `x`; returns `len(x)` and a nil error. -/
abbrev strings.Builder.WriteString.spec : Prop :=
  ∀ (l : Loc) (s x : GoString),
    {{ strings.ownBuilder (GF := GF) l s }}
      (App (Val (l @!! go.GoType.PointerType strings.Builder.ty @!! go!"WriteString")) (Val #x))
    {{ RET (PairV #(W64 x.length) #interface.nil); strings.ownBuilder l (s ++ x) }}

end spec

end Perennial
