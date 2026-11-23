/-
`strings.Builder.Write`'s spec.
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

/-- `b.Write(p)`: appends the bytes of `p`; returns `len(p)` and a nil error. -/
abbrev strings.Builder.Write.spec : Prop :=
  ∀ (l : Loc) (s : GoString) (p : GoSlice) (bs : List w8) (dp : DFrac),
    {{ strings.ownBuilder (GF := GF) l s ∗ p ↦*{dp} bs }}
      (App (Val (l @!! go.GoType.PointerType strings.Builder.ty @!! go!"Write")) (Val #p))
    {{ RET (PairV #(W64 bs.length) #interface.nil); strings.ownBuilder l (s ++ bs) ∗ p ↦*{dp} bs }}

end spec

end Perennial
