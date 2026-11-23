/-
`strings.Builder.Reset`'s spec.
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

/-- `b.Reset()`: the Builder is empty again. (Go's also unties it from `b`'s address, so that a
copy of it may be written to; the model does not, `TrustedCode/strings.lean`, and neither does the
spec.) -/
abbrev strings.Builder.Reset.spec : Prop :=
  ∀ (l : Loc) (s : GoString),
    {{ strings.ownBuilder (GF := GF) l s }}
      (App (Val (l @!! go.GoType.PointerType strings.Builder.ty @!! go!"Reset")) (Val #()))
    {{ RET #(); strings.ownBuilder l [] }}

end spec

end Perennial
