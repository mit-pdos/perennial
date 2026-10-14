/-
`slices.xorshift.Next`'s spec.
-/
module

public import Perennial.Proof.slices.PartitionBasics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

abbrev slices.xorshift.Next.spec : Prop :=
  ∀ (r : Loc) (v : xorshift),
    {{ (r ↦ v : IProp GF) }}
      (App (Val (r @!! go.GoType.PointerType xorshift.ty @!! go!"Next")) (Val #()))
    {{ (n : w64), RET #n; ∃ v' : xorshift, r ↦ v' }}

end spec

end Perennial
