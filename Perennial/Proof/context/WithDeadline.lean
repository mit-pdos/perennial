/-
The proof of `context.WithDeadline`.
-/
module

public import Perennial.Spec.context.WithDeadline
public import Perennial.Spec.context.WithDeadlineCause

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.WithDeadline.wp_proof
    (wp_WithDeadlineCause : context.WithDeadlineCause.spec (GF := GF) (hG := hG)) :
    context.WithDeadline.spec (GF := GF) (hG := hG) := fun parent parent_desc d => by
  wp_start as #Hctx
  wp_auto
  wp_apply wp_WithDeadlineCause $$ [$Hctx] as %ctx' %γ' %cancel %d' ⟨%hd, #Hcancel, #Hctx'⟩
  wp_end
  iframe #
  ipureintro; exact hd

end proof

end Perennial
