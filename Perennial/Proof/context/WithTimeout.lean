/-
The proof of `context.WithTimeout`.
-/
module

public import Perennial.Spec.context.WithTimeout
public import Perennial.Spec.time.Time__Add
public import Perennial.Spec.time.Now
public import Perennial.Spec.context.WithDeadline

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.WithTimeout.wp_proof
    (wp_TAdd : time.Time.Add.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_WithDeadline : context.WithDeadline.spec (GF := GF) (hG := hG)) :
    context.WithTimeout.spec (GF := GF) (hG := hG) := fun parent parent_desc timeout => by
  wp_start as #Hctx
  wp_auto
  wp_apply wp_Now as %now -
  wp_apply wp_TAdd as %d -
  wp_apply wp_WithDeadline $$ [$Hctx] as %ctx' %γ' %cancel %d' ⟨-, #Hcancel, #Hctx'⟩
  wp_end
  iframe #

end proof

end Perennial
