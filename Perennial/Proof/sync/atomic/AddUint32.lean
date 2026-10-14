/-
The proof of `sync.atomic.AddUint32`.
-/
module

public import Perennial.Spec.sync.atomic.AddUint32

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

theorem sync.atomic.AddUint32.wp_proof :
    sync.atomic.AddUint32.spec (GF := GF) (hG := hG) := by
  intro addr v
  wp_start as _
  imod HΦ with ⟨%oldv, Haddr, HΦ⟩
  simp only [typedPointsto_unseal, typedPointstoWrap, typedPointstoDef_heap,
    TypedPointsto.typedPointstoDef]
  icases Haddr with > ⟨Haddr, %Hnn⟩
  wp_apply_core Perennial.wp_atomic_add addr #oldv #v #(oldv + v) (by simp [go.intoVal_unfold, atomicAddEval]) $$ Haddr
  iintro Haddr
  iapply HΦ
  iframe
  ipureintro; exact Hnn

end proof

end Perennial
