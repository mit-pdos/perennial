/-
The proof of `sync.atomic.SwapUint64`.
-/
module

public import Perennial.Spec.sync.atomic.SwapUint64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

theorem sync.atomic.SwapUint64.wp_proof :
    sync.atomic.SwapUint64.spec (GF := GF) (hG := hG) := by
  intro addr v hal
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core typed.wp_atomic_swap addr oldv v hal $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

end proof

end Perennial
