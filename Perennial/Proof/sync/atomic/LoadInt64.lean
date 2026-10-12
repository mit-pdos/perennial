/-
The proof of `sync.atomic.LoadInt64`.
-/
module

public import Perennial.Spec.sync.atomic.LoadInt64

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

theorem sync.atomic.LoadInt64.wp_proof :
    sync.atomic.LoadInt64.spec (GF := GF) (hG := hG) := by
  intro addr dq
  wp_start as _
  imod HΦ with ⟨%v, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_load _ _ addr dq v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

end proof

end Perennial
