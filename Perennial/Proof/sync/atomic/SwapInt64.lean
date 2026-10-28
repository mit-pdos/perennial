/-
The proof of `sync.atomic.SwapInt64`.
-/
module

public import Perennial.Spec.sync.atomic.SwapInt64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

theorem sync.atomic.SwapInt64.wp_proof :
    sync.atomic.SwapInt64.spec (GF := GF) (hG := hG) := by
  intro addr v
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_swap_bytes_typed _ _ addr oldv v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

end proof

end Perennial
