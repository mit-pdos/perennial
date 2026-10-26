/-
The proof of `sync.atomic.StoreInt64`.
-/
module

public import Perennial.Spec.sync.atomic.StoreInt64

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

theorem sync.atomic.StoreInt64.wp_proof :
    sync.atomic.StoreInt64.spec (GF := GF) (hG := hG) := by
  intro addr v
  wp_start as _
  wp_bind (AtomicSwap _ _)
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_swap _ _ addr oldv v $$ Haddr
  iintro Haddr
  imod HΦ $$ Haddr with HΦ
  imodintro
  wp_pures
  iexact HΦ

end proof

end Perennial
