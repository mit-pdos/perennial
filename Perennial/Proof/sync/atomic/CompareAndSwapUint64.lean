/-
The proof of `sync.atomic.CompareAndSwapUint64`.
-/
module

public import Perennial.Spec.sync.atomic.CompareAndSwapUint64

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

theorem sync.atomic.CompareAndSwapUint64.wp_proof :
    sync.atomic.CompareAndSwapUint64.spec (GF := GF) (hG := hG) := by
  intro addr old new hal
  wp_start as _
  wp_bind (CmpXchgN _ _ _)
  imod HΦ with ⟨%v, %dq, >Haddr, >%Hdq, HΦ⟩
  by_cases h : v = old
  · subst h
    simp only [↓reduceIte, decide_true] at Hdq ⊢
    subst Hdq
    wp_apply_core typed.wp_cmpxchg_suc addr v v new hal rfl $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ
  · simp only [h, ↓reduceIte, decide_false]
    wp_apply_core typed.wp_cmpxchg_fail addr v old new dq hal h $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ

end proof

end Perennial
