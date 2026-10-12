/-
The proof of `sync.atomic.CompareAndSwapInt32`.
-/
module

public import Perennial.Spec.sync.atomic.CompareAndSwapInt32

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

theorem sync.atomic.CompareAndSwapInt32.wp_proof :
    sync.atomic.CompareAndSwapInt32.spec (GF := GF) (hG := hG) := by
  intro addr old new
  wp_start as _
  wp_bind (CmpXchg _ _ _)
  imod HΦ with ⟨%v, %dq, >Haddr, >%Hdq, HΦ⟩
  by_cases h : v = old
  · subst h
    simp only [↓reduceIte, decide_true] at Hdq ⊢
    subst Hdq
    wp_apply_core wp_cmpxchg_suc addr v v new _ _ rfl $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ
  · simp only [h, ↓reduceIte, decide_false]
    wp_apply_core wp_cmpxchg_fail addr v old new dq _ _ h $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ

end proof

end Perennial
