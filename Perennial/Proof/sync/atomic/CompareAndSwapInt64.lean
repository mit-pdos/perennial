/-
The proof of `sync.atomic.CompareAndSwapInt64`.
-/
module

public import Perennial.Spec.sync.atomic.CompareAndSwapInt64

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

theorem sync.atomic.CompareAndSwapInt64.wp_proof :
    sync.atomic.CompareAndSwapInt64.spec (GF := GF) (hG := hG) := by
  intro addr old new
  wp_start as _
  wp_bind (CmpXchgBytes _ _ _)
  imod HΦ with ⟨%v, %dq, >Haddr, >%Hdq, HΦ⟩
  by_cases h : v = old
  · subst h
    simp only [↓reduceIte, decide_true] at Hdq ⊢
    subst Hdq
    wp_apply_core wp_cmpxchg_bytes_suc_typed addr v v new _ _ rfl $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ
  · simp only [h, ↓reduceIte, decide_false]
    wp_apply_core wp_cmpxchg_bytes_fail_typed addr v old new dq _ _ h $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ

end proof

end Perennial
