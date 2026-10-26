/-
The proof of `sync.runtime_Semrelease`.
-/
module

public import Perennial.Spec.sync.runtime_Semrelease

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.runtime_Semrelease.wp_proof :
    sync.runtime_Semrelease.spec (GF := GF) (hG := hG) := by
  intro sema γ N _u1 _u2
  wp_start as #Hsem
  simp only [isSema_unseal, isSemaDef, ownSema_unseal, ownSemaDef]
  wp_bind (AtomicAdd _ _)
  iinv Hsem with ⟨%v, >Hs, >Hv⟩
  imod HΦ with ⟨%v1, Hv2, HΦ⟩
  icombine Hv Hv2 gives % ⟨_, Heq⟩
  subst Heq
  simp only [typedPointsto_unseal, typedPointstoWrap, typedPointstoDef_heap]
  icases Hs with ⟨Hs, %Hnn⟩
  wp_apply_core Perennial.wp_atomic_add sema #v #(W32 1) #(v + W32 1)
    (by simp [go.intoVal_unfold, atomicAddEval]) $$ Hs
  iintro Hs
  imod ghostVar_update_halves (v + W32 1) γ v v $$ Hv Hv2 with ⟨Hv, Hv2⟩
  imod HΦ $$ Hv2 with HΦ
  imodintro
  imodintro
  isplitl [Hs Hv]
  · inext; iexists _
    simp only [typedPointsto_unseal, typedPointstoWrap, typedPointstoDef_heap]
    iframe; ipureintro; exact Hnn
  wp_auto
  iexact HΦ

end proof

end Perennial
