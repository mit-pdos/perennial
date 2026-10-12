/-
The proof of `context.parentCancelCtx`.
-/
module

public import Perennial.Spec.context.parentCancelCtx
public import Perennial.Spec.sync.atomic.Value__Load
public import Perennial.Proof.context.CancelCtxCells

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.parentCancelCtx.wp_proof
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG)) :
    context.parentCancelCtx.spec (GF := GF) (hG := hG) := fun parent parent_desc => by
  have wp_done_Load := wp_done_Load_of wp_VLoad
  wp_start as #Hctx
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, ⟨%closed, #Hclosed⟩, _⟩
  unfold isContext isContextDef
  icases Hctx with ⟨#HDeadline, #HDone, #HErr, #HValue, -⟩
  wp_auto
  wp_apply HDone as %done %γdone #Hdone
  by_cases h1 : done = closed
  · simp only [h1, _root_.decide_true]
    wp_auto
    wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  simp only [h1, _root_.decide_false]
  wp_auto
  by_cases h2 : done = chan.nil
  · simp only [h2, _root_.decide_true]
    wp_auto
    wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  simp only [h2, _root_.decide_false]
  wp_auto
  unfold cancelCtxKeyAny
  wp_apply HValue as %v #Hv
  cases v with
  | nil =>
    wp_auto
    wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  | ok ii =>
    by_cases hty : ii.ty = go.GoType.PointerType context.cancelCtx.ty
    · simp only [isCancelCtxAny, hty, ↓reduceIte, _root_.decide_true]
      icases Hv with ⟨%c, %hv, #Hc⟩
      rw [hv]
      wp_auto
      ihave #Hc' : isCancelCtx c $$ []
      · iexact Hc
      unfold isCancelCtx
      icases Hc' with ⟨%γc, %Pc, #Hcc⟩
      wp_apply wp_done_Load $$ [$Hcc] as %och -
      cases och with
      | none =>
        unfold doneAny
        wp_auto
        have h3 : decide (zero_val GoChan = done) = false := by
          simp only [decide_eq_false_iff_not]; exact fun h => h2 h.symm
        simp only [h3]
        wp_auto
        wp_end
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro; trivial
      | some ch =>
        unfold doneAny
        wp_auto
        by_cases h4 : ch = done
        · simp only [h4, _root_.decide_true]
          wp_auto
          wp_end
          simp only [↓reduceIte]
          iexact Hc
        · simp only [h4, _root_.decide_false]
          wp_auto
          wp_end
          simp only [Bool.false_eq_true, ↓reduceIte]
          ipureintro; trivial
    · simp only [hty, ↓reduceIte, _root_.decide_false]
      wp_auto
      wp_end
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; trivial

end proof

end Perennial
