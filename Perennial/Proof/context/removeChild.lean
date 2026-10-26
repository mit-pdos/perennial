/-
The proof of `context.removeChild`.
-/
module

public import Perennial.Spec.context.removeChild
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.context.parentCancelCtx
public import Perennial.Proof.context.BackgroundCtx

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.removeChild.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_parentCancelCtx : context.parentCancelCtx.spec (GF := GF) (hG := hG)) :
    context.removeChild.spec (GF := GF) (hG := hG) :=
  fun parent child [SafeMapKey (GF := GF) context.canceler.ty child] => by
  wp_start as #Hpar
  unfold isParentCtx
  icases Hpar with (%hbg | ⟨%s, #Hctx⟩)
  · subst hbg
    wp_auto
    wp_apply wp_parentCancelCtx_background
    iapply HΦ; itrivial
  · ihave %hne : ⌜parent.ty ≠ context.stopCtx.ty⌝ $$ [Hctx]
    · unfold isContext isContextDef
      iNamed Hctx
      icases HParentCC with ⟨%h, -⟩
      ipureintro; exact h
    wp_auto
    simp only [hne, ↓reduceIte, _root_.decide_false]
    wp_auto
    wp_apply wp_parentCancelCtx parent s $$ [$Hctx] as %p %ok Hp
    cases ok
    · wp_auto
      iapply HΦ; itrivial
    · simp only [↓reduceIte]
      iunfold isCancelCtx at Hp
      icases Hp with ⟨%γp, %Pp, #Hp⟩
      iunfold isCancelCtxOf at Hp
      iNamed Hp
      wp_auto
      wp_apply wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
      unfold cancelCtxLockInv
      icases Hlk with ⟨%children, %cause, %od, %closed, Hchildren, Hcause, Hcl, Hod, HR⟩
      wp_auto
      by_cases hnil : children = map.nil
      · rw [show decide (children = map.nil) = true from decide_eq_true hnil]
        wp_auto
        wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hod HR]
        · inext; iexists children, cause, od, closed; iframe
        iapply HΦ; itrivial
      · rw [show decide (children = map.nil) = false from decide_eq_false hnil]
        cases closed
        · simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hcl with ⟨Hcg, Hch⟩
          unfold childrenInv
          icases Hch with (%h | ⟨%M, HM, #Hspecs⟩)
          · exact absurd h hnil
          wp_auto
          wp_apply wp_mapDelete $$ [$HM] as HM
          wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcg HM Hod HR]
          · inext; iexists children, cause, od, false; simp only [Bool.false_eq_true, ↓reduceIte]
            iframe
            simp only [named]
            iframe Hcg
            iright
            iexists _
            iframe HM
            imodintro
            iintro %k %u %hk
            iapply Hspecs $$ %k %u
            ipureintro
            rw [GMap.lookup_delete_iff] at hk
            split at hk
            · cases hk
            · exact hk
          iapply HΦ; itrivial
        · simp only [↓reduceIte]
          icases Hcl with ⟨-, %h⟩
          exact absurd h hnil

end proof

end Perennial
