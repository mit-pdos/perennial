/-
The proof of `context.(*cancelCtx).Err`.
-/
module

public import Perennial.Spec.context.cancelCtx__Err
public import Perennial.Spec.sync.atomic.Value__Load
public import Perennial.Spec.context.cancelCtx__Done
public import Perennial.Proof.context.CancelCtxCells

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

theorem context.cancelCtx.Err.wp_proof
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG)) :
    context.cancelCtx.Err.spec (GF := GF) (hG := hG) := fun c γ P cl => by
  have wp_err_Load := wp_err_Load_of wp_VLoad
  wp_start as ⟨#Hc, Hcl⟩
  wp_auto
  wp_apply wp_err_Load c γ P cl $$ [$Hc $Hcl] as %e ⟨%hcl, He⟩
  by_cases he : e = interface.nil
  · subst he
    wp_auto
    iapply HΦ
    isplitl []
    · ipureintro; exact hcl
    · itrivial
  · simp only [he, ↓reduceIte]
    icases He with ⟨%ht, #Hp, #Hclosed⟩
    cases e with
    | nil => exact absurd rfl he
    | ok ii =>
    wp_auto
    wp_apply wp_cancelCtx_Done $$ [$Hc] as %ch %γch ⟨#Hd, -⟩
    ihave #Hch := isContextDone_is_chan _ _ _ $$ Hd
    wp_bind (App (Val (chan.receive _)) _)
    iapply chan.wp_receive (V := Unit) ch γch $$ Hch
    iintro _
    iapply isContextDone_receive _ _ _ _ $$ Hd
    iintro -
    wp_auto
    erw [ite_eq_left ht]
    wp_auto
    iapply HΦ
    isplitl []
    · ipureintro; intro _; exact he
    · simp only [he, ↓reduceIte, isTypedErr]
      iframe #; ipureintro; exact ht

end proof

end Perennial
