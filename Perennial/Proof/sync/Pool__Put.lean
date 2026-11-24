/-
The proof of `sync.(*Pool).Put`, whose model (`goose/model/overlay/sync/pool.go`) ignores `nil`
and otherwise adds `x` to the pool's state (`poolModelOf`) or drops it.
-/
module

public import Perennial.Spec.sync.Pool__Put
public import Perennial.Spec.sync.poolModelOf
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.internal.gomodel.Choose

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

theorem sync.Pool.Put.wp_proof
    (wp_poolModelOf : sync.poolModelOf.spec (GF := GF) (hG := hG))
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    sync.Pool.Put.spec (GF := GF) (hG := hG) := by
  intro p f R P x
  wp_start as ⟨#His, Hx⟩
  cases x with
  | nil =>
    wp_auto
    iapply HΦ
    itrivial
  | ok i =>
    wp_auto
    wp_apply wp_poolModelOf p f R P $$ [$His] as %s #Hs
    simp only [sync.isPoolModel_unseal, sync.isPoolModelDef]
    wp_auto
    wp_apply wp_Choose as %b _
    wp_auto
    wp_if_destruct
    · iapply HΦ
      itrivial
    wp_apply wp_Mutex_Lock $$ [$Hs] as ⟨Hlocked, Hi⟩
    unfold sync.poolInv
    iNamed Hi
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoAny) (t := go.any) [GoInterface.ok i]
    wp_auto
    rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.any #(GoInterface.ok i))] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Htmp, -⟩
    wp_auto
    wp_apply wp_slice_append (V := GoAny) (t := go.any) sl xs _ [GoInterface.ok i] (DFrac.own 1)
      $$ [Hsl Hcap Htmp] with %sl' ⟨Hsl, Hcap, -⟩
    · iframe
    wp_apply wp_Mutex_Unlock $$ [$Hs $Hlocked items Hsl Hcap HP Hx]
    · iexists sl', xs ++ [GoInterface.ok i]
      iframe items Hsl Hcap
      iapply BigSepL.bigSepL_snoc.2
      iframe
    iapply HΦ
    itrivial

end proof

end Perennial
