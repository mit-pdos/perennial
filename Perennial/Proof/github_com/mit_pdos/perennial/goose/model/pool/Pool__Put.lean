/-
The proof of `Pool.Put` (`goose/model/pool/pool.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.model.pool.Pool__Put
public import Perennial.Spec.github_com.goose_lang.primitive.Mutex__Lock
public import Perennial.Spec.github_com.goose_lang.primitive.Mutex__Unlock
public import Perennial.Spec.github_com.goose_lang.primitive.RandomUint64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.model.pool.Assumptions]

open github_com.mit_pdos.perennial.goose.model.pool in
theorem github_com.mit_pdos.perennial.goose.model.pool.Pool.Put.wp_proof
    (wp_RandomUint64 : github_com.goose_lang.primitive.RandomUint64.spec (GF := GF) (hG := hG))
    (wp_Mutex_Lock : github_com.goose_lang.primitive.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : github_com.goose_lang.primitive.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.model.pool.Pool.Put.spec (GF := GF) (hG := hG) := by
  intro s P x
  simp only [isPool_unseal, isPoolDef]
  wp_start as ⟨#His, Hx⟩
  wp_auto
  wp_apply wp_RandomUint64 as %r
  iintro _
  wp_auto
  wp_if_destruct
  · iapply HΦ
    itrivial
  wp_apply wp_Mutex_Lock $$ [$His] as ⟨Hlocked, Hi⟩
  unfold poolInv
  iNamed Hi
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoAny) (t := go.any) [x]
  wp_auto
  rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.any #x)] = 1 from rfl]
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Htmp, -⟩
  wp_auto
  wp_apply wp_slice_append (V := GoAny) (t := go.any) sl xs _ [x] (DFrac.own 1)
    $$ [Hsl Hcap Htmp] with %sl' ⟨Hsl, Hcap, -⟩
  · iframe
  wp_apply wp_Mutex_Unlock $$ [$His $Hlocked items Hsl Hcap HP Hx]
  · iexists sl', xs ++ [x]
    iframe items Hsl Hcap
    iapply BigSepL.bigSepL_snoc.2
    iframe
  iapply HΦ
  itrivial

end proof

end Perennial
