From Perennial.Helpers Require Import Qextra.
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
From Perennial.Helpers Require Import iris.
From Perennial.algebra Require Import deletable_heap.
From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import lifting.
From Perennial.goose_lang Require Import proofmode.

Section goose_lang.
  Context `{!invG Σ}.

  Class AsMapsTo (P: iProp Σ)
        (Φ : Qp -> iProp Σ) :=
    { as_mapsto : P ≡ Φ 1%Qp;
      as_mapsto_fractional :> Fractional (λ q, Φ q);
      as_mapsto_timeless :> ∀ q, Timeless (Φ q);
    }.

  Arguments as_mapsto {P Φ} AsMapsTo.

  Let N := nroot .@ "readonly".

  Definition readonly_def P `{H: AsMapsTo P Φ}: iProp Σ :=
    inv N (∃ (q: Qp), ⌜(Qcanon.Qclt q 1)%Qp⌝ ∗ Φ q).
  Definition readonly_aux : seal (@readonly_def). Proof. by eexists. Qed.
  Definition readonly := readonly_aux.(unseal).
  Definition readonly_eq : @readonly = @readonly_def := readonly_aux.(seal_eq).
  Arguments readonly P {Φ}%function_scope {H}.

  Ltac unseal := rewrite readonly_eq /readonly_def.

  Theorem readonly_alloc P `{H: AsMapsTo P Φ} (q:Qp) E :
    Qcanon.Qclt q 1 ->
    Φ q ={E}=∗ readonly P.
  Proof.
    unseal.
    iIntros (Hbound) "HP".
    iMod (inv_alloc with "[HP]") as "$"; auto.
  Qed.

  Global Instance readonly_persistent P `{H: AsMapsTo P Φ} : Persistent (readonly P).
  Proof. unseal; apply _. Qed.

  Instance as_mapsto_AsFractional P `{H: AsMapsTo P Φ} :
    AsFractional (Φ q) (λ q, Φ q) q.
  Proof.
    split; auto.
    apply _.
  Qed.

  Theorem readonly_alloc_1 P `{H: AsMapsTo P Φ} E :
    P ={E}=∗ readonly P.
  Proof.
    iIntros "HP".
    rewrite {1}H.(as_mapsto).
    iDestruct (fractional_half_1 with "HP") as "[HP1 HP2]".
    iApply (readonly_alloc with "HP1").
    reflexivity.
  Qed.

  Theorem readonly_load_lt P `{H: AsMapsTo P Φ} E :
    ↑N ⊆ E ->
    readonly P ={E}=∗ ∃ (q: Qp), ⌜(Qcanon.Qclt q 1)%Qc⌝ ∗ Φ q.
  Proof.
    iIntros (Hsub) "Hro".
    unseal.
    assert (Timeless (∃ q, Φ q)).
    { apply _. }
    iMod (inv_dup_acc (∃ (q: Qp), ⌜(Qcanon.Qclt q 1)%Qc⌝ ∗ Φ q) with "Hro []") as ">H"; first by auto.
    { iIntros "HΦ".
      iDestruct "HΦ" as (q) "[% HΦ]".
      iDestruct (fractional_half with "HΦ") as "[HΦ1 HΦ2]".
      assert (Qcanon.Qclt (q/2)%Qp 1).
      { etransitivity; eauto.
        apply Qp_div_2_lt. }
      iSplitL "HΦ1"; iExists _; by iFrame.
    }
    iModIntro.
    auto.
  Qed.

  Theorem readonly_load P `{H: AsMapsTo P Φ} E :
    ↑N ⊆ E ->
    readonly P ={E}=∗ ∃ q, Φ q.
  Proof.
    iIntros (Hsub) "Hro".
    iMod (readonly_load_lt with "Hro") as (q) "[% HΦ]"; auto.
  Qed.

End goose_lang.

Instance heap_mapsto_AsMapsTo `{ext: !ext_op} `{!na_heapG loc val Σ}
         (l: loc) (v: val) :
  AsMapsTo (l ↦ v) (λ q, l ↦{q} v)%I.
Proof.
  split; [done|apply _|apply _].
Qed.

Instance mapsto_AsMapsTo `{ffi_sem: ext_semantics} `(hG: gen_heapG Σ) :
  AsMapsTo (mapsto (hG:=hG) l 1 v) (λ q, mapsto (hG:=hG) l q v).
Proof.
  split; [done|apply _|apply _].
Qed.

Hint Mode AsMapsTo - + - : typeclass_instances.
Arguments readonly {Σ invG0} _%bi_scope {Φ}%function_scope {H}.
