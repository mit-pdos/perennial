From Perennial.Helpers Require Import Qextra.
From iris.base_logic.lib Require Import ae_invariants.
From iris.bi.lib Require Import fractional.
From Perennial.Helpers Require Import iris.
From Perennial.algebra Require Import deletable_heap.
From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import lifting.
From Perennial.goose_lang Require Import proofmode.

Set Default Proof Using "Type".

Section goose_lang.
  Context `{!invG Σ}.

  Class AsMapsTo (P: iProp Σ)
        (Φ : Qp -> iProp Σ) :=
    { as_mapsto : P ≡ Φ 1%Qp;
      as_mapsto_fractional :> Fractional Φ;
      as_mapsto_timeless :> ∀ q, Timeless (Φ q);
    }.

  Arguments as_mapsto {P Φ} AsMapsTo.

  Definition readonly_inner Φ: iProp Σ := ∃ (q: Qp), ⌜(Qcanon.Qclt q 1)%Qp⌝ ∗ Φ q.
  Definition readonly_def P `{H: AsMapsTo P Φ}: iProp Σ :=
    ae_inv 0 None (readonly_inner Φ).
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
    iMod (ae_inv_alloc with "[HP]") as "$"; auto.
    rewrite /readonly_inner; auto.
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

  Theorem readonly_inner_dup Φ {H: Fractional Φ} :
    readonly_inner Φ -∗ readonly_inner Φ ∗ readonly_inner Φ.
  Proof.
    iIntros "HΦ".
    iDestruct "HΦ" as (q) "[% HΦ]".
    iDestruct (fractional_half with "HΦ") as "[HΦ1 HΦ2]".
    { split; auto. }
    { split; auto. }
    assert (Qcanon.Qclt (q/2)%Qp 1).
    { etransitivity; eauto.
      apply Qp_div_2_lt. }
    iSplitL "HΦ1"; iExists _; by iFrame.
  Qed.

  Theorem readonly_load_lt E P `{H: AsMapsTo P Φ} :
    readonly P -∗ |={E}=> ∃ (q: Qp), ⌜(Qcanon.Qclt q 1)%Qc⌝ ∗ Φ q.
  Proof.
    iIntros "Hro".
    unseal.
    iApply fupd_split_level_fupd.
    iApply (ae_inv_acc_bupd with "Hro []").
    iIntros ">Hinner !> !>".
    iDestruct (readonly_inner_dup with "Hinner") as "[$ Hinner]".
    auto.
  Qed.

  Theorem readonly_load P `{H: AsMapsTo P Φ} E :
    readonly P ={E}=∗ ∃ q, Φ q.
  Proof.
    iIntros "Hro".
    iMod (readonly_load_lt with "Hro") as (q) "[% HΦ]"; auto.
  Qed.

  Theorem readonly_iff P Q `{H1: AsMapsTo P Φ1} `{H2: AsMapsTo Q Φ2} :
    (∀ q, Φ1 q ≡ Φ2 q) ->
    readonly P -∗ readonly Q.
  Proof.
    unseal; rewrite /readonly_inner.
    intros Hequiv.
    iIntros "HP".
    iApply (ae_inv_iff with "HP").
    setoid_rewrite Hequiv.
    iIntros "!> !>".
    iSplit; auto.
  Qed.

  Global Instance readonly_sep P Q `{H1: AsMapsTo P Φ1} `{H2: AsMapsTo Q Φ2} :
    AsMapsTo (P ∗ Q) (λ q, Φ1 q ∗ Φ2 q)%I.
  Proof.
    split; try apply _.
    rewrite (as_mapsto (P:=P)) (as_mapsto (P:=Q)) //.
  Qed.

  Lemma Qclt_plus_r (q q': Qp) :
    Qcanon.Qclt q (q + q')%Qp.
  Proof.
    apply Qp_lt_sum; eauto.
  Qed.

  Theorem readonly_extend E P Q `{H1: AsMapsTo P Φ1} `{H2: AsMapsTo Q Φ2} :
    readonly P -∗ readonly Q ={E}=∗ readonly (P ∗ Q).
  Proof.
    iIntros "HPinv HQinv".
    iMod (readonly_load_lt with "HPinv") as (q1) "[% HP]".
    iMod (readonly_load_lt with "HQinv") as (q2) "[% HQ]".

    destruct (Qp_lower_bound q1 q2) as (qmin & q1' & q2' & [-> ->]).
    iDestruct "HP" as "[HP _]".
    iDestruct "HQ" as "[HQ _]".

    iMod (readonly_alloc (P ∗ Q) qmin with "[HP HQ]") as "$"; simpl; auto with iFrame.
    etrans; eauto.
    apply Qclt_plus_r.
  Qed.

  Theorem readonly_inner_sep Φ1 Φ2 :
    □ (∀ q, Φ1 q ↔ Φ2 q ∗ (Φ2 q -∗ Φ1 q)) -∗
    readonly_inner Φ1 ↔
    (* note that this is true, but it doesn't cleanly separate readonly into two
    halves to be able to use [inv_sep], and using [inv_alter] runs into a
    similar issue *)
    ∃ (q: Qp), ⌜Qcanon.Qclt q 1⌝ ∗ Φ2 q ∗ (Φ2 q -∗ Φ1 q).
  Proof.
    iIntros "#Hiff".
    iSplit.
    - iIntros "H1".
      iDestruct "H1" as (q) "[% H1]".
      iExists _; iFrame "%".
      iApply ("Hiff" with "H1").
    - iIntros "H12".
      iDestruct "H12" as (q) "(%&H2&H1)".
      iExists q; iFrame "%".
      iApply ("H1" with "H2").
  Qed.

  Theorem readonly_weaken E P Q `{H1: AsMapsTo P Φ1} `{H2: AsMapsTo Q Φ2} :
    (∀ q, Φ1 q -∗ Φ2 q) -∗
    readonly P ={E}=∗ readonly Q.
  Proof.
    iIntros "Himpl HP".
    iMod (readonly_load_lt with "HP") as (q) "[% HΦ1]".
    iDestruct ("Himpl" with "HΦ1") as "HΦ2".
    iMod (readonly_alloc with "HΦ2"); auto.
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
