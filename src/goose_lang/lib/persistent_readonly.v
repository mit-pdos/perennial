From Coq.QArith Require Import Qcanon.
From Perennial.Helpers Require Import Qextra.
From Perennial.base_logic.lib Require Import ae_invariants.
From iris.bi.lib Require Import fractional.
From Perennial.Helpers Require Import iris.
From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import lifting.
From Perennial.goose_lang Require Import proofmode.
From Perennial.base_logic.lib Require Import ghost_map.

Set Default Proof Using "Type".

Section goose_lang.
  Context `{!invGS Σ}.

  Class AsMapsTo (P: iProp Σ)
        (Φ : Qp -> iProp Σ) : Set :=
    { as_pointsto : P ≡ Φ 1%Qp;
      as_pointsto_fractional :> Fractional Φ;
      as_pointsto_timeless :> ∀ q, Timeless (Φ q);
    }.

  Arguments as_pointsto {P Φ} AsMapsTo.

  Definition readonly_def P `{H: AsMapsTo P Φ}: iProp Σ :=
    □ |={∅}=> ∃ q, Φ q.
  Definition readonly_aux : seal (@readonly_def). Proof. by eexists. Qed.
  Definition readonly := readonly_aux.(unseal).
  Definition readonly_eq : @readonly = @readonly_def := readonly_aux.(seal_eq).
  Arguments readonly P {Φ}%function_scope {H}.

  Ltac unseal := rewrite readonly_eq /readonly_def.

  Theorem readonly_alloc P `{H: AsMapsTo P Φ} (q:Qp) E :
    Φ q ={E}=∗ readonly P.
  Proof.
    unseal.
    iIntros "HP".
    iMod (ae_inv_alloc 0 None _ (∃ q, Φ q) with "[HP]") as "#Hro"; auto.
    clear q. iIntros "!> !>".
    iApply fupd_split_level_fupd.
    iApply (ae_inv_acc_bupd with "Hro []").
    iIntros ">Hinner !> !>".
    iDestruct "Hinner" as (q) "HΦ".
    (* Import the required instance (which is not registered by default *)
    pose proof @fractional_as_fractional as fractional_instance.
    iDestruct "HΦ" as "[HΦ1 HΦ2]".
    iSplitL "HΦ1".
    - iNext. iExists (q/2)%Qp. done.
    - iExists (q/2)%Qp. done.
  Qed.

  Global Instance readonly_persistent P `{H: AsMapsTo P Φ} : Persistent (readonly P).
  Proof. unseal; apply _. Qed.

  Instance as_pointsto_AsFractional P `{H: AsMapsTo P Φ} q :
    AsFractional (Φ q) (λ q, Φ q) q.
  Proof.
    split; auto.
    apply _.
  Qed.

  Theorem readonly_alloc_1 P `{H: AsMapsTo P Φ} E :
    P ={E}=∗ readonly P.
  Proof.
    iIntros "HP".
    rewrite {1}H.(as_pointsto).
    iApply (readonly_alloc with "HP").
  Qed.

  Theorem readonly_load_lt E P `{H: AsMapsTo P Φ} :
    readonly P -∗ |={E}=> ∃ (q: Qp), ⌜(q < 1)%Qp⌝ ∗ Φ q.
  Proof.
    unseal.
    iIntros "#Hro".
    iApply (fupd_mask_mono ∅); first solve_ndisj.
    iMod ("Hro") as (q) "HΦ".
    destruct (Qp.lower_bound q 1) as (qmin & q1' & q2' & [-> Hone]).
    iDestruct "HΦ" as "[HΦ _]". iExists qmin. iFrame. iPureIntro.
    eapply (Qp.lt_sum _ 1). eauto.
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
    unseal.
    intros Hequiv.
    setoid_rewrite Hequiv. auto.
  Qed.

  Global Instance readonly_sep P Q `{H1: AsMapsTo P Φ1} `{H2: AsMapsTo Q Φ2} :
    AsMapsTo (P ∗ Q) (λ q, Φ1 q ∗ Φ2 q)%I.
  Proof.
    split; try apply _.
    rewrite (as_pointsto (P:=P)) (as_pointsto (P:=Q)) //.
  Qed.

  Theorem readonly_extend P Q `{H1: AsMapsTo P Φ1} `{H2: AsMapsTo Q Φ2} :
    readonly P -∗ readonly Q -∗ readonly (P ∗ Q).
  Proof.
    unseal. iIntros "#HPinv #HQinv". iIntros "!>".
    iMod "HPinv" as (q1) "HΦ1".
    iMod "HQinv" as (q2) "HΦ2".

    destruct (Qp.lower_bound q1 q2) as (qmin & q1' & q2' & [-> ->]).
    iDestruct "HΦ1" as "[HΦ1 _]".
    iDestruct "HΦ2" as "[HΦ2 _]".
    iExists _. by iFrame.
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

#[global]
Instance heap_pointsto_AsMapsTo `{ext: !ffi_syntax} `{!na_heapGS loc val Σ}
         (l: loc) (v: val) :
  AsMapsTo (l ↦ v) (λ q, l ↦{#q} v)%I.
Proof.
  split; [done|apply _|apply _].
Qed.

#[global]
Instance ghost_map_auth_AsMapsTo `{ghost_mapG Σ K V} γ (m:gmap K V) :
  AsMapsTo (ghost_map_auth γ 1 m) (λ q, ghost_map_auth γ q m)%I.
Proof.
  split; [done|apply _|apply _].
Qed.

#[global]
Hint Mode AsMapsTo - + - : typeclass_instances.
Typeclasses Opaque readonly.
Arguments readonly {Σ _} _%bi_scope {Φ}%function_scope {H}.
