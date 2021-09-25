From iris.algebra Require Import auth agree excl csum.
From Perennial.base_logic Require Import ae_invariants.
From iris.bi Require Export weakestpre.
From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic Require Export invariants fancy_updates2.
From Perennial.program_logic Require Import step_fupd_extra ae_invariants_mutable.
From Perennial.algebra Require Export own_discrete.
From Perennial.base_logic.lib Require Export ncfupd.
From iris.prelude Require Import options.
Import uPred.

(* first, define a modality for establishing crash conditions *)
Section cfupd.
  Context `{crashGS Σ} `{invGS Σ}.
  Implicit Types (P: iProp Σ).

  Definition cfupd E1 :=
    λ P, (C -∗ |={E1}=> P)%I.

  Lemma cfupd_wand  (E1 E1' : coPset) P Q:
    E1' ⊆ E1 →
    cfupd E1' P -∗
    (P -∗ Q) -∗
    cfupd E1 Q.
  Proof.
    iIntros (?) "HP HPQ".
    iIntros "HC". iSpecialize ("HP" with "[$]").
    iMod (fupd_mask_mono with "HP") as "HP"; auto.
    iModIntro. by iApply "HPQ".
  Qed.

  Global Instance cfupd_proper_ent E1 :
    Proper ((⊢) ==> (⊢)) (cfupd E1).
  Proof.
    iIntros (P Q Hent) "Hfupd".
    iApply (cfupd_wand with "Hfupd"); eauto.
    iApply Hent.
  Qed.

  Global Instance cfupd_proper_equiv E1 :
    Proper ((⊣⊢) ==> (⊣⊢)) (cfupd E1).
  Proof.
    intros P Q Hequiv.
    iSplit; iIntros "H".
    - iApply (cfupd_wand with "H"); eauto.
      rewrite Hequiv; auto.
    - iApply (cfupd_wand with "H"); eauto.
      rewrite Hequiv; auto.
  Qed.

  Global Instance from_modal_fupd_iter k E P :
    FromModal True modality_id
              (Nat.iter k (fupd E E) P)
              (Nat.iter k (fupd E E) P) P.
  Proof.
    rewrite /FromModal /=.
    iIntros (_) "HP".
    iInduction k as [|k] "IH".
    - simpl; auto.
    - simpl.
      iModIntro.
      iApply "IH"; iFrame.
  Qed.

  Theorem step_fupd_iter_intro k E1 E2 P :
    E2 ⊆ E1 →
    ▷^k P -∗ (Nat.iter k (fun P : iProp Σ =>
                        fupd E1 E2 (▷ (fupd E2 E1 P))) P).
  Proof.
    iIntros (?) "HP".
    iInduction k as [|k] "IH".
    - simpl; auto.
    - simpl.
      iMod (fupd_mask_subseteq E2) as "Hclo"; auto.
      iModIntro.
      iModIntro.
      iMod "Hclo" as "_".
      iModIntro.
      iApply ("IH" with "HP").
  Qed.

  Lemma fupd_iter_intro E1 k P :
    ▷^k P -∗ |={E1,E1}_(k)=> P.
  Proof.
    iIntros "HP".
    iMod (fupd_mask_subseteq ∅) as "Hclo"; first by set_solver.
    iModIntro.
    iApply step_fupd_iter_intro; first by set_solver.
    iModIntro.
    iMod "Hclo" as "_".
    by iFrame.
  Qed.

  Lemma step_fupd_mask_weaken_iter k E1 E2 P :
    E1 ⊆ E2 →
    ▷^k P -∗ |={E2,E1}_k=> P.
  Proof.
    iIntros (?) "HP".
    iApply step_fupd_iter_intro; first by set_solver.
    iMod (fupd_mask_subseteq ∅) as "Hclo"; first by set_solver.
    iModIntro. iModIntro.
    iMod "Hclo" as "_".
    iApply fupd_mask_intro_discard; auto.
  Qed.

  Global Instance from_modal_cfupd E1 P :
    FromModal True modality_id (cfupd E1 P) (cfupd E1 P) (P).
  Proof.
    rewrite /FromModal /=.
    iIntros (_) "HP".
    iIntros "_".
    iModIntro. by iFrame.
  Qed.

  Lemma ineq_to_diff n1 n2 :
    (n1 ≤ n2)%nat →
    ∃ n1' d,
      (n2 - n1 = d) ∧
      n1 = n1' ∧
      n2 = n1' + d.
  Proof.
    intros.
    exists n1, (n2-n1); lia.
  Qed.

  Theorem elim_modal_step_fupdN_subtract E1 E2 k1 k2 P Q :
    (k1 ≤ k2)%nat →
    (|={E1}[E2]▷=>^k1 P) -∗
    (P -∗ |={E1}[E2]▷=>^(k2-k1) Q) -∗
    |={E1}[E2]▷=>^k2 Q.
  Proof.
    iIntros (Hle) "HP HQ".
    destruct (ineq_to_diff _ _ Hle) as (k&kd&->&?&?); subst.
    clear Hle.
    iInduction k as [|k] "IH"; simpl.
    - iApply "HQ"; auto.
    - iMod "HP"; iModIntro. iNext.
      iMod "HP"; iModIntro.
      iApply ("IH" with "HP HQ").
  Qed.

  Theorem elim_modal_step_fupdN_mono E1 E2 k P Q :
    (|={E1}[E2]▷=>^k P) -∗
    (P -∗ Q) -∗
    |={E1}[E2]▷=>^k Q.
  Proof.
    iIntros "HP HQ".
    iApply (elim_modal_step_fupdN_subtract with "HP"); auto.
    replace (k-k) with 0 by lia; simpl.
    auto.
  Qed.

  Theorem elim_modal_step_fupd_masks k1 k2 E1 E2 P Q :
    (k1 ≤ k2)%nat →
    E1 ⊆ E2 →
    (|={E1,E2}_k1=> P) -∗
    (P -∗ (|={E1,E2}_(k2-k1)=> Q)) -∗
    (|={E1,E2}_k2=> Q).
  Proof.
    iIntros (Hle ?) "Hfupd HQ".
    (* rearrange theorem to an addition rather than a subtraction *)
    destruct (ineq_to_diff _ _ Hle) as (k&kd&->&?&?); subst; clear Hle.
    iApply step_fupdN_inner_plus.
    iMod "Hfupd". iModIntro.
    iApply (elim_modal_step_fupdN_mono with "Hfupd").
    iIntros "HP".
    iMod "HP".
    iSpecialize ("HQ" with "HP").
    iApply fupd_mask_intro_discard; auto.
  Qed.

  Lemma step_fupdN_fupd E1 E2 k P :
    E1 ⊆ E2 →
    (|={E1}▷=>^k |={E1,E2}=> P) ⊣⊢ (|={E1}=> |={E1}▷=>^k |={E1,E2}=> P).
  Proof.
    intros Hsub.
    destruct k; simpl.
    - iSplit; iIntros "H".
      + iMod "H".
        iApply fupd_mask_intro_subseteq; auto.
      + iMod "H"; auto.
    - iSplit; iIntros "H".
      + by iFrame.
      + by iMod "H".
  Qed.

  Lemma step_fupdN_fupd_empty E2 k P :
    (|={∅}▷=>^k |={∅,E2}=> P) ⊣⊢ (|={∅}=> |={∅}▷=>^k |={∅,E2}=> P).
  Proof.
    apply step_fupdN_fupd; set_solver.
  Qed.

  Theorem elim_modal_step_fupd_masks_trans k1 k2 E1 E2 E3 P Q :
    (k1 ≤ k2)%nat →
    (|={E1,E2}_k1=> P) -∗
    (P -∗ (|={E2,E3}_(k2-k1)=> Q)) -∗
    (|={E1,E3}_k2=> Q).
  Proof.
    iIntros (Hle) "Hfupd HQ".
    (* rearrange theorem to an addition rather than a subtraction *)
    destruct (ineq_to_diff _ _ Hle) as (k&kd&->&?&?); subst; clear Hle.
    iApply (elim_modal_step_fupdN_subtract with "Hfupd"); first lia.
    iIntros "HP".
    iEval (rewrite step_fupdN_fupd_empty).
    iMod "HP".
    iMod ("HQ" with "HP") as "HQ".
    iModIntro.
    iApply (elim_modal_step_fupdN_subtract with "HQ"); first lia.
    iIntros "HQ".
    iApply step_fupd_iter_intro; auto.
  Qed.

  Lemma step_fupdN_weaken_mask E1 E1' k P :
    E1' ⊆ E1 →
    (|={E1',E1'}_k=> P) -∗
    |={E1,E1}_k=> P.
  Proof.
    iIntros (?) "HP".
    iMod (fupd_mask_subseteq E1') as "Hclo"; first auto.
    iApply (elim_modal_step_fupdN_mono with "HP").
    iIntros "HP".
    iMod "HP".
    iMod "Hclo" as "_".
    auto.
  Qed.

  Theorem cfupd_weaken_mask E1 E1' P :
    E1' ⊆ E1 →
    cfupd  E1'  P -∗ cfupd E1 P.
  Proof.
    iIntros (?) "H".
    iApply (cfupd_wand with "[$]"); eauto.
  Qed.

  (* these instances are local to avoid breaking the proofs in this file *)

  Local Instance elim_modal_step_fupd p k1 k2 E P Q :
    ElimModal (k1 ≤ k2)%nat p false (|={E,E}_k1=> P) P
              (|={E,E}_k2=> Q) (|={E,E}_(k2-k1)=> Q).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim /=.
    iIntros (?) "[Hfupd HQ]".
    iApply (elim_modal_step_fupd_masks with "Hfupd"); auto.
  Qed.

  Local Instance elim_modal_step_fupd_same p k E P Q :
    ElimModal True p false (|={E,E}_k=> P) P
              (|={E,E}_k=> Q) (|={E}=> Q).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim.
    iIntros (?) "[Hfupd HQ]".
    iMod "Hfupd" as "HP".
    replace (k-k) with 0 by lia.
    simpl.
    iSpecialize ("HQ" with "HP").
    iMod "HQ".
    iApply fupd_mask_intro_subseteq; first set_solver; auto.
  Qed.

  Global Instance elim_modal_cfupd p E1 P Q :
    ElimModal True p false (cfupd E1 P) (P)
              (cfupd E1 Q) (cfupd E1 Q).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim /cfupd /=.
    iIntros (?) "[Hfupd HQ]".
    iIntros "#HC".
    iSpecialize ("Hfupd" with "HC").
    iMod "Hfupd".
    iMod ("HQ" with "Hfupd HC") as "HQ".
    iModIntro. auto.
  Qed.

  Global Instance cfupd_frame p E1 R P Q :
    Frame p R P Q →
    Frame p R (cfupd E1 P) (cfupd E1 Q).
  Proof.
    rewrite /Frame.
    iIntros (Hframe) "[HR Hfupd]".
    iIntros "HC".
    iSpecialize ("Hfupd" with "HC").
    iMod "Hfupd". iModIntro. iApply Hframe; by iFrame.
  Qed.

  Lemma cfupd_big_sepL_aux {A} (l: list A) (Φ: nat → A → iProp Σ) n E1 :
    ([∗ list] i↦a ∈ l, cfupd E1 (Φ (n + i) a)) -∗
    cfupd E1 ([∗ list] i↦a ∈ l, Φ (n + i) a).
  Proof.
    iIntros "H".
    iInduction l as [| x l] "IH" forall (n).
    - iModIntro.
      simpl; auto.
    - rewrite -> !big_sepL_cons by set_solver.
      simpl.
      iDestruct "H" as "(Hx & Hrest)".
      iMod "Hx".
      iFrame "Hx".
      assert (forall k, n + S k = S n + k) as Harith by lia.
      setoid_rewrite Harith.
      iMod ("IH" with "Hrest") as "Hrest".
      iModIntro. eauto.
  Qed.

  Lemma cfupd_big_sepL {A} (l: list A) (Φ: nat → A → iProp Σ) E1 :
    ([∗ list] i↦a ∈ l, cfupd E1 (Φ i a)) -∗
    cfupd E1 ([∗ list] i↦a ∈ l, Φ i a).
  Proof. iApply (cfupd_big_sepL_aux _ _ 0). Qed.

  Lemma cfupd_big_sepS `{Countable A} (σ: gset A)(P: A → iProp Σ) E1  :
    ([∗ set] a ∈ σ, cfupd E1 (P a)) -∗
    cfupd E1 ([∗ set] a ∈ σ, P a).
  Proof. rewrite big_opS_eq. apply cfupd_big_sepL. Qed.

  Lemma is_except_0_wand {PROP:bi} (P Q: PROP) :
    IsExcept0 Q → IsExcept0 (P -∗ Q).
  Proof.
    rewrite /IsExcept0.
    intros HQ.
    rewrite -{2}HQ.
    iIntros ">HQ HP !>".
    iApply ("HQ" with "HP").
  Qed.

  Global Instance cfupd_is_except0 E Q : IsExcept0 (cfupd E Q).
  Proof.
    rewrite /cfupd.
    apply is_except_0_wand.
    apply _.
  Qed.

  Global Instance from_pure_cfupd a E P φ :
    FromPure a P φ → FromPure a (cfupd E P) φ.
  Proof.
    rewrite /FromPure=> HP. iIntros "? !>". by iApply HP.
  Qed.

End cfupd.

(* Open to alternative notation for this. *)
Notation "|C={ E1 }=> P" := (cfupd E1 P)
      (at level 99, E1 at level 50, P at level 200,
       format "'[  ' |C={ E1 }=>  '/' P ']'").

Global Hint Extern 1 (environments.envs_entails _ (|C={_}=> _)) => iModIntro : core.
