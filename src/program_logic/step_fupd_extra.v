From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export invariants.
Set Default Proof Using "Type".
Import uPred.


Notation "|={ E1 , E2 }_ k => P" :=
    (|={E1, ∅}=> |={∅, ∅}▷=>^k |={∅, E2}=> P)%I
      (at level 99, E1, E2 at level 50, k at level 9, P at level 200,
       format "|={ E1 , E2 }_ k =>  P").


Notation "|={ E }_ k =>^ n P" :=
    (Nat.iter n (λ Q, (|={E%I, ∅}=> |={∅, ∅}▷=>^k |={∅, E}=> Q)) P)%I
      (at level 99, E at level 50, k, n at level 9, P at level 200,
       format "|={ E }_ k =>^ n  P").


Section step_fupdN.

Context {PROP: bi} {H: BiFUpd PROP} {HAff: BiAffine PROP}.
Implicit Types P Q: PROP.

Lemma step_fupd_sep E P Q : (|={E}▷=> P) ∗ (|={E}▷=> Q) -∗ |={E}▷=> P ∗ Q.
Proof using HAff.
  iIntros "(>H1&>H2)".
  iModIntro. iNext. iMod "H1". iMod "H2". by iFrame.
Qed.

Lemma step_fupdN_sep P Q k  : (|={∅,∅}_k=> P) ∗ (|={∅,∅}_k=> Q) -∗ |={∅, ∅}_k=> P ∗ Q.
Proof using HAff.
  iInduction k as [| k] "IH".
  - iIntros "(>>HP&>>HQ) !> !>". iFrame.
  - iIntros "(>>HP&>>HQ) !> !> !>".
    iApply ("IH" with "[$]").
Qed.

Lemma step_fupdN_le {E1 E2 : coPset} (n1 n2 : nat) (P: PROP):
  E2 ⊆ E1 →
  n1 ≤ n2 → (|={E1,E2}▷=>^n1 P) -∗ |={E1,E2}▷=>^n2 P.
Proof.
  intros ?. induction 1 => //=.
  iIntros. iApply step_fupd_intro; auto. iNext. by iApply IHle.
Qed.

Lemma step_fupdN_fupd_swap {E : coPset} (P: PROP) (n: nat):
  (|={E,E}▷=>^n |={E}=> P) -∗ |={E}=> |={E, E}▷=>^n P.
Proof.
  induction n => //=.
  iIntros "H". iMod "H". iModIntro. iModIntro. iNext. iMod "H".
  by iApply IHn.
Qed.

Lemma step_fupdN_later E1 E2 k (P: PROP):
  E2 ⊆ E1 →
  ▷^k P -∗ |={E1,E2}▷=>^k P.
Proof using HAff.
  iIntros (Hle).
  iInduction k as [| k] "IH".
  - eauto.
  - iIntros. rewrite Nat_iter_S. iMod (fupd_intro_mask' _ E2) as "Hclo".
    { set_solver. }
    iModIntro. iModIntro. iMod "Hclo". iModIntro. by iApply "IH".
Qed.

Lemma step_fupdN_inner_later' E1 E2 k (P: PROP):
  (▷^k |={E1, E2}=> P)%I -∗ |={E1,∅}=> |={∅,∅}▷=>^k |={∅,E2}=> P.
Proof using HAff.
  iInduction k as [| k] "IH".
  - rewrite //=. iIntros "HP".
    iMod "HP".
    iApply fupd_intro_mask; eauto; first set_solver.
  - iIntros. iMod (fupd_intro_mask' _ ∅) as "Hclo".
    { set_solver. }
    rewrite Nat_iter_S.
    iModIntro. iModIntro. iNext. iMod "Hclo". by iApply "IH".
Qed.

Lemma step_fupdN_inner_later E1 E2 k (P: PROP):
  E2 ⊆ E1 →
  ▷^k P -∗ |={E1,∅}=> |={∅,∅}▷=>^k |={∅,E2}=> P.
Proof using HAff.
  iIntros (Hle) "H".
  iApply step_fupdN_inner_later'.
  iNext. iMod (fupd_intro_mask' _ E2) as "?"; eauto.
Qed.

Lemma step_fupdN_inner_fupd E1 E2 k (P: PROP):
  (|={E1,∅}=> |={∅,∅}▷=>^k |={∅,E2}=> |={E2}=> P) -∗
  |={E1,∅}=> |={∅,∅}▷=>^k |={∅,E2}=> P.
Proof.
  iIntros "H". iMod "H". iApply (step_fupdN_wand with "H").
  iModIntro. iIntros "H". by iMod "H".
Qed.

Lemma step_fupdN_inner_plain `{BP: BiPlainly PROP} `{@BiFUpdPlainly PROP H BP}
      (k: nat) (P: PROP) :
  Plain P →
  ⊢ (|={⊤, ∅}=> |={∅, ∅}▷=>^k |={∅, ∅}=> P) -∗
  |={⊤}=> ▷^(S k) P.
Proof.
  iIntros (HPlain).
  iInduction k as [| k] "IH" forall (P HPlain).
  - rewrite //=. iIntros "H". iApply fupd_plain_mask. do 2 iMod "H".
    by iModIntro.
  - iIntros "H".
    iApply fupd_plain_mask.
    iMod "H". rewrite -step_fupdN_S_fupd.
    iMod (step_fupdN_plain with "H") as "H".
    iModIntro. rewrite -!later_laterN !laterN_later.
    iNext. iNext. by iMod "H".
Qed.

Lemma step_fupdN_inner_wand E1 E2 k1 k2 (P Q: PROP):
  E2 ⊆ E1 →
  k2 ≤ k1 →
  (|={E2,∅}=> |={∅,∅}▷=>^k2 |={∅,E2}=> P) -∗
  (P -∗ Q) -∗
  |={E1,∅}=> |={∅,∅}▷=>^k1 |={∅,E1}=> Q.
Proof.
  iIntros (??) "HP HPQ".
  iMod (fupd_intro_mask' _ E2) as "Hclo"; auto.
  iMod "HP". iModIntro.
  iApply (step_fupdN_le k2 _); auto.
  iApply (step_fupdN_wand with "HP").
  iIntros "HP". iMod "HP". iMod "Hclo" as "_".
  iModIntro. by iApply "HPQ".
Qed.

Lemma step_fupdN_inner_frame_l E k (P Q: PROP):
  Q ∗ (|={E,E}_k=> P) -∗ (|={E,E}_k=> Q ∗ P).
Proof using HAff.
  iIntros "(HQ&H)". iApply (step_fupdN_inner_wand with "H"); eauto.
  iIntros; iFrame.
Qed.

Lemma step_fupdN_inner_frame_r E k (P Q: PROP):
  (|={E,E}_k=> P) ∗ Q -∗ (|={E,E}_k=> P ∗ Q).
Proof using HAff.
  iIntros "(H&HQ)". iApply (step_fupdN_inner_wand with "H"); eauto.
  iIntros; iFrame.
Qed.

Lemma step_fupdN_innerN_wand E1 E2 k1 k2 n1 n2 (P Q: PROP):
  E2 ⊆ E1 →
  k2 ≤ k1 →
  n2 ≤ n1 →
  (|={E2}_k2=>^n2 P) -∗
  (P -∗ Q) -∗
  (|={E1}_k1=>^n1 Q).
Proof using HAff.
  iIntros (?? Hle) "HP HPQ".
  iInduction Hle as [] "IH".
  {
    iInduction n2 as [|n2] "IH".
    { iApply "HPQ". eauto. }
    rewrite !Nat_iter_S.
    iApply  (step_fupdN_inner_wand with "HP"); auto.
    iIntros. iApply ("IH" with "[$] [$]").
  }
  rewrite Nat_iter_S.
  iApply (step_fupdN_inner_later); first auto.
  iNext. by iApply ("IH" with "[$] [$]").
Qed.

Lemma step_fupdN_inner_wand' E1 E1' E2 E2' k1 k2 (P Q: PROP):
  E2 ⊆ E1 →
  E1' ⊆ E2' →
  k2 ≤ k1 →
  (|={E2,∅}=> |={∅,∅}▷=>^k2 |={∅,E2'}=> P) -∗
  (P -∗ Q) -∗
  |={E1,∅}=> |={∅,∅}▷=>^k1 |={∅,E1'}=> Q.
Proof using HAff.
  iIntros (???) "HP HPQ".
  iMod (fupd_intro_mask' _ E2) as "Hclo"; auto.
  iMod "HP". iModIntro.
  iApply (step_fupdN_le k2 _); auto.
  iApply (step_fupdN_wand with "HP").
  iIntros "HP". iMod "HP". iApply fupd_mask_weaken; auto.
  by iApply "HPQ".
Qed.

Lemma step_fupdN_innerN_wand' E k n (P Q: PROP):
  (|={E}_k=>^n P) -∗
  (P -∗ Q) -∗
  |={E}_k=>^n Q.
Proof using HAff.
  iIntros "HP HPQ". iInduction n as [| n] "IH".
  - rewrite //=. by iApply "HPQ".
  - rewrite //=. iApply (step_fupdN_inner_wand' with "HP"); eauto.
    iIntros; by iApply ("IH" with "[$] [$]").
Qed.

Lemma step_fupdN_innerN_S_fupd E k n (P: PROP):
  (|={E}_k=>^(S n) |={E}=> P) -∗
  (|={E}_k=>^(S n) P).
Proof using HAff.
  rewrite !Nat_iter_S_r.
  iIntros "H". iApply (step_fupdN_innerN_wand' with "H").
  iApply step_fupdN_inner_fupd.
Qed.

Lemma step_fupdN_inner_plus E1 E2 k1 k2 (P: PROP):
  (|={E1,∅}=> |={∅,∅}▷=>^k1 |={∅, E1}=> |={E1,∅}=> |={∅,∅}▷=>^k2 |={∅,E2}=> P)
  ⊢ |={E1,∅}=> |={∅,∅}▷=>^(k1 + k2) |={∅,E2}=> P.
Proof using HAff.
  rewrite Nat_iter_add.
  iIntros "H". iMod "H". iModIntro.
  iApply (step_fupdN_mono with "H"). iIntros "H".
  destruct k2.
  * simpl. do 3 iMod "H". eauto.
  * rewrite Nat_iter_S. iMod "H". iMod "H". eauto.
Qed.

Lemma step_fupdN_inner_plus' E1 k1 k2 (P: PROP):
  (|={E1,∅}_k1=> |={∅,∅}_k2=> P)
  ⊢ |={E1,∅}_(k1+k2)=> P.
Proof using HAff.
  rewrite Nat_iter_add.
  iIntros "H". iMod "H". iModIntro.
  iApply (step_fupdN_mono with "H"). iIntros "H".
  destruct k2.
  * simpl. do 3 iMod "H". eauto.
  * rewrite Nat_iter_S. iMod "H". iMod "H". eauto.
Qed.

Lemma step_fupdN_ne E1 E2 n:
  NonExpansive (λ (P: PROP), |={E1, E2}▷=>^n P)%I.
Proof.
  induction n => //=.
  - apply _.
  - intros ? P Q ->. eauto.
Qed.

Lemma step_fupdN_inner_plain' `{BP: BiPlainly PROP} `{@BiFUpdPlainly PROP H BP}
      (k: nat) (P: PROP) :
  Plain P →
  ⊢ (|={⊤, ⊤}_k=> P) -∗
  |={⊤}=> ▷^(S k) P.
Proof using HAff.
  iIntros (HPlain).
  iInduction k as [| k] "IH" forall (P HPlain).
  - rewrite //=. iIntros "H". do 2 iMod "H". eauto.
  - iIntros "H".
    iApply (fupd_plain_mask _ ∅).
    iMod "H".
    iDestruct (step_fupdN_wand _ _ _ _ (|={∅}=> P)%I with "H []") as "H".
    { iIntros "H". iMod "H". iApply fupd_mask_weaken; eauto. }
    rewrite -step_fupdN_S_fupd.
    iMod (step_fupdN_plain with "H") as "H".
    iModIntro. rewrite -!later_laterN !laterN_later.
    iNext. iNext. by iMod "H".
Qed.

Lemma step_fupdN_innerN_plain `{BP: BiPlainly PROP} `{@BiFUpdPlainly PROP H BP}
      (k n: nat) (P: PROP) :
  Plain P →
  ⊢ (|={⊤}_k=>^n P) -∗
  |={⊤}=> ▷^(n * (S k)) P.
Proof using HAff.
  iIntros (HPlain).
  iInduction n as [| n] "IH" forall (P HPlain).
  - rewrite //=. eauto.
  - iIntros "H".
    rewrite Nat_iter_S.
    iDestruct (step_fupdN_inner_wand with "H []") as "H";
      [ reflexivity | reflexivity | |].
    { iApply "IH"; eauto. }
    rewrite step_fupdN_inner_fupd.
    iMod (step_fupdN_inner_plain' with "H") as "H".
    iModIntro. replace (S n * S k) with (S k + (n * S k)) by lia.
    rewrite laterN_plus; eauto.
Qed.

End step_fupdN.
