From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic Require Export invariants fancy_updates2.
Set Default Proof Using "Type".
Import uPred.


Notation "|={ E1 , E2 }_ k => P" :=
    (|={E1, ∅}=> |={∅}[∅]▷=>^k |={∅, E2}=> P)%I
      (at level 99, E1, E2 at level 50, k at level 9, P at level 200,
       format "|={ E1 , E2 }_ k =>  P").


Notation "|={ E }_ k =>^ n P" :=
    (Nat.iter n (λ Q, (|={E%I, ∅}=> |={∅}[∅]▷=>^k |={∅, E}=> Q)) P)%I
      (at level 99, E at level 50, k, n at level 9, P at level 200,
       format "|={ E }_ k =>^ n  P").

Notation "||▷=> Q" := (||={∅|∅, ∅|∅}=> ▷ ||={∅|∅, ∅|∅}=> Q)%I
  (at level 99, Q at level 200,
   format "||▷=> Q") : bi_scope.
Notation "||▷=>^ n Q" := (Nat.iter n (λ P, ||▷=> P)%I Q)
  (at level 99, n at level 9, Q at level 200,
   format "||▷=>^ n  Q") : bi_scope.

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
  n1 ≤ n2 → (|={E1}[E2]▷=>^n1 P) -∗ |={E1}[E2]▷=>^n2 P.
Proof.
  intros ?. induction 1 => //=.
  iIntros. iApply step_fupd_intro; auto. iNext. by iApply IHle.
Qed.

Lemma step_fupdN_fupd_swap {E : coPset} (P: PROP) (n: nat):
  (|={E}▷=>^n |={E}=> P) -∗ |={E}=> |={E}▷=>^n P.
Proof.
  induction n => //=.
  iIntros "H". iMod "H". iModIntro. iModIntro. iNext. iMod "H".
  by iApply IHn.
Qed.

Lemma step_fupdN_later E1 E2 k (P: PROP):
  E2 ⊆ E1 →
  ▷^k P -∗ |={E1}[E2]▷=>^k P.
Proof using HAff.
  iIntros (Hle).
  iInduction k as [| k] "IH".
  - eauto.
  - iIntros. rewrite Nat.iter_succ. iMod (fupd_mask_subseteq E2) as "Hclo".
    { set_solver. }
    iModIntro. iModIntro. iMod "Hclo". iModIntro. by iApply "IH".
Qed.

Lemma step_fupdN_inner_later' E1 E2 k (P: PROP):
  (▷^k |={E1, E2}=> P)%I -∗ |={E1,∅}=> |={∅}▷=>^k |={∅,E2}=> P.
Proof using HAff.
  iInduction k as [| k] "IH".
  - rewrite //=. iIntros "HP".
    iMod "HP".
    iApply fupd_mask_intro_subseteq; eauto; first set_solver.
  - iIntros. iMod (fupd_mask_subseteq ∅) as "Hclo".
    { set_solver. }
    rewrite Nat.iter_succ.
    iModIntro. iModIntro. iNext. iMod "Hclo". by iApply "IH".
Qed.

Lemma step_fupdN_inner_later E1 E2 k (P: PROP):
  E2 ⊆ E1 →
  ▷^k P -∗ |={E1,∅}=> |={∅}▷=>^k |={∅,E2}=> P.
Proof using HAff.
  iIntros (Hle) "H".
  iApply step_fupdN_inner_later'.
  iNext. iMod (fupd_mask_subseteq E2) as "?"; eauto.
Qed.

Lemma step_fupdN_inner_fupd E1 E2 k (P: PROP):
  (|={E1,∅}=> |={∅}▷=>^k |={∅,E2}=> |={E2}=> P) -∗
  |={E1,∅}=> |={∅}▷=>^k |={∅,E2}=> P.
Proof.
  iIntros "H". iMod "H". iApply (step_fupdN_wand with "H").
  iModIntro. iIntros "H". by iMod "H".
Qed.

Lemma step_fupdN_inner_plain `{BP: BiPlainly PROP} `{@BiFUpdPlainly PROP H BP}
      (k: nat) (P: PROP) :
  Plain P →
  ⊢ (|={⊤, ∅}=> |={∅}▷=>^k |={∅}=> P) -∗
  |={⊤}=> ▷^(S k) P.
Proof using HAff.
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
  (|={E2,∅}=> |={∅}▷=>^k2 |={∅,E2}=> P) -∗
  (P -∗ Q) -∗
  |={E1,∅}=> |={∅}▷=>^k1 |={∅,E1}=> Q.
Proof.
  iIntros (??) "HP HPQ".
  iMod (fupd_mask_subseteq E2) as "Hclo"; auto.
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
    rewrite !Nat.iter_succ.
    iApply  (step_fupdN_inner_wand with "HP"); auto.
    iIntros. iApply ("IH" with "[$] [$]").
  }
  rewrite Nat.iter_succ.
  iApply (step_fupdN_inner_later); first auto.
  iNext. by iApply ("IH" with "[$] [$]").
Qed.

Lemma step_fupdN_inner_wand' E1 E1' E2 E2' k1 k2 (P Q: PROP):
  E2 ⊆ E1 →
  E1' ⊆ E2' →
  k2 ≤ k1 →
  (|={E2,∅}=> |={∅}▷=>^k2 |={∅,E2'}=> P) -∗
  (P -∗ Q) -∗
  |={E1,∅}=> |={∅}▷=>^k1 |={∅,E1'}=> Q.
Proof using HAff.
  iIntros (???) "HP HPQ".
  iMod (fupd_mask_subseteq E2) as "Hclo"; auto.
  iMod "HP". iModIntro.
  iApply (step_fupdN_le k2 _); auto.
  iApply (step_fupdN_wand with "HP").
  iIntros "HP". iMod "HP". iApply fupd_mask_intro_discard; auto.
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
  rewrite !Nat.iter_succ_r.
  iIntros "H". iApply (step_fupdN_innerN_wand' with "H").
  iApply step_fupdN_inner_fupd.
Qed.

Lemma step_fupdN_inner_add E1 E2 k1 k2 (P: PROP):
  (|={E1,∅}=> |={∅}▷=>^k1 |={∅, E1}=> |={E1,∅}=> |={∅}▷=>^k2 |={∅,E2}=> P)
  ⊢ |={E1,∅}=> |={∅}▷=>^(k1 + k2) |={∅,E2}=> P.
Proof using HAff.
  rewrite Nat.iter_add.
  iIntros "H". iMod "H". iModIntro.
  iApply (step_fupdN_mono with "H"). iIntros "H".
  destruct k2.
  * simpl. do 3 iMod "H". eauto.
  * rewrite Nat.iter_succ. iMod "H". iMod "H". eauto.
Qed.

Lemma step_fupdN_inner_add' E1 k1 k2 (P: PROP):
  (|={E1,∅}_k1=> |={∅,∅}_k2=> P)
  ⊢ |={E1,∅}_(k1+k2)=> P.
Proof using HAff.
  rewrite Nat.iter_add.
  iIntros "H". iMod "H". iModIntro.
  iApply (step_fupdN_mono with "H"). iIntros "H".
  destruct k2.
  * simpl. do 3 iMod "H". eauto.
  * rewrite Nat.iter_succ. iMod "H". iMod "H". eauto.
Qed.

Lemma step_fupdN_ne E1 E2 n:
  NonExpansive (λ (P: PROP), |={E1}[E2]▷=>^n P)%I.
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
    rewrite Nat.iter_succ.
    iDestruct (step_fupdN_inner_wand with "H []") as "H";
      [ reflexivity | reflexivity | |].
    { iApply "IH"; eauto. }
    rewrite step_fupdN_inner_fupd.
    iMod (step_fupdN_inner_plain' with "H") as "H".
    iModIntro. replace (S n * S k) with (S k + (n * S k)) by lia.
    rewrite laterN_add; eauto.
Qed.

End step_fupdN.

Section step_fupd2.
Context `{!invGS Σ}.
Lemma step_fupd2N_ne n:
  NonExpansive (λ (P: iProp Σ), ||▷=>^n P)%I.
Proof.
  induction n => //=.
  - apply _.
  - intros ? P Q ->. eauto.
Qed.

Lemma step_fupd2N_wand n P Q :
  (||▷=>^n P) -∗ (P -∗ Q) -∗ (||▷=>^n Q).
Proof.
  apply wand_intro_l. induction n as [|n IH]=> /=.
  { by rewrite wand_elim_l. }
  rewrite -IH -fupd2_frame_l later_sep -fupd2_frame_l.
  by apply sep_mono; first apply later_intro.
Qed.

Lemma step_fupd2N_later k P:
  ▷^k P -∗ ||▷=>^k P.
Proof.
  iInduction k as [| k] "IH".
  - eauto.
  - iIntros. rewrite Nat.iter_succ.
    iModIntro. iModIntro. iModIntro. by iApply "IH".
Qed.

Lemma step_fupd2N_inner_later' E1a E1b E2a E2b k (P: iProp Σ):
  (▷^k ||={E1a|E1b, E2a|E2b}=> P)%I -∗ ||={E1a|E1b,∅|∅}=> ||▷=>^k ||={∅|∅,E2a|E2b}=> P.
Proof.
  iInduction k as [| k] "IH".
  - rewrite //=. iIntros "HP".
    iMod "HP".
    iApply fupd2_mask_intro_subseteq; eauto; try set_solver.
  - iIntros. iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo".
    { set_solver. }
    { set_solver. }
    rewrite Nat.iter_succ.
    iModIntro. iModIntro. iNext. iMod "Hclo". by iApply "IH".
Qed.

Lemma step_fupd2N_inner_later E1a E1b E2a E2b k (P: iProp Σ):
  E2a ⊆ E1a →
  E2b ⊆ E1b →
  ▷^k P -∗ ||={E1a|E1b,∅|∅}=> ||▷=>^k ||={∅|∅,E2a|E2b}=> P.
Proof.
  iIntros (Hle1 Hle2) "H".
  iApply step_fupd2N_inner_later'.
  iNext. iMod (fupd2_mask_subseteq E2a E2b) as "?"; eauto.
Qed.

Lemma step_fupd2N_inner_fupd2 E1a E1b E2a E2b k P:
  (||={E1a|E1b,∅|∅}=> ||▷=>^k ||={∅|∅,E2a|E2b}=> ||={E2a|E2b,E2a|E2b}=> P) -∗
  ||={E1a|E1b,∅|∅}=> ||▷=>^k ||={∅|∅,E2a|E2b}=> P.
Proof.
  iIntros "H". iMod "H". iApply (step_fupd2N_wand with "H").
  iModIntro. iIntros "H". by iMod "H".
Qed.

Lemma step_fupd2N_inner_fupd E1a E1b E2a E2b k P:
  (||={E1a|E1b,∅|∅}=> ||▷=>^k ||={∅|∅,E2a|E2b}=> |={E2a}=> P) -∗
  ||={E1a|E1b,∅|∅}=> ||▷=>^k ||={∅|∅,E2a|E2b}=> P.
Proof.
  iIntros "H". iMod "H". iApply (step_fupd2N_wand with "H").
  iModIntro. iIntros "H". do 2 iMod "H". auto.
Qed.

Lemma step_fupd2N_le (n1 n2 : nat) P :
  n1 ≤ n2 → (||▷=>^n1 P) -∗ ||▷=>^n2 P.
Proof.
  induction 1 => //=.
  iIntros. iApply step_fupd2_intro; auto. iNext. by iApply IHle.
Qed.

Lemma step_fupd2N_inner_wand E1a E1b E2a E2b k1 k2 P Q:
  E2a ⊆ E1a →
  E2b ⊆ E1b →
  k2 ≤ k1 →
  (||={E2a|E2b,∅|∅}=> ||▷=>^k2 ||={∅|∅,E2a|E2b}=> P) -∗
  (P -∗ Q) -∗
  ||={E1a|E1b,∅|∅}=> ||▷=>^k1 ||={∅|∅,E1a|E1b}=> Q.
Proof.
  iIntros (???) "HP HPQ".
  iMod (fupd2_mask_subseteq E2a E2b) as "Hclo"; auto.
  iMod "HP". iModIntro.
  iApply (step_fupd2N_le k2 _); auto.
  iApply (step_fupd2N_wand with "HP").
  iIntros "HP". iMod "HP". iMod "Hclo" as "_".
  iModIntro. by iApply "HPQ".
Qed.

Lemma step_fupdN_step_fupd2N k P :
  (|={∅}▷=>^k P) -∗ ||▷=>^k P.
Proof.
  induction k => //=.
  iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. by iApply IHk.
Qed.

Lemma step_fupd2N_inner_le k1 k2 E1a E1b E2a E2b P:
  k2 ≤ k1 →
  (||={E1a|E1b,∅|∅}=> ||▷=>^k2 ||={∅|∅,E2a|E2b}=> P) -∗
  ||={E1a|E1b,∅|∅}=> ||▷=>^k1 ||={∅|∅,E2a|E2b}=> P.
Proof.
  iIntros (?) "HP".
  iMod "HP". iModIntro. iApply step_fupd2N_le; try eassumption. auto.
Qed.

Lemma step_fupd2N_add k1 k2 P :
 (||▷=>^k1 ||▷=>^k2 P) ⊣⊢ ||▷=>^(k1 + k2) P.
Proof.
  rewrite Nat.iter_add. done.
Qed.

Lemma step_fupd2N_inner_add E1a E1b E2a E2b k1 k2 P :
 (||={E1a|E1b,∅|∅}=> ||▷=>^k1 ||={∅|∅, E1a|E1b}=> ||={E1a|E1b,∅|∅}=> ||▷=>^k2 ||={∅|∅,E2a|E2b}=> P)
  ⊢||={E1a|E1b,∅|∅}=> ||▷=>^(k1 + k2) ||={∅|∅,E2a|E2b}=> P.
Proof.
  rewrite Nat.iter_add.
  iIntros "H". iMod "H". iModIntro.
  iApply (step_fupd2N_wand with "H"). iIntros "H".
  destruct k2.
  * simpl. do 3 iMod "H". eauto.
  * rewrite Nat.iter_succ. iMod "H". iMod "H". eauto.
Qed.

Lemma step_fupd2N_S_fupd2 n P :
  (||▷=>^(S n) P) ⊣⊢ (||▷=>^(S n) ||={∅|∅,∅|∅}=> P).
Proof.
  apply (anti_symm (⊢)); rewrite !Nat.iter_succ_r.
  - iIntros "H". iApply (step_fupd2N_wand with "H").
    iIntros ">H". iModIntro. iNext. iModIntro. auto.
  - iIntros "H". iApply (step_fupd2N_wand with "H").
    iIntros ">H". iModIntro. iNext. iMod "H". auto.
Qed.

Lemma step_fupd2N_fupd2 n P :
  n > 0 →
  (||▷=>^n ||={∅|∅,∅|∅}=> P) ⊢ (||▷=>^n P).
Proof.
  intros. destruct n; first lia.
  rewrite -step_fupd2N_S_fupd2. done.
Qed.

Lemma step_fupd2_fupd2N n P :
  n > 0 →
  (||={∅|∅,∅|∅}=> ||▷=>^n P) ⊢ (||▷=>^n P).
Proof.
  intros. destruct n; first lia.
  replace (S n) with (1 + n) by lia.
  rewrite Nat.iter_add. iIntros "H". iMod "H". done.
Qed.

Lemma step_fupd2_fupd2 Eo1 Eo2 Ei1 Ei2 P :
  (||={Eo1|Eo2,Ei1|Ei2}=> ▷ ||={Ei1|Ei2,Eo1|Eo2}=> P) ⊣⊢
  (||={Eo1|Eo2, Ei1|Ei2}=> ▷ ||={Ei1|Ei2,Eo1|Eo2}=> ||={Eo1|Eo2, Eo1|Eo2}=> P).
Proof.
  apply (anti_symm (⊢)).
  - by rewrite -fupd2_intro.
  - by rewrite fupd2_trans.
Qed.

End step_fupd2.

Lemma step_fupd2N_soundness `{!invGpreS Σ} n m φ :
  (∀ `{Hinv: !invGS Σ}, £ m ⊢@{iPropI Σ} ||={⊤|⊤,∅|∅}=> ||▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  intros Hiter. eapply (fupd2_soundness (m+n)).
  intros Hinv. iIntros "[Hm Hn]".
  iMod (Hiter with "Hm") as "Hupd". clear Hiter.
  iInduction n as [|n] "IH"; simpl.
  - iModIntro. done. 
  - rewrite lc_succ. iDestruct "Hn" as "[Hone Hn]".
    iMod "Hupd". iMod (lc_fupd_elim_later with "Hone Hupd") as "> Hupd".
    by iApply ("IH" with "Hn Hupd").
Qed.
