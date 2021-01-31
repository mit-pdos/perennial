From iris.proofmode Require Import base tactics.
From iris.base_logic Require Import upred bi.
Import interface.bi.
Import derived_laws.bi.
Import derived_laws_later.bi.
Import base_logic.bi.uPred.

Section uPred_laws.
Context {M: ucmra}.
Implicit Types φ : Prop.
Implicit Types P Q R : (uPred M).
Implicit Types Ps : list (uPred M).
Implicit Types A : Type.

Notation "P ⊢ Q" := (P ⊢@{uPredI M} Q).
Notation "P ⊣⊢ Q" := (P ⊣⊢@{uPredI M} Q).

Lemma laterN_hold_minus n a x (P: uPred M) :
  ✓{n} x →
  a ≤ n →
  uPred_holds (▷^a P) n x →
  uPred_holds P (n - a) x.
Proof.
  revert x n.
  induction a.
  - repeat (rewrite //= || uPred.unseal).
    intros. replace (n - 0) with n by lia. auto.
  - intros x n Hval Hle. destruct n; first by lia.
    replace (S n - S a) with (n - a) by lia.
    intros. eapply IHa; eauto using cmra_validN_S.
    { lia. }
    move: H. uPred.unseal => //=.
Qed.

Lemma laterN_soundness P k: (⊢ ▷^k P) → ⊢ P.
Proof.
  intros HP. split => n x Hx _.
  apply uPred_mono with n ε; eauto using ucmra_unit_leastN.
  replace n with ((n + k) - k) by lia.
  apply laterN_hold_minus; eauto using ucmra_unit_validN.
  - lia.
  - apply HP; eauto using ucmra_unit_validN.
    uPred.unseal => //=.
Qed.

Lemma laterN_big n a x φ: ✓{n} x →  a ≤ n → uPred_holds (▷^a ⌜φ⌝ : uPred M)%I n x → φ.
Proof.
  induction 2 as [| ?? IHle].
  - induction a; repeat (rewrite //= || uPred.unseal).
    intros Hlater. apply IHa; auto using cmra_validN_S.
    move:Hlater; repeat (rewrite //= || uPred.unseal).
  - intros. apply IHle; auto using cmra_validN_S.
    eapply uPred_mono; eauto using cmra_validN_S.
Qed.

Lemma laterN_small n a x P: ✓{n} x →  n < a → uPred_holds (▷^a P) n x.
Proof.
  induction 2.
  - induction n as [| n IHn]; [| move: IHn];
      repeat (rewrite //= || uPred.unseal).
    naive_solver eauto using cmra_validN_S.
  - induction n as [| n IHn]; [| move: IHle];
      repeat (rewrite //= || uPred.unseal).
    red; rewrite //=. intros.
    eapply (uPred_mono _ _ (S n)); eauto using cmra_validN_S.
Qed.

Lemma laterN_exist_big_inhabited A (Φ: A → uPred M) k n x:
  ✓{n} x →  k ≤ n → uPred_holds (▷^k uPred_exist_def (λ a : A, Φ a)) n x →
  ∃ a : A, True.
Proof.
  induction 2 as [| ?? IHle].
  - induction k; repeat (rewrite //= || uPred.unseal).
    { destruct 1; eauto. }
    intros Hlater. apply IHk; auto using cmra_validN_S.
  - intros. apply IHle; auto using cmra_validN_S.
    eapply uPred_mono; eauto using cmra_validN_S.
Qed.

Local Hint Resolve or_elim or_intro_l' or_intro_r' True_intro False_elim : core.
Local Hint Resolve and_elim_l' and_elim_r' and_intro forall_intro : core.


Lemma laterN_exist_false A (Φ : A → uPred M) k:
  ▷^k (∃ a : A, Φ a) -∗ ▷^k False ∨ (∃ a : A, ▷^k Φ a).
Proof.
  split => n x Hval Hall.
  destruct (decide (n < k)).
  - uPred.unseal. left. apply laterN_small; eauto.
  - move: Hall. uPred.unseal. right.
    edestruct (laterN_exist_big_inhabited A Φ k) as (a&_); eauto.
    { lia. }
    assert (Inhabited A).
    { by econstructor. }
    specialize (laterN_exist k Φ).
    uPred.unseal. intros Hequiv. eapply Hequiv; eauto.
Qed.


Lemma laterN_ownM (a: M) k: ▷^k uPred_ownM a -∗ ∃ b, uPred_ownM b ∧ ▷^k (a ≡ b).
Proof.
  revert a. induction k as [| k IH] => a; iIntros "H".
  - eauto.
  - iAssert (▷^k ∃ b, uPred_ownM b ∧ ▷ (a ≡ b))%I with "[H]" as "H".
    { iNext. by iApply later_ownM. }
    assert (Inhabited M) by (eexists; eauto).
    iDestruct "H" as (b) "(Hown&#Hequiv)".
    iPoseProof (IH with "Hown") as (b') "(Hown&#Hequiv')".
    iExists b'. iFrame. rewrite -later_laterN laterN_later. iNext.
    iNext. iRewrite "Hequiv". eauto.
Qed.
End uPred_laws.
