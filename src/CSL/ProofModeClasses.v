From Perennial Require Export CSL.Refinement CSL.WeakestPre.
From iris.algebra Require Import auth gmap frac agree.
From Perennial Require Export CSL.WeakestPre CSL.Lifting CSL.Counting CSL.ThreadReg.
From iris.algebra Require Export functions csum.
From iris.base_logic.lib Require Export invariants gen_heap.
From iris.proofmode Require Export tactics.

(* Extends the iExist tactic to make it easier to re-prove invariants after steps *)
Global Instance from_exist_left_sep {Σ} {A} (Φ : A → iProp Σ) Q :
  FromExist (▷ (∃ a, Φ a) ∗ Q) (λ a, ▷ Φ a ∗ Q)%I .
Proof. rewrite /FromExist. iIntros "H". iDestruct "H" as (?) "(?&$)". iExists _; eauto. Qed.

Ltac iCancelPureRec P :=
  match P with
  | (⌜ ?P' ⌝)%I =>
    let H := iFresh in
    iAssert (⌜ P' ⌝)%I as H; [ iPureIntro | (iFrame H) ]
  | (?P1 ∗ ?P2)%I => first [ iCancelPureRec P1 | iCancelPureRec P2 ]
  end.

Ltac iCancelPure :=
  match goal with
  | [ |- environments.envs_entails _ ?P] => iCancelPureRec P
  end.

Ltac iDestructPure :=
  repeat match goal with
  | [ |- context[ environments.Esnoc _ ?H (⌜ _ ⌝)%I ]] =>
    iDestruct H as "%"
  end.

Section test.
Context {PROP: bi}.
Context {Hpos: BiPositive PROP}.
Context {Haffine: BiAffine PROP}.

Lemma cancel_pure1 (P: PROP) : P ⊢ ⌜(2 + 2 = 4)%nat⌝ ∗ P.
Proof.
  iIntros "HP". iCancelPure; first by lia. auto.
Qed.

Lemma cancel_pure2 (P: PROP) : P ⊢ P ∗ ⌜(2 + 2 = 4)%nat⌝.
Proof.
  iIntros "HP". iCancelPure; first by lia. auto.
Qed.

Lemma cancel_pure3 (P: PROP) : P ⊢ ⌜ 5 = 5 ⌝%nat ∗ ⌜(2 + 2 = 4)%nat⌝.
Proof.
  iIntros "HP". iCancelPure; first by lia. auto.
Qed.

Lemma destruct_pure1 (P: PROP) n : P ∗ ⌜ n > 100 ⌝ ⊢ P ∗ ⌜ n > 99 ⌝.
Proof.
  iIntros "(?&?)". iDestructPure. iCancelPure; first lia.
  auto.
Qed.

End test.
