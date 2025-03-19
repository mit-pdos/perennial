From iris.algebra Require Import numbers auth.
From iris.base_logic.lib Require Export own.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From Perennial Require Import base.

Class tok_setG Σ := {
    tok_set_inG :: inG Σ (authUR natR)
  }.

Definition tok_setΣ : gFunctors := #[GFunctor $ authUR natR].

Global Instance subG_tok_setΣ{Σ} : subG (tok_setΣ) Σ → (tok_setG Σ).
Proof. solve_inG. Qed.

Section proof.

Context `{!tok_setG Σ}.
Definition own_tok_auth_dfrac_def γ dq (num_toks : nat) : iProp Σ :=
  own γ (●{dq} num_toks).
Program Definition own_tok_auth_dfrac := sealed @own_tok_auth_dfrac_def.
Definition own_tok_auth_dfrac_unseal : own_tok_auth_dfrac = _ := seal_eq _.
Notation own_tok_auth γ n := (own_tok_auth_dfrac γ (DfracOwn 1) n).

Definition own_toks_def γ (n : nat) : iProp Σ :=
  own γ (◯ n).
Program Definition own_toks := sealed @own_toks_def.
Definition own_toks_unseal : own_toks = _ := seal_eq _.

Local Ltac unseal := rewrite ?own_tok_auth_dfrac_unseal /own_tok_auth_dfrac_def ?own_toks_unseal /own_toks_def.

Lemma own_tok_auth_alloc :
  ⊢ |==> ∃ γ, own_tok_auth γ O.
Proof. unseal. iApply own_alloc. rewrite auth_auth_valid //. Qed.

Lemma own_tok_auth_plus m γ n :
  own_tok_auth γ n ==∗ own_tok_auth γ (n + m) ∗ own_toks γ m.
Proof. unseal. rewrite -own_op. iApply own_update. by apply auth_update_alloc, nat_local_update.
Qed.

Lemma own_tok_auth_delete m γ n :
  own_tok_auth γ (n + m) -∗ own_toks γ m ==∗ own_tok_auth γ n.
Proof. unseal. iApply own_update_2. by apply auth_update_dealloc, nat_local_update. Qed.

Lemma own_tok_auth_S γ n :
  own_tok_auth γ n ==∗ own_tok_auth γ (S n) ∗ own_toks γ 1.
Proof. replace (S n) with (n + 1)%nat by lia. iApply (own_tok_auth_plus 1). Qed.

Lemma own_tok_auth_delete_S γ n :
  own_tok_auth γ (S n) -∗ own_toks γ 1 ==∗ own_tok_auth γ n.
Proof. replace (S n) with (n + 1)%nat by lia. iApply (own_tok_auth_delete 1). Qed.

Lemma own_toks_0 γ :
  ⊢ |==> own_toks γ 0.
Proof. unseal. iApply own_unit. Qed.

Lemma own_toks_plus m γ n :
  own_toks γ (n + m) ⊣⊢ own_toks γ n ∗ own_toks γ m.
Proof. unseal. rewrite -own_op //. Qed.

Global Instance own_toks_combine_as γ n m :
  CombineSepAs (own_toks γ n) (own_toks γ m) (own_toks γ (n + m)).
Proof. rewrite /CombineSepAs. unseal. rewrite -own_op auth_frag_op //. Qed.

Global Instance own_tok_auth_toks_combine_gives_as γ dq n m :
  CombineSepGives (own_tok_auth_dfrac γ dq n) (own_toks γ m) (⌜ (m <= n)%nat ⌝).
Proof.
  rewrite /CombineSepGives. unseal.
  rewrite -own_op. iIntros "H".
  iDestruct (own_valid with "H") as %?.
  iModIntro. iPureIntro.
  rewrite auth_both_dfrac_valid_discrete in H.
  intuition. rewrite -nat_included. done.
Qed.

Global Instance own_tok_auth_combine_as γ dq dq' n :
  CombineSepAs (own_tok_auth_dfrac γ dq n) (own_tok_auth_dfrac γ dq' n)
    (own_tok_auth_dfrac γ (dq ⋅ dq') n).
Proof. rewrite /CombineSepAs. unseal. rewrite -own_op auth_auth_dfrac_op //. Qed.

Global Instance own_tok_auth_combine_gives_as γ dq dq' n n' :
  CombineSepGives (own_tok_auth_dfrac γ dq n) (own_tok_auth_dfrac γ dq' n')
                  (⌜ ✓ (dq ⋅ dq') ∧ n = n' ⌝).
Proof.
  rewrite /CombineSepGives. unseal.
  rewrite -own_op. iIntros "H".
  iDestruct (own_valid with "H") as %?.
  iModIntro. iPureIntro.
  rewrite auth_auth_dfrac_op_valid in H.
  intuition.
Qed.

Global Instance own_toks_Timeless γ n : Timeless (own_toks γ n).
Proof. unseal. apply _. Qed.

Global Instance own_tok_auth_dfrac_Timeless γ dq n : Timeless (own_tok_auth_dfrac γ dq n).
Proof. unseal. apply _. Qed.

Global Instance typed_pointsto_fractional γ n : Fractional (λ q, own_tok_auth_dfrac γ (DfracOwn q) n)%I.
Proof.
  unseal. unfold Fractional.
  intros ??. rewrite -own_op -auth_auth_dfrac_op dfrac_op_own //.
Qed.

Global Instance typed_pointsto_as_fractional γ q n :
  AsFractional (own_tok_auth_dfrac γ (DfracOwn q) n) (λ q, own_tok_auth_dfrac γ (DfracOwn q) n)%I q.
Proof. constructor; [done | apply _]. Qed.
End proof.

Global Notation own_tok_auth γ n := (own_tok_auth_dfrac γ (DfracOwn 1) n).
