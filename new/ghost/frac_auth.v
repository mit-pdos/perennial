(** Ghost state for a fractional authoritative CMRA, wrapping the [frac_authR]
  RA. Provides an authoritative proposition [frac_auth_auth_own γ dq a] and a
  fragment proposition [frac_auth_frag_own γ q a].

  The auth can be split fractionally: [●F{p⋅q} a ≡ ●F{p} a ⋅ ●F{q} a].
  A full fragment (q=1) agrees exactly with the auth value. A partial fragment
  (q<1) gives an inclusion. *)
From New.ghost Require Export own.
From iris.algebra.lib Require Import frac_auth.
From iris.bi.lib Require Import fractional.

Local Definition frac_auth_auth_own_def `{!allG Σ} {A : cmra} {Ae : syntax.cmra}
    `{!IsCmra (iProp Σ) A Ae}
    (γ : gname) (dq : dfrac) (a : A) : iProp Σ :=
  own γ (●F{dq} a).
Local Definition frac_auth_auth_own_aux : seal (@frac_auth_auth_own_def).
Proof. by eexists. Qed.
Definition frac_auth_auth_own := frac_auth_auth_own_aux.(unseal).
Local Definition frac_auth_auth_own_unseal :
  @frac_auth_auth_own = @frac_auth_auth_own_def := frac_auth_auth_own_aux.(seal_eq).
Global Arguments frac_auth_auth_own {Σ _ A Ae _} γ dq a.

Local Definition frac_auth_frag_own_def `{!allG Σ} {A : cmra} {Ae : syntax.cmra}
    `{!IsCmra (iProp Σ) A Ae}
    (γ : gname) (q : frac) (a : A) : iProp Σ :=
  own γ (◯F{q} a).
Local Definition frac_auth_frag_own_aux : seal (@frac_auth_frag_own_def).
Proof. by eexists. Qed.
Definition frac_auth_frag_own := frac_auth_frag_own_aux.(unseal).
Local Definition frac_auth_frag_own_unseal :
  @frac_auth_frag_own = @frac_auth_frag_own_def := frac_auth_frag_own_aux.(seal_eq).
Global Arguments frac_auth_frag_own {Σ _ A Ae _} γ q a.

Local Ltac unseal := rewrite
  ?frac_auth_auth_own_unseal /frac_auth_auth_own_def
  ?frac_auth_frag_own_unseal /frac_auth_frag_own_def.

Section frac_auth_own.
  Context `{!allG Σ} {A : cmra} {Ae : syntax.cmra} `{!IsCmra (iProp Σ) A Ae}.
  Implicit Types (a b : A) (dq : dfrac) (q : frac).

  Global Instance frac_auth_auth_own_timeless γ dq a :
    Discrete a → Timeless (frac_auth_auth_own γ dq a).
  Proof. unseal. apply _. Qed.
  Global Instance frac_auth_frag_own_timeless γ q a :
    Discrete a → Timeless (frac_auth_frag_own γ q a).
  Proof. unseal. apply _. Qed.

  Global Instance frac_auth_auth_own_fractional γ a :
    Fractional (λ q, frac_auth_auth_own γ (DfracOwn q) a).
  Proof.
    unseal. intros p q. rewrite -own_op -frac_auth_auth_dfrac_op //.
  Qed.
  Global Instance frac_auth_auth_own_as_fractional γ q a :
    AsFractional (frac_auth_auth_own γ (DfracOwn q) a)
      (λ q, frac_auth_auth_own γ (DfracOwn q) a) q.
  Proof. split; [auto|apply _]. Qed.

  Lemma frac_auth_auth_own_agree `{!CmraDiscrete A} γ dq1 dq2 a1 a2 :
    frac_auth_auth_own γ dq1 a1 -∗
    frac_auth_auth_own γ dq2 a2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ a1 ≡ a2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iCombine "H1 H2" gives %[? ?]%frac_auth_auth_dfrac_op_valid.
    auto.
  Qed.

  Lemma frac_auth_auth_own_agree_L `{!CmraDiscrete A, !LeibnizEquiv A} γ dq1 dq2 a1 a2 :
    frac_auth_auth_own γ dq1 a1 -∗
    frac_auth_auth_own γ dq2 a2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ a1 = a2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (frac_auth_auth_own_agree with "H1 H2") as %[Hdq Heq].
    iPureIntro. split; [done|by apply leibniz_equiv].
  Qed.

  Lemma frac_auth_auth_frag_own_agree `{!CmraDiscrete A} γ dq a b :
    frac_auth_auth_own γ dq a -∗
    frac_auth_frag_own γ 1 b -∗
    ⌜a ≡ b⌝.
  Proof.
    unseal. iIntros "Hauth Hfrag".
    iCombine "Hauth Hfrag" gives %?%frac_auth_agree.
    auto.
  Qed.

  Lemma frac_auth_auth_frag_own_agree_L `{!CmraDiscrete A, !LeibnizEquiv A} γ dq a b :
    frac_auth_auth_own γ dq a -∗
    frac_auth_frag_own γ 1 b -∗
    ⌜a = b⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (frac_auth_auth_frag_own_agree with "Hauth Hfrag") as %Heq.
    iPureIntro. by apply leibniz_equiv.
  Qed.

  Lemma frac_auth_own_alloc a :
    ✓ a →
    ⊢ |==> ∃ γ, frac_auth_auth_own γ (DfracOwn 1) a ∗ frac_auth_frag_own γ 1 a.
  Proof.
    intros Hv. unseal. setoid_rewrite <-own_op.
    apply own_alloc. by apply frac_auth_valid.
  Qed.

  Lemma frac_auth_update γ q a b a' b' :
    (a, b) ~l~> (a', b') →
    frac_auth_auth_own γ (DfracOwn 1) a -∗
    frac_auth_frag_own γ q b ==∗
    frac_auth_auth_own γ (DfracOwn 1) a' ∗ frac_auth_frag_own γ q b'.
  Proof.
    intros Hupd. unseal. rewrite -own_op.
    iApply own_update_2.
    by apply frac_auth_update.
  Qed.

  Lemma frac_auth_update_1 γ a b a' :
    ✓ a' →
    frac_auth_auth_own γ (DfracOwn 1) a -∗
    frac_auth_frag_own γ 1 b ==∗
    frac_auth_auth_own γ (DfracOwn 1) a' ∗ frac_auth_frag_own γ 1 a'.
  Proof.
    intros Hv. unseal. rewrite -own_op.
    iApply own_update_2.
    by apply frac_auth_update_1.
  Qed.
End frac_auth_own.
