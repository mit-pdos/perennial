From iris.algebra Require Import auth gset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Class auth_setG Σ (A: Type) `{Countable A} := AuthSetG {
    auth_set_inG :: inG Σ (authUR (gset_disjUR A));
}.
Global Hint Mode auth_setG - ! - - : typeclass_instances.

Definition auth_setΣ A `{Countable A} : gFunctors :=
  #[ GFunctor (authRF (gset_disjUR A)) ].

#[global] Instance subG_auth_setG Σ A `{Countable A} :
  subG (auth_setΣ A) Σ → auth_setG Σ A.
Proof. solve_inG. Qed.

(*| auth_set is a thin wrapper around the resource algebra `authUR (gset_disjUR A)`. |*)
Local Definition auth_set_auth_def `{auth_setG Σ A}
    (γ : gname) (s: gset A) : iProp Σ :=
  own γ (● GSet s).
Local Definition auth_set_auth_aux : seal ( @auth_set_auth_def).
Proof. by eexists. Qed.
Definition auth_set_auth := auth_set_auth_aux.(unseal).
Local Definition auth_set_auth_unseal :
  @auth_set_auth = @auth_set_auth_def := auth_set_auth_aux.(seal_eq).
Global Arguments auth_set_auth {Σ A _ _ _} γ s.

#[local] Notation "○ a" := (auth_frag a) (at level 20).

Local Definition auth_set_frag_def `{auth_setG Σ A}
    (γ : gname) (a: A) : iProp Σ :=
  own γ (○ GSet {[a]}).
Local Definition auth_set_frag_aux : seal (@auth_set_frag_def). Proof. by eexists. Qed.
Definition auth_set_frag := auth_set_frag_aux.(unseal).
Local Definition auth_set_frag_unseal :
  @auth_set_frag = @auth_set_frag_def := auth_set_frag_aux.(seal_eq).
Global Arguments auth_set_frag {Σ A _ _ _} γ a.

Local Ltac unseal := rewrite ?auth_set_auth_unseal ?auth_set_frag_unseal /auth_set_auth_def /auth_set_frag_def.

Section lemmas.
  Context `{auth_setG Σ A}.

  Implicit Types (s: gset A) (a: A).

  #[global] Instance auth_set_auth_timeless γ s :
    Timeless (auth_set_auth γ s).
  Proof. unseal. apply _. Qed.
  #[global] Instance auth_set_frag_timeless γ a :
    Timeless (auth_set_frag γ a).
  Proof. unseal. apply _. Qed.

(*| The definition of auth_set is designed to make these ghost updates true. This as the API for this construction, in that the user of the library will not use the definitions above, only these lemmas. However, we have to carefully choose the definitions to make all of these rules true. |*)

(*| We create an auth_set variable with an empty set and thus no fragments. |*)
  Lemma auth_set_init :
    ⊢ |==> ∃ γ, auth_set_auth γ (∅: gset A).
  Proof.
    unseal.
    iApply (own_alloc (● GSet (∅: gset A))).
    apply auth_auth_valid. done.
  Qed.

(*| We can add to the set and produce a new fragment that controls the new element. `a ∉ s` is required since there can only be one `auth_set_frag γ a` for a given value of `a`. |*)
  Lemma auth_set_alloc a γ s :
    a ∉ s →
    auth_set_auth γ s ==∗
    auth_set_auth γ ({[a]} ∪ s) ∗ auth_set_frag γ a.
  Proof.
    unseal.
    iIntros (Hnotin) "Hauth".
    rewrite -own_op.
    iApply (own_update with "Hauth").
    apply auth_update_alloc.
    apply gset_disj_alloc_empty_local_update.
    set_solver.
  Qed.

(*| Because a fragment expresses ownership of a part of the authoritative set, we have this rule which says that fragments agree with the authoritative predicate: |*)
  Lemma auth_set_elem γ s a :
    auth_set_auth γ s -∗ auth_set_frag γ a -∗ ⌜a ∈ s⌝.
  Proof.
    unseal. iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hin.
    iPureIntro.
    apply auth_both_valid_discrete in Hin as [Hin _].
    apply gset_disj_included in Hin.
    apply singleton_subseteq_l in Hin.
    auto.
  Qed.

(*| If we control an element via `auth_set_frag γ a`, it's also possible to delete that element from the authoritative set (as long as we also give up ownership of the fragment). |*)
  Lemma auth_set_dealloc γ s a :
    auth_set_auth γ s ∗ auth_set_frag γ a ==∗
    auth_set_auth γ (s ∖ {[a]}).
  Proof.
    unseal. iIntros "[Hauth Hfrag]".
    iApply (own_update_2 with "Hauth Hfrag").
    apply auth_update_dealloc.
    apply gset_disj_dealloc_local_update.
  Qed.

End lemmas.

