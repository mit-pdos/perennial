From Perennial.program_proof Require Import grove_prelude.

Set Default Proof Using "Type*".

Section classes.
Context {PROP : bi} {A B : Type}.

Class Func (f : A → B → PROP) : Prop :=
  func x y1 y2 : f x y1 -∗ f x y2 -∗ ⌜ y1 = y2 ⌝.
Class InjRel (f : A → B → PROP) : Prop :=
  inj_rel x1 x2 y : f x1 y -∗ f x2 y -∗ ⌜ x1 = x2 ⌝.
End classes.

Section func_sepL.
Context {PROP : bi} {A : Type} {Φ : nat → A → PROP}.

Lemma big_sepL_func_eq l1 l2 :
  Func Φ →
  length l1 = length l2 →
  ([∗ list] k↦x1 ∈ l1, Φ k x1) -∗
  ([∗ list] k↦x1 ∈ l2, Φ k x1) -∗
  ⌜ l1 = l2 ⌝.
Proof.
  revert Φ l2. induction l1 as [|x1 l1 IH]=> Φ l2 HF Hlen.
  - destruct l2; naive_solver.
  - destruct l2 as [|x2 l2]; [done|].
    rewrite !big_sepL_cons.
    iIntros "[Ha1 H1] [Ha2 H2]".
    ospecialize (IH (λ k, Φ (S k)) l2 _ _).
    { unfold Func in *. naive_solver. }
    { by list_simplifier. }
    iDestruct (IH with "H1 H2") as %->.
    by iDestruct (HF with "Ha1 Ha2") as %->.
Qed.

Local Open Scope nat.

Lemma big_sepL_func_prefix k_ub ψ l1 l2 :
  Func Φ →
  length l1 ≥ k_ub →
  length l2 ≥ k_ub →
  (∀ k, k < k_ub → Φ k = ψ k) →
  ([∗ list] k↦x1 ∈ l1, Φ k x1) -∗
  ([∗ list] k↦x1 ∈ l2, ψ k x1) -∗
  ⌜ take k_ub l1 = take k_ub l2 ⌝.
Proof.
  iIntros (??? Heq) "H1 H2".
  iDestruct (big_sepL_take_drop _ _ k_ub with "H1") as "[H1 _]".
  iDestruct (big_sepL_take_drop _ _ k_ub with "H2") as "[H2 _]".
  iDestruct (big_sepL_impl _ Φ with "H2 []") as "H2".
  { iIntros "!>". iIntros (?? Hlook) "?".
    rewrite Heq; [done|].
    apply lookup_lt_Some in Hlook.
    rewrite take_length_le in Hlook; [done|lia]. }
  iApply (big_sepL_func_eq with "[$H1] [$H2]").
  rewrite !take_length_le; lia.
Qed.
End func_sepL.

Section func_sepL2.
Context {PROP : bi} {A B : Type} {Φ : nat → A → B → PROP}.
Context `{HF : !Func (uncurry Φ)}.

Lemma big_sepL2_func_eq l1 l2 l3 :
  ([∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2) -∗
  ([∗ list] k↦x1;x2 ∈ l1;l3, Φ k x1 x2) -∗
  ⌜ l2 = l3 ⌝.
Proof.
  iIntros "H1 H2".
  iAssert (⌜ length l2 = length l3 ⌝%I) as %Hlen_eq.
  { iDestruct (big_sepL2_length with "H1") as %?.
    iDestruct (big_sepL2_length with "H2") as %?.
    iPureIntro. lia. }
  iDestruct (big_sepL2_to_sepL_2 with "H1") as "H1".
  iDestruct (big_sepL2_to_sepL_2 with "H2") as "H2".
  iDestruct (big_sepL_func_eq with "H1 H2") as %Heq; [|done|].
  { iIntros (k ??) "(%a &%& H1) (% &%& H2)".
    list_simplifier.
    by iApply (HF (k, a) with "[H1] [H2]"). }
  done.
Qed.

Lemma big_sepL2_func_prefix_aux l1 l2 l3 l4 :
  l1 `prefix_of` l3 →
  ([∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2) -∗
  ([∗ list] k↦x1;x2 ∈ l3;l4, Φ k x1 x2) -∗
  ⌜ l2 `prefix_of` l4 ⌝.
Proof.
  iIntros ([? ->]) "H1 H2".
  iDestruct (big_sepL2_app_inv_l with "H2") as (??) "(%Heq & H2 &_)".
  iDestruct (big_sepL2_func_eq with "H1 H2") as %<-.
  list_simplifier.
  eauto using prefix_app_r.
Qed.

Lemma big_sepL2_func_prefix l1 l2 l3 l4 :
  l1 `prefix_of` l3 ∨ l3 `prefix_of` l1 →
  ([∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2) -∗
  ([∗ list] k↦x1;x2 ∈ l3;l4, Φ k x1 x2) -∗
  ⌜ l2 `prefix_of` l4 ∨ l4 `prefix_of` l2 ⌝.
Proof.
  iIntros ([?|?]) "H1 H2".
  - iLeft. by iApply (big_sepL2_func_prefix_aux with "H1 H2").
  - iRight. by iApply (big_sepL2_func_prefix_aux with "H2 H1").
Qed.
End func_sepL2.
