From New.proof Require Import proof_prelude.
From iris.algebra.lib Require Import mono_list mono_nat dfrac_agree gmap_view.
From Coq Require Import Logic.ClassicalEpsilon.

Module cmra_expr.
Section defn.

Inductive t :=
| prod (A B : t)
| gmap (K : Type) `{Countable K} (V : t)
| mono_list (E : Type)
| frac
| dfrac
| agree (A : Type)
| excl (A : Type)
| gmap_view (K : Type) `{Countable K} (V : t)
| saved_pred (A : Type)
.

Fixpoint interpret (PROP : ofe) `{!Cofe PROP} (x : t) : cmra :=
  match x with
  | prod A B => prodR (interpret PROP A) (interpret PROP B)
  | gmap K V => gmapR K (interpret PROP V)
  | mono_list A => mono_listR (leibnizO A)
  | frac => fracR
  | dfrac => dfracR
  | agree A => agreeR (leibnizO A)
  | excl A => exclR (leibnizO A)
  | gmap_view K V => gmap_viewR K (interpret PROP V)
  | saved_pred A => (dfrac_agreeR (A -d> laterO ( PROP)))
  end.

Fixpoint interpretF (x : t) : rFunctor :=
  match x with
  | prod A B => prodRF (interpretF A) (interpretF B)
  | gmap K V => gmapRF K (interpretF V)
  | mono_list A => mono_listRF (leibnizO A)
  | frac => fracR
  | dfrac => dfracR
  | agree A => agreeRF (leibnizO A)
  | excl A => exclRF (leibnizO A)
  | gmap_view K V => gmap_viewRF K (interpretF V)
  | saved_pred A => (dfrac_agreeRF (A -d> ▶ ∙))
  end.
End defn.
End cmra_expr.

Section defn.
Context (PROP : ofe) `{!Cofe PROP}.

Definition any_cmra : Type := discrete_funUR (optionUR ∘ cmra_expr.interpret PROP).

Definition cast {A B : cmra} (a : A) (e : A = B) : B :=
  match e in (_ = A) return A with eq_refl => a end.

Definition to_any (A : cmra_expr.t) (a : cmra_expr.interpret PROP A) : any_cmra :=
  λ (B : cmra_expr.t),

    match (excluded_middle_informative
             (cmra_expr.interpret PROP A = cmra_expr.interpret PROP B)) with
    | right _ => None
    | left eq_proof =>
        Some (cast a eq_proof)
    end.

Lemma any_cmra_update {A : cmra_expr.t} a b :
  a ~~> b →
  to_any A a ~~> to_any A b.
Proof.
  intros H. apply functions.discrete_fun_update. intros B. unfold to_any.
  destruct excluded_middle_informative; last done.
  simpl in *. destruct e. simpl in *. by apply option_update.
Qed.

Lemma any_cmra_op {M : cmra} {A B : cmra_expr.t} (a b : M)
  (eq_a : M = cmra_expr.interpret PROP A) (eq_b : M = cmra_expr.interpret PROP B) :
  to_any A (cast a eq_a) ⋅ to_any B (cast b eq_b) = to_any A (cast (a ⋅ b) eq_a).
Proof.
  rewrite /to_any. simpl.
  apply FunctionalExtensionality.functional_extensionality_dep_good.
  intros C. rewrite discrete_fun_lookup_op.
  subst.
  destruct excluded_middle_informative as [Heq|Hbad];
    destruct excluded_middle_informative as [Heq'|Hbad'].
  2:{ exfalso. apply Hbad'. rewrite -Heq. naive_solver. }
  2:{ exfalso. apply Hbad. rewrite -Heq'. naive_solver. }
  2:{ done. }
  simpl in *. destruct Heq, Heq'.
  progress simpl in *.
  pose proof (UIP_refl _ _ eq_b). subst.
  simpl. done.
Qed.

Definition any_cmraUR := discrete_funUR (optionUR ∘ (cmra_expr.interpret PROP)).

Definition any_cmraURF := discrete_funURF (λ A, optionURF (cmra_expr.interpretF A)).

Global Instance contr :
  urFunctorContractive any_cmraURF.
Proof.
  apply discrete_funURF_contractive.
  intro A. apply optionURF_contractive.
  induction A; simpl in *; tc_solve.
Qed.
End defn.

Definition anyΣ : gFunctors :=
  #[ GFunctor (urFunctor_to_rFunctor any_cmraURF) ].

Class anyG Σ :=
  {
    any_inG :: inG Σ (any_cmraUR (iPropO Σ));
  }.


Lemma x A Σ :
  (rFunctor_apply (cmra_expr.interpretF A) (iPropO Σ)) =
  (cmra_expr.interpret (iPropO Σ) A).
Proof.
  induction A; simpl in *; try done.
  - unfold rFunctor_apply in *. simpl in *.
    rewrite IHA1 IHA2 //.
  - unfold rFunctor_apply in *. simpl in *.
    rewrite IHA //.
  - unfold rFunctor_apply in *. simpl in *.
    rewrite IHA. done.
Qed.

Global Instance subG_anyΣ Σ :
  subG (anyΣ) Σ → anyG Σ.
Proof.
  intros. constructor.
  apply subG_inv in H. destruct H.
  apply subG_inG in s. simpl in *.
  exact_eq s.
  unfold any_cmraUR.
  simpl.
  assert (
      (λ c : cmra_expr.t, optionUR ((cmra_expr.interpretF c).(rFunctor_car) (iPropO Σ) (iPropO Σ)))
        = (optionUR ∘ cmra_expr.interpret (iPropO Σ))).
  2:{ rewrite H //. }
  apply FunctionalExtensionality.functional_extensionality_dep_good.
  intros A. simpl.
  rewrite -x. done.
Qed.

Section own.
Context `{!anyG Σ}.

Class SimpleCmra A :=
  {
    Aexp : cmra_expr.t;
    eq_proof : A = cmra_expr.interpret (iProp Σ) Aexp;
  }.

Definition own_any {A : cmra} γ (a : A) : iProp Σ :=
  ∃ (_ : SimpleCmra A), own γ (to_any (iProp Σ) Aexp (cast a eq_proof) : any_cmra (iProp Σ)).

Lemma own_any_update γ {A : cmra} (a a' : A) :
  a ~~> a' →
  own_any γ a ==∗ own_any γ a'.
Proof.
  intros Hupd. iIntros "[% Hown]".
  iExists _. iApply (own_update with "Hown").
  apply any_cmra_update. simpl. destruct H.
  simpl in *. destruct eq_proof0. simpl.
  apply Hupd.
Qed.

Global Instance own_any_combine {A : cmra} γ (a b : A) :
  CombineSepAs (own_any γ a) (own_any γ b) (own_any γ (a ⋅ b)).
Proof.
  rewrite /CombineSepAs. iIntros "[H1 H2]".
  rewrite /own_any. iDestruct "H1" as "[% H1]".
  iDestruct "H2" as "[% H2]". iExists _.
  iCombine "H1 H2" as "H".
  iExactEq "H". f_equal.
  destruct H, H0. simpl in *.
  unfold to_any.
  apply FunctionalExtensionality.functional_extensionality_dep_good.
  intros C. rewrite discrete_fun_lookup_op.
  destruct excluded_middle_informative as [Heq|Hbad];
    destruct excluded_middle_informative as [Heq'|Hbad'].
  2:{ exfalso. apply Hbad'. rewrite -Heq. naive_solver. }
  2:{ exfalso. apply Hbad. rewrite -Heq'. naive_solver. }
  2:{ done. }
  subst. simpl in *.
  destruct Heq, Heq'. simpl in *.
  pose proof (UIP_refl _ _ eq_proof1). subst. done.
  (* FIXME: use [any_cmra_op] instead of manually proving? *)
Qed.

Lemma own_any_alloc `{!SimpleCmra A} (a : A) :
  ✓ a →
  ⊢ |==> ∃ γ, own_any γ a.
Proof.
  intros Hvalid.
  iMod (own_alloc (to_any PROP Aexp (eq_rect A id a _ eq_proof) : any_cmra PROP)) as (γ) "H".
  { intros ?. rewrite /= /to_any.
    destruct excluded_middle_informative as [Heq|Hbad]; last done.
    destruct Heq. simpl in *. destruct SimpleCmra0.
    subst. done. }
  by iFrame.
Qed.

Instance mlist_simple_cmra (A : Type) : SimpleCmra (mono_listR (leibnizO A)).
Proof. by eexists (cmra_expr.mono_list A). Qed.

Lemma own_any_mono_list (l : list nat) :
  ⊢ |==> ∃ γ, own_any γ (●ML l).
Proof.
  iApply own_any_alloc. apply mono_list_auth_valid.
Qed.

Global Instance own_ne A γ : NonExpansive (@own_any A γ).
Proof.
  intros ???. intros.
  unfold own_any.
  apply bi.exist_ne.
  intros ?.
  rewrite !own.own_eq. simpl.
  rewrite /own.own_def.
Admitted.

Instance own_proper :
  ∀ {A : cmra} (γ : gname), Proper (equiv ==> equiv) (@own_any A γ).
Proof. intros. apply (ne_proper _). Qed.


Global Instance any_cmra_is_op (x y : any_cmraR PROP) : IsOp (x ⋅ y) x y.
Proof. Admitted.

Lemma interpret_inj a a' :
  cmra_expr.interpret PROP a = cmra_expr.interpret PROP a' →
  a = a'.
Proof.
Admitted.

Section saved_pred.
Context {A : Type}.
Definition saved_pred_own (γ : gname) (dq : dfrac) (Φ : A → iProp PROP) :=
  own_any γ (to_dfrac_agree dq (Next ∘ Φ : oFunctor_apply (A -d> ▶ ∙) (iPropO PROP))).

Global Instance saved_pred_own_contractive `{!savedPredG PROP A} γ dq :
  Contractive (saved_pred_own γ dq : (A -d> iPropO PROP) → iProp PROP).
Proof.
Abort.

Global Instance saved_pred_discarded_persistent γ Φ :
  Persistent (saved_pred_own γ DfracDiscarded Φ).
Proof.
Abort.

Lemma saved_pred_alloc (Φ : A → iProp PROP) dq :
  ✓ dq →
  ⊢ |==> ∃ γ, saved_pred_own γ dq Φ.
Proof.
  intros.
  iApply @own_any_alloc.
  { by eexists (cmra_expr.saved_pred _). }
  { done. }
Qed.


Lemma saved_pred_valid_2 γ dq1 dq2 Φ Ψ x :
  saved_pred_own γ dq1 Φ -∗ saved_pred_own γ dq2 Ψ -∗ ⌜✓ (dq1 ⋅ dq2)⌝ ∗ ▷ (Φ x ≡ Ψ x).
Proof.
  iIntros "HΦ HΨ".
  iCombine "HΦ HΨ" as "HP".
Qed.

Lemma saved_pred_agree γ dq1 dq2 Φ Ψ x :
  saved_pred_own γ dq1 Φ -∗ saved_pred_own γ dq2 Ψ -∗ ▷ (Φ x ≡ Ψ x).
Proof.
  iIntros "HΦ HΨ".
  iPoseProof (saved_pred_valid_2 with "HΦ HΨ") as "[_ $]".
Qed.

Lemma own_saved_prop (P : iProp PROP) :
  ⊢ |==> ∃ γ, own_any γ (to_dfrac_agree (DfracOwn 1)
                        (Next ∘ (λ _, P): oFunctor_apply (unit -d> ▶ ∙) (iPropO PROP))).
Proof.
  iApply @own_any_alloc.
  { by eexists (cmra_expr.saved_pred unit). }
  { done. }
Qed.

End own.


(* Print Assumptions own_any_mono_list.
  constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
  classic : ∀ P : Prop, P ∨ ¬ P
*)
