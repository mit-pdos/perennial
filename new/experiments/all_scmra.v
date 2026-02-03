From New.proof Require Import proof_prelude.
From iris.algebra.lib Require Import mono_list mono_nat dfrac_agree gmap_view.
From Coq Require Import Logic.ClassicalEpsilon.

Module cmra_expr.
Section defn.
Context (Σ : gFunctors).

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

Fixpoint interpret (x : t) : cmra :=
  match x with
  | prod A B => prodR (interpret A) (interpret B)
  | gmap K V => gmapR K (interpret V)
  | mono_list A => mono_listR (leibnizO A)
  | frac => fracR
  | dfrac => dfracR
  | agree A => agreeR (leibnizO A)
  | excl A => exclR (leibnizO A)
  | gmap_view K V => gmap_viewR K (interpret V)
  | saved_pred A => (dfrac_agreeR (oFunctor_apply (A -d> ▶ ∙) (iPropO Σ)))
  end.
End defn.
End cmra_expr.

Section defn.
Context (Σ : gFunctors).

Definition any_cmra : Type := discrete_funUR (optionUR ∘ cmra_expr.interpret Σ).

Definition cast {A B : cmra} (a : A) (e : A = B) : B :=
  match e in (_ = A) return A with eq_refl => a end.

Definition to_any (A : cmra_expr.t) (a : cmra_expr.interpret Σ A) : any_cmra :=
  λ (B : cmra_expr.t),

    match (excluded_middle_informative
             (cmra_expr.interpret Σ A = cmra_expr.interpret Σ B)) with
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
  (eq_a : M = cmra_expr.interpret Σ A) (eq_b : M = cmra_expr.interpret Σ B) :
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

Definition any_cmraR Σ := discrete_funR (optionUR ∘ cmra_expr.interpret Σ).

End defn.

Section own.
Context `{!inG Σ (any_cmraR Σ)}.

Class SimpleCmra A :=
  {
    Aexp : cmra_expr.t;
    eq_proof : A = cmra_expr.interpret Σ Aexp;
  }.

Definition own_any {A : cmra} γ (a : A) : iProp Σ :=
  ∃ (_ : SimpleCmra A), own γ (to_any Σ Aexp (cast a eq_proof) : any_cmra Σ).

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
  iMod (own_alloc (to_any Σ Aexp (eq_rect A id a _ eq_proof) : any_cmra Σ)) as (γ) "H".
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


Global Instance any_cmra_is_op (x y : any_cmraR Σ) : IsOp (x ⋅ y) x y.
Proof. Admitted.

Lemma interpret_inj a a' :
  cmra_expr.interpret Σ a = cmra_expr.interpret Σ a' →
  a = a'.
Proof.
Admitted.

Section saved_pred.
Context {A : Type}.
Definition saved_pred_own (γ : gname) (dq : dfrac) (Φ : A → iProp Σ) :=
  own_any γ (to_dfrac_agree (DfracOwn 1)
               (Next ∘ Φ : oFunctor_apply (A -d> ▶ ∙) (iPropO Σ))).

Global Instance saved_pred_own_contractive `{!savedPredG Σ A} γ dq :
  Contractive (saved_pred_own γ dq : (A -d> iPropO Σ) → iProp Σ).
Proof.
Abort.

Global Instance saved_pred_discarded_persistent γ Φ :
  Persistent (saved_pred_own γ DfracDiscarded Φ).
Proof.
Abort.

Lemma saved_pred_alloc (Φ : A → iProp Σ) dq :
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
  iCombine "HΦ HΨ" gives "($ & Hag)".
  iApply later_equivI. by iApply (discrete_fun_equivI with "Hag").
Qed.

Lemma saved_pred_agree γ dq1 dq2 Φ Ψ x :
  saved_pred_own γ dq1 Φ -∗ saved_pred_own γ dq2 Ψ -∗ ▷ (Φ x ≡ Ψ x).
Proof.
  iIntros "HΦ HΨ".
  iPoseProof (saved_pred_valid_2 with "HΦ HΨ") as "[_ $]".
Qed.

Lemma own_saved_prop (P : iProp Σ) :
  ⊢ |==> ∃ γ, own_any γ (to_dfrac_agree (DfracOwn 1)
                        (Next ∘ (λ _, P): oFunctor_apply (unit -d> ▶ ∙) (iPropO Σ))).
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
