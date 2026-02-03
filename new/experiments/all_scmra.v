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
| saved_pred (A : Type).

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

Definition allUR (PROP : ofe) `{!Cofe PROP}
  : Type := discrete_funUR (optionUR ∘ cmra_expr.interpret PROP).

Definition allURF := discrete_funURF (λ A, optionURF (cmra_expr.interpretF A)).

Global Instance all_contractive : urFunctorContractive allURF.
Proof.
  apply discrete_funURF_contractive.
  intro A. apply optionURF_contractive.
  induction A; simpl in *; tc_solve.
Qed.

Definition allΣ : gFunctors :=
  #[ GFunctor (urFunctor_to_rFunctor allURF) ].

Class allG Σ :=
  { #[local] any_inG :: inG Σ (allUR (iPropO Σ)); }.

Local Lemma interpret_eq_interpretF A Σ :
  (cmra_expr.interpretF A).(rFunctor_car) (iPropO Σ) (iPropO Σ) =
  (cmra_expr.interpret (iPropO Σ) A).
Proof.
  induction A; simpl in *; try done.
  - unfold rFunctor_apply in *. rewrite IHA1 IHA2 //.
  - unfold rFunctor_apply in *. rewrite IHA //.
  - unfold rFunctor_apply in *. rewrite IHA //.
Qed.

Global Instance subG_allΣ Σ :
  subG (allΣ) Σ → allG Σ.
Proof.
  intros. constructor.
  apply subG_inv in H. destruct H.
  apply subG_inG in s. simpl in *.
  exact_eq s. rewrite /allUR.
  apply (f_equal ucmra_cmraR).
  apply (f_equal discrete_funUR).
  apply FunctionalExtensionality.functional_extensionality_dep_good.
  intros. rewrite interpret_eq_interpretF //.
Qed.

Definition cast {A B : cmra} (a : A) (e : A = B) : B :=
  match e in (_ = A) return A with eq_refl => a end.

Definition to_all (PROP : ofe) `{!Cofe PROP}
  (A : cmra_expr.t) (a : cmra_expr.interpret PROP A) : allUR PROP :=
  λ (B : cmra_expr.t),
    match (excluded_middle_informative (cmra_expr.interpret PROP A = cmra_expr.interpret PROP B)) with
    | right _ => None
    | left eq_proof =>
        Some (cast a eq_proof)
    end.

Local Lemma to_all_update
  {PROP : ofe} `{!Cofe PROP}
  {A : cmra_expr.t} a b :
  a ~~> b →
  to_all PROP A a ~~> to_all PROP A b.
Proof.
  intros H. apply functions.discrete_fun_update. intros B. rewrite /to_all.
  destruct excluded_middle_informative; last done.
  simpl in *. destruct e. simpl in *. by apply option_update.
Qed.

Lemma cast_self {A : cmra} (a : A) (eq_A : A = A) :
  (cast a eq_A) = a.
Proof.
  pose proof (UIP_refl _ _ eq_A). subst. done.
Qed.

Lemma to_all_op {PROP : ofe} `{!Cofe PROP} {A B : cmra_expr.t}
  (a b : cmra_expr.interpret PROP A)
  (eq_pf : cmra_expr.interpret PROP A = cmra_expr.interpret PROP B) :
  to_all PROP A a ⋅ to_all PROP B (cast b eq_pf) = to_all PROP A (a ⋅ b).
Proof.
  apply FunctionalExtensionality.functional_extensionality_dep_good.
  intros C. rewrite discrete_fun_lookup_op. subst. simpl.
  rewrite /to_all.
  destruct excluded_middle_informative as [Heq|Hbad];
    destruct excluded_middle_informative as [Heq'|Hbad']; try done.
  2:{ exfalso. rewrite -Heq in Hbad'. done. }
  2:{ exfalso. rewrite -Heq' in Hbad. done. }
  destruct Heq, Heq'. simpl in *. rewrite cast_self //.
Qed.

Section own.
Context `{!allG Σ}.

Class SimpleCmra A :=
  {
    Aexp : cmra_expr.t;
    eq_proof : A = cmra_expr.interpret (iProp Σ) Aexp;
  }.

Definition owna_def {A : cmra} γ (a : A) : iProp Σ :=
  ∃ (S : SimpleCmra A), own γ (to_all (iProp Σ) Aexp (cast a eq_proof) : allUR (iProp Σ)).
Program Definition owna := sealed @owna_def.
Final Obligation. econstructor. done. Qed.
Definition owna_unseal : owna = _ := seal_eq _.

Global Arguments owna {A} (γ a).

(** Core facts that requires unfolding [owna] *)
Section core.

(*
  [*] own_ne
  [*] own_op
  [*] own_valid
  [*] own_timeless
  [*] own_persistent
  [ ] later_own
  [*] own_alloc_strong_dep
  [ ] own_updateP
  [ ] own_unit
  [ ] own_forall
 *)

Global Instance owna_ne A γ : NonExpansive (@owna A γ).
Proof.
  rewrite owna_unseal.
  intros ???. intros.
  apply bi.exist_ne. intros ?. apply own_ne.
  intros ?. rewrite /to_all. destruct excluded_middle_informative; try done.
  simpl in *. destruct e. simpl.
  destruct a. subst. simpl. apply Some_ne. done.
Qed.

Lemma owna_op {A : cmra} γ (a1 a2 : A) :
  owna γ (a1 ⋅ a2) ⊣⊢ owna γ a1 ∗ owna γ a2.
Proof.
  rewrite owna_unseal.
  iSplit.
  - iIntros "[% H]". destruct S. subst. simpl in *.
    rewrite -(to_all_op (B:=Aexp0)). iDestruct "H" as "[H1 H2]". simpl.
    iSplitL "H1"; iExists {| Aexp := Aexp0; eq_proof := eq_refl |}; iFrame.
  - iIntros "[[% H1] [% H2]]". destruct S, S0. subst.
    iExists {| Aexp := Aexp0; eq_proof := eq_refl |}. simpl.
    iCombine "H1 H2" as "H". simpl. iExactEq "H". f_equal. rewrite to_all_op //.
Qed.

Lemma owna_valid γ {A : cmra} (a : A) :
  owna γ a ⊢ ✓ a.
Proof.
  rewrite owna_unseal.
  iIntros "[% Hown]". iDestruct (own_valid with "Hown") as "Hv".
  rewrite discrete_fun_validI. destruct S. subst.
  iSpecialize ("Hv" $! Aexp0). rewrite option_validI. simpl.
  rewrite /to_all. destruct excluded_middle_informative; try done.
  simpl in *. destruct e. done.
Qed.

Global Instance owna_timeless {A : cmra} `{!SimpleCmra A} γ (a : A) :
  Discrete a → Timeless (owna γ a).
Proof.
  rewrite /Timeless. rewrite !owna_unseal /owna_def. intros ?.
  iIntros "H". assert (Inhabited (SimpleCmra A)) by done.
  iDestruct "H" as (?) "H". iExists _.
  destruct S. subst. simpl in *.
  assert (Discrete (to_all (iProp Σ) Aexp0 a)).
  - rewrite /to_all. intros a' Heq. intros B. specialize (Heq B).
    simpl in *. destruct excluded_middle_informative.
    + simpl in *. destruct a'; try done.
      * rewrite dist_Some in Heq.
        destruct e. simpl in *.
        apply H in Heq. setoid_rewrite Heq. done.
      * exfalso. rewrite dist_None // in Heq.
    + simpl in *. destruct a'; try done.
      exfalso. symmetry in Heq. rewrite dist_None // in Heq.
  - iMod "H". iFrame.
Qed.

Global Instance owna_core_persistent {A : cmra} γ (a : A) : CoreId a → Persistent (owna γ a).
Proof.
  rewrite !owna_unseal. intros Hcore.
  apply exist_persistent. intros S. apply own_core_persistent.
  rewrite /CoreId. rewrite /to_all.
  rewrite cmra_pcore_core. apply Some_proper.
  intros B. rewrite /core /=.
  destruct excluded_middle_informative; try done.
  destruct S. simpl in *. destruct e. simpl in *.
  destruct eq_proof0. simpl in *. done.
Qed.

Lemma owna_update γ {A : cmra} (a a' : A) :
  a ~~> a' →
  owna γ a ==∗ owna γ a'.
Proof.
  rewrite owna_unseal.
  intros Hupd. iIntros "[% Hown]".
  iExists _. iApply (own_update with "Hown").
  apply to_all_update. destruct S.
  simpl in *. destruct eq_proof0. simpl.
  apply Hupd.
Qed.

Lemma owna_alloc_strong_dep {A} {S : SimpleCmra A} (f : gname → A) (P : gname → Prop) :
  pred_infinite P →
  (∀ γ, P γ → ✓ (f γ)) →
  ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ owna γ (f γ).
Proof.
  rewrite owna_unseal. intros Hpred Hvalid.
  iMod (own_alloc_strong_dep
          (λ γ,
             (to_all (iProp Σ) Aexp (eq_rect A id (f γ) _ eq_proof) : allUR (iProp Σ))) P
          ) as (γ) "H".
  { done. }
  { intros γ HP. rewrite /= /to_all. intros B.
    destruct excluded_middle_informative as [Heq|Hbad]; last done.
    destruct S. subst. simpl in *. destruct Heq. simpl in *.
    apply Some_valid. apply Hvalid. done. }
  by iDestruct "H" as "($ & $)".
Qed.

End core.

Global Instance own_any_combine {A : cmra} γ (a b : A) :
  CombineSepAs (owna γ a) (owna γ b) (owna γ (a ⋅ b)).
Proof.
  rewrite /CombineSepAs. iIntros "[H1 H2]".
  rewrite owna_op. iFrame.
Qed.

Lemma owna_alloc `{!SimpleCmra A} (a : A) :
  ✓ a →
  ⊢ |==> ∃ γ, owna γ a.
Proof.
  iIntros "%Hvalid".
  iMod (owna_alloc_strong_dep (const a) (λ γ, True)) as (?) "[_ H]"; try done.
  { intros g. eexists (fresh g). by split; last apply infinite_is_fresh. }
  by iFrame.
Qed.

Instance mlist_simple_cmra (A : Type) : SimpleCmra (mono_listR (leibnizO A)).
Proof. by eexists (cmra_expr.mono_list A). Qed.

Lemma own_any_mono_list (l : list nat) :
  ⊢ |==> ∃ γ, owna γ (●ML l).
Proof.
  iApply owna_alloc. apply mono_list_auth_valid.
Qed.

Instance own_proper :
  ∀ {A : cmra} (γ : gname), Proper (equiv ==> equiv) (@owna A γ).
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
  owna γ (to_dfrac_agree dq (Next ∘ Φ : oFunctor_apply (A -d> ▶ ∙) (iPropO PROP))).

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
  ⊢ |==> ∃ γ, owna γ (to_dfrac_agree (DfracOwn 1)
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
