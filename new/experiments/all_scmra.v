From iris.algebra Require Export
  gset functions reservation_map mra dyn_reservation_map view gmultiset csum
  gmap_view max_prefix_list dfrac_agree auth excl numbers proofmode_classes.
From Coq Require Import Logic.ClassicalEpsilon Logic.FunctionalExtensionality.
From iris.base_logic Require Export proofmode iprop.
From iris.base_logic Require Import own.
From Perennial.Helpers Require Export
  Tactics List ListLen Transitions ModArith iris ipm.
From Perennial Require Export base.
Export uPred.

Global Set Default Proof Using "Type".
Global Set Printing Projections.

Module syntax.
Inductive cmra :=
| authR (A : ucmra)
| gmap_viewR (K : Type) `{Countable K} (V : cmra)
| saved_propR
| saved_predR (A : Type)

| agreeR (A : Type)
| gmapR (K : Type) `{Countable K} (V : cmra)
| prodR (A B : cmra)
| optionR (A : cmra)
| csumR (A B : cmra)
| exclR (A : Type)
| natR
| max_natR
| min_natR
| positiveR
| ZR
| max_ZR
| gmultisetR (K : Type) `{Countable K}
| fracR
| gsetR (K : Type) `{Countable K}
| dfracR
with ucmra :=
| gset_disjUR (K : Type) `{Countable K}
| max_prefix_listUR (A : Type)
| gmapUR (K : Type) `{Countable K} (V : cmra)
| natUR.
End syntax.

Section denote.
Context (PROP : ofe) `{!Cofe PROP} .
Fixpoint interpret (x : syntax.cmra) : cmra :=
  match x with
  | syntax.authR A => authR (interpret_u A)
  | syntax.gmap_viewR K V => gmap_viewR K (interpret V)
  | syntax.saved_propR => dfrac_agreeR (laterO PROP)
  | syntax.saved_predR A => dfrac_agreeR (A -d> laterO PROP)

  | syntax.agreeR A => agreeR (leibnizO A)
  | syntax.gmapR K V => gmapR K (interpret V)
  | syntax.prodR A B => prodR (interpret A) (interpret B)
  | syntax.optionR A => optionR (interpret A)
  | syntax.csumR A B => csumR (interpret A) (interpret B)
  | syntax.exclR A => exclR (leibnizO A)

  | syntax.natR => natR
  | syntax.max_natR => max_natR
  | syntax.min_natR => min_natR
  | syntax.positiveR => positiveR
  | syntax.ZR => ZR
  | syntax.max_ZR => max_ZR
  | syntax.gmultisetR K => gmultisetR K
  | syntax.fracR => fracR
  | syntax.gsetR K => gsetR K
  | syntax.dfracR => dfracR
  end
with interpret_u (x : syntax.ucmra) : ucmra :=
match x with
| syntax.gset_disjUR K => gset_disjUR K
| syntax.max_prefix_listUR A => max_prefix_listUR (leibnizO A)
| syntax.gmapUR K V => gmapUR K (interpret V)
| syntax.natUR => natUR
end.

Fixpoint interpretF (x : syntax.cmra) : rFunctor :=
  match x with
  | syntax.authR A => authRF (interpretF_u A)
  | syntax.gmap_viewR K V => gmap_viewRF K (interpretF V)

  | syntax.saved_propR => (dfrac_agreeRF (▶ ∙))
  | syntax.saved_predR A => (dfrac_agreeRF (A -d> ▶ ∙))

  | syntax.agreeR A => agreeR (leibnizO A)
  | syntax.gmapR K V => gmapRF K (interpretF V)
  | syntax.prodR A B => prodRF (interpretF A) (interpretF B)
  | syntax.optionR A => optionRF (interpretF A)
  | syntax.csumR A B => csumRF (interpretF A) (interpretF B)
  | syntax.exclR A => exclR (leibnizO A)

  | syntax.natR => natR
  | syntax.max_natR => max_natR
  | syntax.min_natR => min_natR
  | syntax.positiveR => positiveR
  | syntax.ZR => ZR
  | syntax.max_ZR => max_ZR
  | syntax.gmultisetR K => gmultisetR K
  | syntax.fracR => fracR
  | syntax.gsetR K => gsetR K
  | syntax.dfracR => dfracR
  end
with interpretF_u (x : syntax.ucmra) : urFunctor :=
match x with
| syntax.gset_disjUR K => gset_disjUR K
| syntax.max_prefix_listUR A => max_prefix_listUR (leibnizO A)
| syntax.gmapUR K V => gmapURF K (interpretF V)
| syntax.natUR => natUR
end.

Class Is (A : cmra) (e : syntax.cmra) :=
  { eq_cmra : A = interpret e; }.
Global Hint Mode Is ! - : typeclass_instances.

Class IsU (A : ucmra) (e : syntax.ucmra) :=
  { eq_ucmra : A = interpret_u e; }.
Global Hint Mode IsU ! - : typeclass_instances.

Local Ltac s :=
  constructor; simpl;
  repeat (lazymatch goal with
          | H : Is _ _ |- _ => apply @eq_cmra in H; rewrite -H; clear H
          | H : IsU _ _ |- _ => apply @eq_ucmra in H; rewrite -H; clear H
          end);
  try done.

#[global] Instance is_prodR `{!Is A Ae} `{!Is B Be} : Is (prodR A B) (syntax.prodR Ae Be).
Proof. s. Qed.
#[global] Instance is_authR `{!IsU A Ae} : Is (authR A) (syntax.authR Ae).
Proof. s. Qed.
#[global] Instance is_gmap_viewR K `{Countable K} `{!Is V Ve} :
  Is (gmap_viewR K V) (syntax.gmap_viewR K Ve).
Proof. s. Qed.
#[global] Instance is_saved_propR : Is (dfrac_agreeR (laterO PROP)) (syntax.saved_propR).
Proof. s. Qed.
#[global] Instance is_saved_predR A : Is (dfrac_agreeR (A -d> laterO PROP)) (syntax.saved_predR A).
Proof. s. Qed.
#[global] Instance is_agreeR A :
  Is (agreeR (leibnizO A)) (syntax.agreeR A).
Proof. s. Qed.
#[global] Instance is_gmapR K `{Countable K} `{!Is V Ve} :
  Is (gmapR K V) (syntax.gmapR K Ve).
Proof. s. Qed.
#[global] Instance is_optionR `{!Is A Ae} :
  Is (optionR A) (syntax.optionR Ae).
Proof. s. Qed.
#[global] Instance is_csumR `{!Is A Ae} `{!Is B Be} :
  Is (csumR A B) (syntax.csumR Ae Be).
Proof. s. Qed.
#[global] Instance is_exclR A :
  Is (exclR (leibnizO A)) (syntax.exclR A).
Proof. s. Qed.
#[global] Instance is_natR : Is natR syntax.natR.
Proof. s. Qed.
#[global] Instance is_max_natR : Is max_natR syntax.max_natR.
Proof. s. Qed.
#[global] Instance is_min_natR : Is min_natR syntax.min_natR.
Proof. s. Qed.
#[global] Instance is_positiveR : Is positiveR syntax.positiveR.
Proof. s. Qed.
#[global] Instance is_ZR : Is ZR syntax.ZR.
Proof. s. Qed.
#[global] Instance is_max_ZR : Is max_ZR syntax.max_ZR.
Proof. s. Qed.
#[global] Instance is_gmultisetR K `{Countable K} : Is (gmultisetR K) (syntax.gmultisetR K).
Proof. s. Qed.
#[global] Instance is_fracR : Is fracR syntax.fracR.
Proof. s. Qed.
#[global] Instance is_gsetR K `{Countable K} : Is (gsetR K) (syntax.gsetR K).
Proof. s. Qed.
#[global] Instance is_dfracR : Is dfracR syntax.dfracR.
Proof. s. Qed.
#[global] Instance is_gset_disjUR K `{Countable K} : IsU (gset_disjUR K) (syntax.gset_disjUR K).
Proof. s. Qed.
#[global] Instance is_max_prefix_listUR A :
  IsU (max_prefix_listUR (leibnizO A)) (syntax.max_prefix_listUR A).
Proof. s. Qed.
#[global] Instance is_gmapUR K `{Countable K} `{!Is V Ve} :
  IsU (gmapUR K V) (syntax.gmapUR K Ve).
Proof. s. Qed.
#[global] Instance is_natUR :
  IsU natUR syntax.natUR.
Proof. s. Qed.
End denote.

Arguments eq_cmra {_ _ _ _}.
Arguments eq_ucmra {_ _ _ _}.

Definition allUR (PROP : ofe) `{!Cofe PROP}
  : Type := discrete_funUR (optionUR ∘ interpret PROP).

Definition allURF := discrete_funURF (λ A, optionURF (interpretF A)).

Global Instance all_contractive : urFunctorContractive allURF.
Proof.
  apply discrete_funURF_contractive.
  intro A. apply optionURF_contractive. revert A.
  fix I 1 with
    (pf_u A : urFunctorContractive (interpretF_u A)); intros A.
  { induction A; simpl in *; try tc_solve. }
  { induction A; simpl in *; try tc_solve. }
Qed.

Definition allΣ : gFunctors :=
  #[ GFunctor (urFunctor_to_rFunctor allURF) ].

Class allG Σ :=
  { #[local] any_inG :: inG Σ (allUR (iPropO Σ)); }.

Local Lemma interpret_eq_interpretF A Σ :
  (interpretF A).(rFunctor_car) (iPropO Σ) (iPropO Σ) =
  (interpret (iPropO Σ) A).
Proof.
  revert A.
  fix I 1 with
    (pf_u A : (interpretF_u A).(urFunctor_car) (iPropO Σ) (iPropO Σ) = interpret_u (iPropO Σ) A
    ); intros A.
  - induction A; simpl in *; rewrite ?pf_u; try done.
    + unfold rFunctor_apply in *. rewrite IHA //.
    + unfold rFunctor_apply in *. rewrite IHA //.
    + unfold rFunctor_apply in *. rewrite IHA1 IHA2 //.
    + unfold rFunctor_apply in *. rewrite IHA //.
    + unfold rFunctor_apply in *. rewrite IHA1 IHA2 //.
  - induction A; simpl in *; rewrite ?I; try done.
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
  apply functional_extensionality_dep_good.
  intros. rewrite interpret_eq_interpretF //.
Qed.

Local Instance ucmra_expr_eq_decision : EqDecision syntax.ucmra.
Proof.
  intros A B. destruct (excluded_middle_informative (A = B)); [left|right]; done.
Qed.

Local Instance cmra_expr_eq_decision : EqDecision syntax.cmra.
Proof.
  intros A B. destruct (excluded_middle_informative (A = B)); [left|right]; done.
Qed.

Definition to_all (PROP : ofe) `{!Cofe PROP}
  (A : syntax.cmra) (a : interpret PROP A) : allUR PROP :=
    discrete_fun_singleton (B:=optionUR ∘ interpret PROP) A (Some a).

Section own.
Context `{!allG Σ}.

Definition own_def `{!Is (iProp Σ) A e} γ (a : A) : iProp Σ :=
  own γ (discrete_fun_singleton (B:=optionUR ∘ interpret (iProp Σ)) e
           (Some (cmra_transport eq_cmra a))).

Program Definition own := sealed @own_def.
Definition own_unseal : own = _ := seal_eq _.
Global Arguments own {A _ _} (γ a).

Context {A e} {HC : Is (iProp Σ) A e}.
Implicit Types (a : A).

(** Core facts that requires unfolding [own] *)
Section core.

(*
  [*] own_ne
  [*] own_op
  [*] own_valid
  [*] own_timeless
  [*] own_persistent
  [ ] later_own
  [*] own_alloc_strong_dep
  [*] own_updateP
  [*] own_unit
  [ ] own_forall
 *)

Ltac start :=
  rewrite own_unseal /own_def; destruct HC; clear HC; subst; simpl in *.

Global Instance own_ne γ : NonExpansive (own (A:=A) γ).
Proof. start. solve_proper. Qed.

Lemma own_op γ (a1 a2 : A) :
  own γ (a1 ⋅ a2) ⊣⊢ own γ a1 ∗ own γ a2.
Proof.
  start. rewrite -own_op discrete_fun_singleton_op Some_op //.
Qed.

Lemma own_valid γ (a : A) :
  own γ a ⊢ ✓ a.
Proof.
  start. iIntros "H". iDestruct (own_valid with "H") as "H".
  rewrite discrete_fun_validI. iSpecialize ("H" $! e).
  rewrite discrete_fun_lookup_singleton option_validI //.
Qed.

Global Instance own_timeless γ (a : A) :
  Discrete a → Timeless (own γ a).
Proof. start. apply _. Qed.

Global Instance own_core_persistent γ (a : A) : CoreId a → Persistent (own γ a).
Proof. start. apply _. Qed.

Lemma own_updateP P γ (a : A) : a ~~>: P → own γ a ⊢ |==> ∃ a', ⌜P a'⌝ ∗ own γ a'.
Proof.
  start. iIntros "%Hupd H". iDestruct (own_updateP with "H") as "H".
  { eapply discrete_fun_singleton_updateP'. by apply option_updateP'. }
  iMod "H" as (?) "[% H]". destruct H as (? & ? & ?). subst.
  destruct x; try done. simpl in *. iExists c. by iFrame.
Qed.

Lemma own_alloc_strong_dep (f : gname → A) (P : gname → Prop) :
  pred_infinite P →
  (∀ γ, P γ → ✓ (f γ)) →
  ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ (f γ).
Proof.
  start. intros Hpred Hvalid.
  iApply own_alloc_strong_dep; first done.
  intros ?. rewrite discrete_fun_singleton_valid Some_valid. apply Hvalid.
Qed.

Lemma own_unit {B : ucmra} Be {HB : Is (iProp Σ) B Be} γ :
  ⊢ |==> own γ (ε : B).
Proof.
  destruct HB; subst; simpl in *. rewrite own_unseal.
  simpl in *. rewrite /own_def.
  iMod own_unit as "H". iApply (own_update with "H"). simpl.
  apply discrete_fun_singleton_update_empty.
  intros n []; simpl in *.
  - intros H. rewrite left_id in H. destruct c.
    + rewrite -Some_op Some_validN.
      replace (c) with (cmra_transport eq_cmra0 (cmra_transport (eq_sym eq_cmra0) c)).
      2:{ clear. destruct eq_cmra0. done. }
      rewrite -cmra_transport_op. apply cmra_transport_validN.
      rewrite Some_validN in H. rewrite -cmra_transport_validN in H.
      rewrite left_id //.
    + rewrite right_id. apply cmra_transport_validN, ucmra_unit_validN.
  - intros Hbad. apply Some_validN.
    apply cmra_transport_validN, ucmra_unit_validN.
Qed.

End core.
End own.
