(** This file provides a universal cmra and a new notion of ownership that
   allows for using many different cmras in proofs, without having separate
   [inG] assumptions for each algebra as is typical in Iris.

   Instead of Iris's built-in [own] predicate, use this file's
   [own γ (a : A)] predicate, which requires ensuring proofs have [allG Σ] in
   their context. The single [allG Σ] covers a large class of cmras, and is
   meant to be a singleton in all proofs (there should never be more than one in
   context). *)

(** For developers: the universal cmra is roughly a coproduct of all supported
   cmras. This is an infinite coproduct, as it supports e.g. [authR A] for any
   type [A]. The type [syntax.cmra] is the indexing type for the coproduct, and
   each one denotes some actual [cmra] via [int_cmra]. To add more cmras, add it
   to [syntax], and then also add the relevant [IsCmra] instances; [IsCmra]
   helps map an arbitrary [cmra] into some [syntax.cmra] as evidence that it is
   included in the universal cmra.

   Iris does not provide a coproduct cmra library. Iris does provide arbitrary
   products of [ucmra]s via [discrete_funUR]. In the category of ucmras,
   coproducts and products are similar (e.g. think coproduct and product of
   abelian groups being similar: ∐ᵢ Aᵢ = ⨁ᵢ Aᵢ ⊆ ∏ᵢ Aᵢ). Moreover, [optionUR]
   turns any [cmra] into a [ucmra] in a nice way. Put together, this allows for
   having (something bigger than) the coproduct as [discrete_funUR (optionUR ∘
   int_cmra)]. *)

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

Module syntax.
Inductive ofe :=
| unitO
| leibnizO (A : Type)
.

Inductive cmra :=
| authR (A : ucmra)
| gmap_viewR (K : Type) `{Countable K} (V : cmra)
| saved_propR
| saved_predR (A : Type)

| agreeR (A : ofe)
| gmapR (K : Type) `{Countable K} (V : cmra)
| prodR (A B : cmra)
| optionR (A : cmra)
| csumR (A B : cmra)
| exclR (A : ofe)
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
| max_prefix_listUR (A : ofe)
| gmapUR (K : Type) `{Countable K} (V : cmra)
| natUR.
End syntax.

Section denote.
Context (PROP : ofe) `{!Cofe PROP} .

Definition int_ofe (x : syntax.ofe) : ofe :=
  match x with
  | syntax.unitO => unitO
  | syntax.leibnizO A => leibnizO A
  end.

Fixpoint int_cmra (x : syntax.cmra) : cmra :=
  match x with
  | syntax.authR A => authR (int_ucmra A)
  | syntax.gmap_viewR K V => gmap_viewR K (int_cmra V)
  | syntax.saved_propR => dfrac_agreeR (laterO PROP)
  | syntax.saved_predR A => dfrac_agreeR (A -d> laterO PROP)

  | syntax.agreeR A => agreeR (int_ofe A)
  | syntax.gmapR K V => gmapR K (int_cmra V)
  | syntax.prodR A B => prodR (int_cmra A) (int_cmra B)
  | syntax.optionR A => optionR (int_cmra A)
  | syntax.csumR A B => csumR (int_cmra A) (int_cmra B)
  | syntax.exclR A => exclR (int_ofe A)

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
with int_ucmra (x : syntax.ucmra) : ucmra :=
  match x with
  | syntax.gset_disjUR K => gset_disjUR K
  | syntax.max_prefix_listUR A => max_prefix_listUR (int_ofe A)
  | syntax.gmapUR K V => gmapUR K (int_cmra V)
  | syntax.natUR => natUR
  end.

Fixpoint intF_cmra (x : syntax.cmra) : rFunctor :=
  match x with
  | syntax.authR A => authRF (intF_ucmra A)
  | syntax.gmap_viewR K V => gmap_viewRF K (intF_cmra V)

  | syntax.saved_propR => (dfrac_agreeRF (▶ ∙))
  | syntax.saved_predR A => (dfrac_agreeRF (A -d> ▶ ∙))

  | syntax.agreeR A => agreeR (int_ofe A)
  | syntax.gmapR K V => gmapRF K (intF_cmra V)
  | syntax.prodR A B => prodRF (intF_cmra A) (intF_cmra B)
  | syntax.optionR A => optionRF (intF_cmra A)
  | syntax.csumR A B => csumRF (intF_cmra A) (intF_cmra B)
  | syntax.exclR A => exclR (int_ofe A)

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
with intF_ucmra (x : syntax.ucmra) : urFunctor :=
match x with
| syntax.gset_disjUR K => gset_disjUR K
| syntax.max_prefix_listUR A => max_prefix_listUR (int_ofe A)
| syntax.gmapUR K V => gmapURF K (intF_cmra V)
| syntax.natUR => natUR
end.

Class IsCmra (A : cmra) (e : syntax.cmra) :=
  { eq_cmra : A = int_cmra e; }.
Global Hint Mode IsCmra ! - : typeclass_instances.
Class IsUcmra (A : ucmra) (e : syntax.ucmra) :=
  { eq_ucmra : A = int_ucmra e; }.
Global Hint Mode IsUcmra ! - : typeclass_instances.
Class IsOfe (A : ofe) (e : syntax.ofe) :=
  { eq_ofe : A = int_ofe e; }.
Global Hint Mode IsOfe ! - : typeclass_instances.

Local Ltac s :=
  constructor; simpl;
  repeat (lazymatch goal with
          | H : IsCmra _ _ |- _ => apply @eq_cmra in H; rewrite -H; clear H
          | H : IsUcmra _ _ |- _ => apply @eq_ucmra in H; rewrite -H; clear H
          | H : IsOfe _ _ |- _ => apply @eq_ofe in H; rewrite -H; clear H
          end);
  try done.

#[global] Instance is_prodR `{!IsCmra A Ae} `{!IsCmra B Be} : IsCmra (prodR A B) (syntax.prodR Ae Be).
Proof. s. Qed.
#[global] Instance is_authR `{!IsUcmra A Ae} : IsCmra (authR A) (syntax.authR Ae).
Proof. s. Qed.
#[global] Instance is_gmap_viewR K `{Countable K} `{!IsCmra V Ve} :
  IsCmra (gmap_viewR K V) (syntax.gmap_viewR K Ve).
Proof. s. Qed.
#[global] Instance is_saved_propR : IsCmra (dfrac_agreeR (laterO PROP)) (syntax.saved_propR).
Proof. s. Qed.
#[global] Instance is_saved_predR A : IsCmra (dfrac_agreeR (A -d> laterO PROP)) (syntax.saved_predR A).
Proof. s. Qed.
#[global] Instance is_agreeR `{!IsOfe A Ae} :
  IsCmra (agreeR A) (syntax.agreeR Ae).
Proof. s. Qed.
#[global] Instance is_gmapR K `{Countable K} `{!IsCmra V Ve} :
  IsCmra (gmapR K V) (syntax.gmapR K Ve).
Proof. s. Qed.
#[global] Instance is_optionR `{!IsCmra A Ae} :
  IsCmra (optionR A) (syntax.optionR Ae).
Proof. s. Qed.
#[global] Instance is_csumR `{!IsCmra A Ae} `{!IsCmra B Be} :
  IsCmra (csumR A B) (syntax.csumR Ae Be).
Proof. s. Qed.
#[global] Instance is_exclR `{!IsOfe A Ae} :
  IsCmra (exclR A) (syntax.exclR Ae).
Proof. s. Qed.
#[global] Instance is_natR : IsCmra natR syntax.natR.
Proof. s. Qed.
#[global] Instance is_max_natR : IsCmra max_natR syntax.max_natR.
Proof. s. Qed.
#[global] Instance is_min_natR : IsCmra min_natR syntax.min_natR.
Proof. s. Qed.
#[global] Instance is_positiveR : IsCmra positiveR syntax.positiveR.
Proof. s. Qed.
#[global] Instance is_ZR : IsCmra ZR syntax.ZR.
Proof. s. Qed.
#[global] Instance is_max_ZR : IsCmra max_ZR syntax.max_ZR.
Proof. s. Qed.
#[global] Instance is_gmultisetR K `{Countable K} : IsCmra (gmultisetR K) (syntax.gmultisetR K).
Proof. s. Qed.
#[global] Instance is_fracR : IsCmra fracR syntax.fracR.
Proof. s. Qed.
#[global] Instance is_gsetR K `{Countable K} : IsCmra (gsetR K) (syntax.gsetR K).
Proof. s. Qed.
#[global] Instance is_dfracR : IsCmra dfracR syntax.dfracR.
Proof. s. Qed.
#[global] Instance is_gset_disjUR K `{Countable K} : IsUcmra (gset_disjUR K) (syntax.gset_disjUR K).
Proof. s. Qed.
#[global] Instance is_max_prefix_listUR `{!IsOfe A Ae} :
  IsUcmra (max_prefix_listUR A) (syntax.max_prefix_listUR Ae).
Proof. s. Qed.
#[global] Instance is_gmapUR K `{Countable K} `{!IsCmra V Ve} :
  IsUcmra (gmapUR K V) (syntax.gmapUR K Ve).
Proof. s. Qed.
#[global] Instance is_natUR :
  IsUcmra natUR syntax.natUR.
Proof. s. Qed.
#[global] Instance is_unitO :
  IsOfe unitO syntax.unitO.
Proof. s. Qed.
#[global] Instance is_leibnizO A :
  IsOfe (leibnizO A) (syntax.leibnizO A).
Proof. s. Qed.
End denote.

Arguments eq_cmra {_ _ _ _}.
Arguments eq_ucmra {_ _ _ _}.

Definition allUR (PROP : ofe) `{!Cofe PROP}
  : Type := discrete_funUR (optionUR ∘ int_cmra PROP).

Definition allURF := discrete_funURF (λ A, optionURF (intF_cmra A)).

Global Instance all_contractive : urFunctorContractive allURF.
Proof.
  apply discrete_funURF_contractive.
  intro A. apply optionURF_contractive. revert A.
  fix I 1 with
    (pf_u A : urFunctorContractive (intF_ucmra A)); intros A.
  { induction A; simpl in *; try tc_solve. }
  { induction A; simpl in *; try tc_solve. }
Qed.

Definition allΣ : gFunctors :=
  #[ GFunctor (urFunctor_to_rFunctor allURF) ].

Class allG Σ :=
  { #[local] any_inG :: inG Σ (allUR (iPropO Σ)); }.

Local Lemma interpret_eq_intF A Σ :
  (intF_cmra A).(rFunctor_car) (iPropO Σ) (iPropO Σ) =
  (int_cmra (iPropO Σ) A).
Proof.
  revert A.
  fix I 1 with
    (pf_u A : (intF_ucmra A).(urFunctor_car) (iPropO Σ) (iPropO Σ) = int_ucmra (iPropO Σ) A
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
  intros. rewrite interpret_eq_intF //.
Qed.

Local Instance ucmra_expr_eq_decision : EqDecision syntax.ucmra.
Proof.
  intros A B. destruct (excluded_middle_informative (A = B)); [left|right]; done.
Qed.

Local Instance cmra_expr_eq_decision : EqDecision syntax.cmra.
Proof.
  intros A B. destruct (excluded_middle_informative (A = B)); [left|right]; done.
Qed.

Section own.
Context `{!allG Σ}.

Definition own_def `{!IsCmra (iProp Σ) A e} γ (a : A) : iProp Σ :=
  own γ (discrete_fun_singleton (B:=optionUR ∘ int_cmra (iProp Σ)) e
           (Some (cmra_transport eq_cmra a))).

Program Definition own := sealed @own_def.
Definition own_unseal : own = _ := seal_eq _.
Global Arguments own {A _ _} (γ a).

Context {A e} {HC : IsCmra (iProp Σ) A e}.
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

Lemma own_unit {B : ucmra} Be {HB : IsCmra (iProp Σ) B Be} γ :
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
