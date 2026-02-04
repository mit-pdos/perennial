From New.proof Require Import proof_prelude.
From iris.algebra Require Import
  gset functions reservation_map mra dyn_reservation_map view gmultiset csum
  gmap_view max_prefix_list dfrac_agree.
From iris.bi Require Import fractional.
From Coq Require Import Logic.ClassicalEpsilon.

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
| gmapUR (K : Type) `{Countable K} (V : cmra).
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
end.

Class Is (A : cmra) (e : syntax.cmra) :=
  { eq_cmra : A = interpret e; }.
Global Hint Mode Is + - : typeclass_instances.

Class IsU (A : ucmra) (e : syntax.ucmra) :=
  { eq_ucmra : A = interpret_u e; }.
Global Hint Mode IsU + - : typeclass_instances.

Local Ltac s :=
  constructor; simpl;
  repeat (lazymatch goal with
          | H : Is _ _ |- _ => apply @eq_cmra in H; rewrite -H; clear H
          | H : IsU _ _ |- _ => apply @eq_ucmra in H; rewrite -H; clear H
          end);
  try done.

#[global] Instance is_prodR `{!Is A Ae} `{!Is B Be} :
  Is (prodR A B) (syntax.prodR Ae Be).
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
  apply FunctionalExtensionality.functional_extensionality_dep_good.
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

Definition owna_def `{!Is (iProp Σ) A e} γ (a : A) : iProp Σ :=
  own γ (discrete_fun_singleton (B:=optionUR ∘ interpret (iProp Σ)) e
           (Some (cmra_transport eq_cmra a))).

Program Definition owna := sealed @owna_def.
Final Obligation. econstructor. done. Qed.
Definition owna_unseal : owna = _ := seal_eq _.

Global Arguments owna {A _ _} (γ a).

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
  [*] own_updateP
  [*] own_unit
  [ ] own_forall
 *)

Section with_A.
Context {A e} {HC : cmra_expr.Is (PROP:=iProp Σ) A e}.

Ltac start :=
  rewrite owna_unseal /owna_def; destruct HC; clear HC; subst; simpl in *.
Global Instance owna_ne γ : NonExpansive (owna (A:=A) γ).
Proof. start. solve_proper. Qed.

Lemma owna_op  γ (a1 a2 : A) :
  owna γ (a1 ⋅ a2) ⊣⊢ owna γ a1 ∗ owna γ a2.
Proof.
  start. rewrite -own_op discrete_fun_singleton_op Some_op //.
Qed.

Lemma owna_valid γ (a : A) :
  owna γ a ⊢ ✓ a.
Proof.
  start. iIntros "H". iDestruct (own_valid with "H") as "H".
  rewrite discrete_fun_validI. iSpecialize ("H" $! e).
  rewrite discrete_fun_lookup_singleton option_validI //.
Qed.

Global Instance owna_timeless γ (a : A) :
  Discrete a → Timeless (owna γ a).
Proof. start. apply _. Qed.

Global Instance owna_core_persistent γ (a : A) : CoreId a → Persistent (owna γ a).
Proof. start. apply _. Qed.

Lemma owna_updateP P γ (a : A) : a ~~>: P → owna γ a ⊢ |==> ∃ a', ⌜P a'⌝ ∗ owna γ a'.
Proof.
  start. iIntros "%Hupd H". iDestruct (own_updateP with "H") as "H".
  { eapply discrete_fun_singleton_updateP'. by apply option_updateP'. }
  iMod "H" as (?) "[% H]". destruct H as (? & ? & ?). subst.
  destruct x; try done. simpl in *. iExists c. by iFrame.
Qed.

Lemma owna_alloc_strong_dep (f : gname → A) (P : gname → Prop) :
  pred_infinite P →
  (∀ γ, P γ → ✓ (f γ)) →
  ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ owna γ (f γ).
Proof.
  start. intros Hpred Hvalid.
  iApply own_alloc_strong_dep; first done.
  intros ?. rewrite discrete_fun_singleton_valid Some_valid. apply Hvalid.
Qed.

End with_A.

Lemma owna_unit {A : ucmra} e {HC : cmra_expr.Is A e} γ :
  ⊢ |==> owna γ (ε : A).
Proof.
  destruct HC; subst; simpl in *. rewrite owna_unseal.
  simpl in *. rewrite /owna_def.
  iMod own_unit as "H". iApply (own_update with "H"). simpl.
  apply discrete_fun_singleton_update_empty.
  intros n []; simpl in *.
  - intros H. rewrite left_id in H. destruct c.
    + rewrite -Some_op Some_validN.
      replace (c) with (cmra_transport eq_proof (cmra_transport (eq_sym eq_proof) c)).
      2:{ clear. destruct eq_proof. done. }
      rewrite -cmra_transport_op. apply cmra_transport_validN.
      rewrite Some_validN in H. rewrite -cmra_transport_validN in H.
      rewrite left_id //.
    + rewrite right_id. apply cmra_transport_validN, ucmra_unit_validN.
  - intros Hbad. apply Some_validN.
    apply cmra_transport_validN, ucmra_unit_validN.
Qed.

End core.

Section derived.

Global Instance owna_proper γ :
  Proper ((≡) ==> (⊣⊢)) (@owna A γ) := ne_proper _.

Section needs_simple.
Context `{!SimpleCmra A}.
Implicit Type (a : A).
Local Set Default Proof Using "All".
Lemma owna_alloc_cofinite_dep (f : gname → A) (G : gset gname) :
  (∀ γ, γ ∉ G → ✓ (f γ)) → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ owna γ (f γ).
Proof.
  intros Ha.
  apply (owna_alloc_strong_dep f (λ γ, γ ∉ G))=> //.
  apply (pred_infinite_set (C:=gset gname)).
  intros E. set (γ := fresh (G ∪ E)).
  exists γ. apply not_elem_of_union, is_fresh.
Qed.
Lemma owna_alloc_dep (f : gname → A) :
  (∀ γ, ✓ (f γ)) → ⊢ |==> ∃ γ, owna γ (f γ).
Proof.
  intros Ha. rewrite /bi_emp_valid (owna_alloc_cofinite_dep f ∅) //; [].
  apply bupd_mono, exist_mono=>?. apply: sep_elim_r.
Qed.

Lemma owna_alloc_strong a (P : gname → Prop) :
  pred_infinite P →
  ✓ a → ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ owna γ a.
Proof. intros HP Ha. eapply (owna_alloc_strong_dep (λ _, a)); eauto. Qed.
Lemma owna_alloc_cofinite a (G : gset gname) :
  ✓ a → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ owna γ a.
Proof. intros Ha. eapply (owna_alloc_cofinite_dep (λ _, a)); eauto. Qed.
Lemma owna_alloc a : ✓ a → ⊢ |==> ∃ γ, owna γ a.
Proof. intros Ha. eapply (owna_alloc_dep (λ _, a)); eauto. Qed.
End needs_simple.

Lemma owna_update_2 {A : cmra} γ (a1 a2 a' : A) :
  a1 ⋅ a2 ~~> a' → owna γ a1 -∗ owna γ a2 ==∗ owna γ a'.
Proof. intros. apply entails_wand, wand_intro_r. rewrite -owna_op. by iApply owna_update. Qed.


Section proofmode_instances.
  Context {A : cmra}.
  Implicit Types a b : A.

  Global Instance into_sep_owna γ a b1 b2 :
    IsOp a b1 b2 → IntoSep (owna γ a) (owna γ b1) (owna γ b2).
  Proof. intros. by rewrite /IntoSep (is_op a) owna_op. Qed.
  Global Instance into_and_owna p γ a b1 b2 :
    IsOp a b1 b2 → IntoAnd p (owna γ a) (owna γ b1) (owna γ b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) owna_op sep_and. Qed.

  Global Instance from_sep_owna γ a b1 b2 :
    IsOp a b1 b2 → FromSep (owna γ a) (owna γ b1) (owna γ b2).
  Proof. intros. by rewrite /FromSep -owna_op -is_op. Qed.
  (* TODO: Improve this instance with generic owna simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_owna γ a b1 b2 :
    IsOp a b1 b2 → CombineSepAs (owna γ b1) (owna γ b2) (owna γ a) | 60.
  Proof. intros. by rewrite /CombineSepAs -owna_op -is_op. Qed.
  (* TODO: Improve this instance with generic owna validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_gives_owna γ b1 b2 :
    CombineSepGives (owna γ b1) (owna γ b2) (✓ (b1 ⋅ b2)).
  Proof.
    intros. rewrite /CombineSepGives -owna_op owna_valid.
    by apply: bi.persistently_intro.
  Qed.
  Global Instance from_and_owna_persistent γ a b1 b2 :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (owna γ a) (owna γ b1) (owna γ b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) owna_op.
    destruct Hb; by rewrite persistent_and_sep.
  Qed.
End proofmode_instances.

End derived.
End own.

Section saved_pred.
  Context `{!allG Σ}.
  Context {A : Type}.

  Local Instance s :
    SimpleCmra (Σ:=Σ) (dfrac_agreeR (oFunctor_apply (A -d> ▶ ∙) (iPropO Σ))).
  Proof.
    refine {| Aexp := cmra_expr.saved_pred A; eq_proof := eq_refl |}.
  Qed.

  Definition saved_pred_own (γ : gname) (dq : dfrac) (Φ : A → iProp Σ) :=
    owna γ (to_dfrac_agree dq (Next ∘ Φ : oFunctor_apply (A -d> ▶ ∙) (iPropO Σ))).

  Global Instance saved_pred_own_contractive `{!savedPredG Σ A} γ dq :
    Contractive (saved_pred_own γ dq : (A -d> iPropO Σ) → iProp Σ).
  Proof.
    solve_proper_core ltac:(fun _ => first [ intros ?; progress simpl | by auto | f_contractive | f_equiv ]).
  Qed.

  Global Instance saved_pred_discarded_persistent γ Φ :
    Persistent (saved_pred_own γ DfracDiscarded Φ).
  Proof. apply _. Qed.

  Global Instance saved_pred_fractional γ Φ : Fractional (λ q, saved_pred_own γ (DfracOwn q) Φ).
  Proof. intros q1 q2. rewrite /saved_pred_own -owna_op -dfrac_agree_op //. Qed.
  Global Instance saved_pred_as_fractional γ Φ q :
    AsFractional (saved_pred_own γ (DfracOwn q) Φ) (λ q, saved_pred_own γ (DfracOwn q) Φ) q.
  Proof. split; [done|]. apply _. Qed.

  (** Allocation *)
  Lemma saved_pred_alloc_strong (I : gname → Prop) (Φ : A → iProp Σ) dq :
    ✓ dq →
    pred_infinite I →
    ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_pred_own γ dq Φ.
  Proof. intros ??. by apply owna_alloc_strong. Qed.

  Lemma saved_pred_alloc_cofinite (G : gset gname) (Φ : A → iProp Σ) dq :
    ✓ dq →
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_pred_own γ dq Φ.
  Proof. intros ?. by apply owna_alloc_cofinite. Qed.

  Lemma saved_pred_alloc (Φ : A → iProp Σ) dq :
    ✓ dq →
    ⊢ |==> ∃ γ, saved_pred_own γ dq Φ.
  Proof. intros ?. by apply owna_alloc. Qed.

  (** Validity *)
  Lemma saved_pred_valid γ dq Φ :
    saved_pred_own γ dq Φ -∗ ⌜✓ dq⌝.
  Proof.
    rewrite /saved_pred_own owna_valid dfrac_agree_validI //. eauto.
  Qed.
  Lemma saved_pred_valid_2 γ dq1 dq2 Φ Ψ x :
    saved_pred_own γ dq1 Φ -∗ saved_pred_own γ dq2 Ψ -∗ ⌜✓ (dq1 ⋅ dq2)⌝ ∗ ▷ (Φ x ≡ Ψ x).
  Proof.
    iIntros "Hx Hy". rewrite /saved_pred_own.
    iCombine "Hx Hy" gives "Hv".
    rewrite dfrac_agree_validI_2. iDestruct "Hv" as "[$ Hag]".
    iApply later_equivI. by iApply (discrete_fun_equivI with "Hag").
  Qed.
  Lemma saved_pred_agree γ dq1 dq2 Φ Ψ x :
    saved_pred_own γ dq1 Φ -∗ saved_pred_own γ dq2 Ψ -∗ ▷ (Φ x ≡ Ψ x).
  Proof. iIntros "HΦ HΨ". iPoseProof (saved_pred_valid_2 with "HΦ HΨ") as "[_ $]". Qed.

  (** Make an element read-only. *)
  Lemma saved_pred_persist γ dq Φ :
    saved_pred_own γ dq Φ ==∗ saved_pred_own γ DfracDiscarded Φ.
  Proof.
    iApply owna_update. apply dfrac_agree_persist.
  Qed.

  (* FIXME: own_updateP *)
  (* (** Recover fractional ownership for read-only element. *) *)
  (* Lemma saved_pred_unpersist γ Φ: *)
  (*   saved_pred_own γ DfracDiscarded Φ ==∗ ∃ q, saved_pred_own γ (DfracOwn q) Φ. *)
  (* Proof. *)
  (*   iIntros "H". *)
  (*   iMod (own_updateP with "H") as "H"; *)
  (*     first by apply dfrac_agree_unpersist. *)
  (*   iDestruct "H" as (? (q&->)) "H". *)
  (*   iIntros "!>". iExists q. done. *)
  (* Qed. *)

  (** Updates *)
  Lemma saved_pred_update Ψ γ Φ :
    saved_pred_own γ (DfracOwn 1) Φ ==∗ saved_pred_own γ (DfracOwn 1) Ψ.
  Proof.
    iApply owna_update. apply cmra_update_exclusive. done.
  Qed.
  Lemma saved_pred_update_2 Ψ γ q1 q2 Φ1 Φ2 :
    (q1 + q2 = 1)%Qp →
    saved_pred_own γ (DfracOwn q1) Φ1 -∗ saved_pred_own γ (DfracOwn q2) Φ2 ==∗
    saved_pred_own γ (DfracOwn q1) Ψ ∗ saved_pred_own γ (DfracOwn q2) Ψ.
  Proof.
    intros Hq. rewrite -owna_op. iApply owna_update_2.
    apply dfrac_agree_update_2.
    rewrite dfrac_op_own Hq //.
  Qed.
  Lemma saved_pred_update_halves Ψ γ Φ1 Φ2 :
    saved_pred_own γ (DfracOwn (1/2)) Φ1 -∗
    saved_pred_own γ (DfracOwn (1/2)) Φ2 ==∗
    saved_pred_own γ (DfracOwn (1/2)) Ψ ∗ saved_pred_own γ (DfracOwn (1/2)) Ψ.
  Proof. iApply saved_pred_update_2. apply Qp.half_half. Qed.
End saved_pred.

(* Print Assumptions own_any_mono_list.
  constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
  classic : ∀ P : Prop, P ∨ ¬ P
*)

Section ghost_map.

Section instance.
Context `{!allG Σ}.
Context `{Countable K} {V : Type}.
Local Instance simple : SimpleCmra (Σ:=Σ) (gmap_viewR K (agreeR $ leibnizO V)).
Proof.
  refine {| Aexp := cmra_expr.gmap_view K (cmra_expr.agree V); eq_proof := eq_refl |}.
Qed.
End instance.

Existing Instance simple.
Section definitions.
  Context `{!allG Σ}.
  Context `{Countable K} {V : Type}.

  Local Definition ghost_map_auth_def
      (γ : gname) (q : Qp) (m : gmap K V) : iProp Σ :=
    owna γ (gmap_view_auth (V:=agreeR $ leibnizO V) (DfracOwn q) (to_agree <$> m)).
  Local Definition ghost_map_auth_aux : seal (@ghost_map_auth_def).
  Proof. by eexists. Qed.
  Definition ghost_map_auth := ghost_map_auth_aux.(unseal).
  Local Definition ghost_map_auth_unseal :
    @ghost_map_auth = @ghost_map_auth_def := ghost_map_auth_aux.(seal_eq).

  Local Definition ghost_map_elem_def
      (γ : gname) (k : K) (dq : dfrac) (v : V) : iProp Σ :=
    owna γ (gmap_view_frag (V:=agreeR $ leibnizO V) k dq (to_agree v)).
  Local Definition ghost_map_elem_aux : seal (@ghost_map_elem_def).
  Proof. by eexists. Qed.
  Definition ghost_map_elem := ghost_map_elem_aux.(unseal).
  Local Definition ghost_map_elem_unseal :
    @ghost_map_elem = @ghost_map_elem_def := ghost_map_elem_aux.(seal_eq).
End definitions.

Notation "k ↪[ γ ] dq v" := (ghost_map_elem γ k dq v)
  (at level 20, γ at level 50, dq custom dfrac at level 1,
   format "k  ↪[ γ ] dq  v") : bi_scope.

Local Ltac unseal := rewrite
  ?ghost_map_auth_unseal /ghost_map_auth_def
  ?ghost_map_elem_unseal /ghost_map_elem_def.

Section lemmas.
  Context `{!allG Σ}.
  Context `{Countable K} {V : Type}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V).

  (** * Lemmas about the map elements *)
  Global Instance ghost_map_elem_timeless k γ dq v : Timeless (k ↪[γ]{dq} v).
  Proof. unseal.
         apply owna_timeless.
         apply _. Qed.
  Global Instance ghost_map_elem_persistent k γ v : Persistent (k ↪[γ]□ v).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_map_elem_fractional k γ v :
    Fractional (λ q, k ↪[γ]{#q} v)%I.
  Proof. unseal=> p q. rewrite -owna_op -gmap_view_frag_add agree_idemp //. Qed.
  Global Instance ghost_map_elem_as_fractional k γ q v :
    AsFractional (k ↪[γ]{#q} v) (λ q, k ↪[γ]{#q} v)%I q.
  Proof. split; first done. apply _. Qed.

  Local Lemma ghost_map_elems_unseal γ m dq :
    ([∗ map] k ↦ v ∈ m, k ↪[γ]{dq} v) ==∗
    owna γ ([^op map] k↦v ∈ m,
      gmap_view_frag (V:=agreeR (leibnizO V)) k dq (to_agree v)).
  Proof.
    unseal. destruct (decide (m = ∅)) as [->|Hne].
    - rewrite !big_opM_empty. iIntros "_". (* iApply owna_unit. *) admit. (* FIXME: primitive *)
    - (* rewrite big_opM_own //. iIntros "?". done. *) admit. (* FIXME: lemma *)
  Admitted.

  Lemma ghost_map_elem_valid k γ dq v : k ↪[γ]{dq} v -∗ ⌜✓ dq⌝.
  Proof.
    unseal. iIntros "Helem".
    iDestruct (owna_valid with "Helem") as %?%gmap_view_frag_valid.
    naive_solver.
  Qed.
  Lemma ghost_map_elem_valid_2 k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iCombine "H1 H2" gives %[? Hag]%gmap_view_frag_op_valid.
    rewrite to_agree_op_valid_L in Hag. done.
  Qed.
  Lemma ghost_map_elem_agree k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (ghost_map_elem_valid_2 with "Helem1 Helem2") as %[_ ?].
    done.
  Qed.

  Global Instance ghost_map_elem_combine_gives γ k v1 dq1 v2 dq2 :
    CombineSepGives (k ↪[γ]{dq1} v1) (k ↪[γ]{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[H1 H2].
    eauto.
  Qed.

  Lemma ghost_map_elem_combine k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ k ↪[γ]{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (ghost_map_elem_agree with "Hl1 Hl2") as %->.
    unseal. iCombine "Hl1 Hl2" as "Hl". rewrite agree_idemp. eauto with iFrame.
  Qed.

  Global Instance ghost_map_elem_combine_as k γ dq1 dq2 v1 v2 :
    CombineSepAs (k ↪[γ]{dq1} v1) (k ↪[γ]{dq2} v2) (k ↪[γ]{dq1 ⋅ dq2} v1) | 60.
    (* higher cost than the Fractional instance [combine_sep_fractional_bwd],
       which kicks in for #qs *)
  Proof.
    rewrite /CombineSepAs. iIntros "[H1 H2]".
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[$ _]".
  Qed.

  Lemma ghost_map_elem_frac_ne γ k1 k2 dq1 dq2 v1 v2 :
    ¬ ✓ (dq1 ⋅ dq2) → k1 ↪[γ]{dq1} v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof.
    iIntros (?) "H1 H2"; iIntros (->).
    by iCombine "H1 H2" gives %[??].
  Qed.
  Lemma ghost_map_elem_ne γ k1 k2 dq2 v1 v2 :
    k1 ↪[γ] v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof. apply ghost_map_elem_frac_ne. apply: exclusive_l. Qed.

  (** Make an element read-only. *)
  Lemma ghost_map_elem_persist k γ dq v :
    k ↪[γ]{dq} v ==∗ k ↪[γ]□ v.
  Proof. unseal. iApply owna_update. apply gmap_view_frag_persist. Qed.

  (** Recover fractional ownaership for read-only element. *)
  Lemma ghost_map_elem_unpersist k γ v :
    k ↪[γ]□ v ==∗ ∃ q, k ↪[γ]{# q} v.
  Proof.
    unseal. iIntros "H".
  (*   iMod (owna_updateP with "H") as "H"; *)
  (*     first by apply gmap_view_frag_unpersist. *)
  (*   iDestruct "H" as (? (q&->)) "H". *)
  (*   iIntros "!>". iExists q. done. *)
  (* Qed. *)
  Admitted. (* FIXME: *)

  (** * Lemmas about [ghost_map_auth] *)
  Lemma ghost_map_alloc_strong P m :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ghost_map_auth γ 1 m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ] v.
  Proof.
    unseal. intros.
    iMod (owna_alloc_strong
      (gmap_view_auth (V:=agreeR (leibnizO V)) (DfracOwn 1) ∅) P)
      as (γ) "[% Hauth]"; first done.
    { eapply gmap_view_auth_valid. }
    iExists γ. iSplitR; first done.
    rewrite -big_opM_owna_1 -owna_op. iApply (owna_update with "Hauth").
    etrans; first apply (gmap_view_alloc_big _ (to_agree <$> m) (DfracOwna 1)).
    - apply map_disjoint_empty_r.
    - done.
    - by apply map_Forall_fmap.
    - rewrite right_id big_opM_fmap. done.
  Qed.
  Lemma ghost_map_alloc_strong_empty P :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ghost_map_auth γ 1 (∅ : gmap K V).
  Proof.
    intros. iMod (ghost_map_alloc_strong P ∅) as (γ) "(% & Hauth & _)"; eauto.
  Qed.
  Lemma ghost_map_alloc m :
    ⊢ |==> ∃ γ, ghost_map_auth γ 1 m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ] v.
  Proof.
    iMod (ghost_map_alloc_strong (λ _, True) m) as (γ) "[_ Hmap]".
    - by apply pred_infinite_True.
    - eauto.
  Qed.
  Lemma ghost_map_alloc_empty :
    ⊢ |==> ∃ γ, ghost_map_auth γ 1 (∅ : gmap K V).
  Proof.
    intros. iMod (ghost_map_alloc ∅) as (γ) "(Hauth & _)"; eauto.
  Qed.

  Global Instance ghost_map_auth_timeless γ q m : Timeless (ghost_map_auth γ q m).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_map_auth_fractional γ m : Fractional (λ q, ghost_map_auth γ q m)%I.
  Proof. intros p q. unseal. rewrite -owna_op -gmap_view_auth_dfrac_op //. Qed.
  Global Instance ghost_map_auth_as_fractional γ q m :
    AsFractional (ghost_map_auth γ q m) (λ q, ghost_map_auth γ q m)%I q.
  Proof. split; first done. apply _. Qed.

  Lemma ghost_map_auth_valid γ q m : ghost_map_auth γ q m -∗ ⌜q ≤ 1⌝%Qp.
  Proof.
    unseal. iIntros "Hauth".
    iDestruct (owna_valid with "Hauth") as %?%gmap_view_auth_dfrac_valid.
    done.
  Qed.
  Lemma ghost_map_auth_valid_2 γ q1 q2 m1 m2 :
    ghost_map_auth γ q1 m1 -∗ ghost_map_auth γ q2 m2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ m1 = m2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    (* We need to explicitly specify the Inj instances instead of
    using inj _ since we need to specify [leibnizO] for [to_agree_inj]. *)
    iCombine "H1 H2" gives %[? ?%(map_fmap_equiv_inj _
      (to_agree_inj (A:=(leibnizO _))))]%gmap_view_auth_dfrac_op_valid.
    iPureIntro. split; first done. by fold_leibniz.
  Qed.
  Lemma ghost_map_auth_agree γ q1 q2 m1 m2 :
    ghost_map_auth γ q1 m1 -∗ ghost_map_auth γ q2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  (** * Lemmas about the interaction of [ghost_map_auth] with the elements *)
  Lemma ghost_map_lookup {γ q m k dq v} :
    ghost_map_auth γ q m -∗ k ↪[γ]{dq} v -∗ ⌜m !! k = Some v⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    iCombine "Hauth Hel" gives
      %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
    iPureIntro.
    apply lookup_fmap_Some in Hav' as [v' [<- Hv']].
    (* FIXME: Why do we need [(SI:=natSI) (A:=leibnizO V)]
    https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/555 seems to resolve
    the problem? *)
    apply (to_agree_included_L (SI:=natSI) (A:=leibnizO V)) in Hincl.
    by rewrite Hincl.
  Qed.

  Global Instance ghost_map_lookup_combine_gives_1 {γ q m k dq v} :
    CombineSepGives (ghost_map_auth γ q m) (k ↪[γ]{dq} v) ⌜m !! k = Some v⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (ghost_map_lookup with "H1 H2") as %->. eauto.
  Qed.

  Global Instance ghost_map_lookup_combine_gives_2 {γ q m k dq v} :
    CombineSepGives (k ↪[γ]{dq} v) (ghost_map_auth γ q m) ⌜m !! k = Some v⌝.
  Proof.
    rewrite /CombineSepGives comm. apply ghost_map_lookup_combine_gives_1.
  Qed.

  Lemma ghost_map_insert {γ m} k v :
    m !! k = None →
    ghost_map_auth γ 1 m ==∗ ghost_map_auth γ 1 (<[k := v]> m) ∗ k ↪[γ] v.
  Proof.
    unseal. intros Hm. rewrite -owna_op.
    iApply owna_update. rewrite fmap_insert. apply: gmap_view_alloc; [|done..].
    rewrite lookup_fmap Hm //.
  Qed.
  Lemma ghost_map_insert_persist {γ m} k v :
    m !! k = None →
    ghost_map_auth γ 1 m ==∗ ghost_map_auth γ 1 (<[k := v]> m) ∗ k ↪[γ]□ v.
  Proof.
    iIntros (?) "Hauth".
    iMod (ghost_map_insert k with "Hauth") as "[$ Helem]"; first done.
    iApply ghost_map_elem_persist. done.
  Qed.

  Lemma ghost_map_delete {γ m k v} :
    ghost_map_auth γ 1 m -∗ k ↪[γ] v ==∗ ghost_map_auth γ 1 (delete k m).
  Proof.
    unseal. iApply bi.wand_intro_r. rewrite -owna_op.
    iApply owna_update. rewrite fmap_delete. apply: gmap_view_delete.
  Qed.

  Lemma ghost_map_update {γ m k v} w :
    ghost_map_auth γ 1 m -∗ k ↪[γ] v ==∗ ghost_map_auth γ 1 (<[k := w]> m) ∗ k ↪[γ] w.
  Proof.
    unseal. iApply bi.wand_intro_r. rewrite -!owna_op.
    iApply owna_update. rewrite fmap_insert. apply: gmap_view_replace; done.
  Qed.

  (** Big-op versions of above lemmas *)
  Lemma ghost_map_lookup_big {γ q m dq} m0 :
    ghost_map_auth γ q m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ]{dq} v) -∗
    ⌜m0 ⊆ m⌝.
  Proof.
    iIntros "Hauth Hfrag". rewrite map_subseteq_spec. iIntros (k v Hm0).
    iDestruct (ghost_map_lookup with "Hauth [Hfrag]") as %->.
    { rewrite big_sepM_lookup; done. }
    done.
  Qed.

  Lemma ghost_map_insert_big {γ m} m' :
    m' ##ₘ m →
    ghost_map_auth γ 1 m ==∗
    ghost_map_auth γ 1 (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ] v).
  Proof.
    unseal. intros ?. rewrite -big_opM_owna_1 -owna_op. iApply owna_update.
    etrans; first apply: (gmap_view_alloc_big _ (to_agree <$> m') (DfracOwna 1)).
    - apply map_disjoint_fmap. done.
    - done.
    - by apply map_Forall_fmap.
    - rewrite map_fmap_union big_opM_fmap. done.
  Qed.
  Lemma ghost_map_insert_persist_big {γ m} m' :
    m' ##ₘ m →
    ghost_map_auth γ 1 m ==∗
    ghost_map_auth γ 1 (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ]□ v).
  Proof.
    iIntros (Hdisj) "Hauth".
    iMod (ghost_map_insert_big m' with "Hauth") as "[$ Helem]"; first done.
    iApply big_sepM_bupd. iApply (big_sepM_impl with "Helem").
    iIntros "!#" (k v) "_". iApply ghost_map_elem_persist.
  Qed.

  Lemma ghost_map_delete_big {γ m} m0 :
    ghost_map_auth γ 1 m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ] v) ==∗
    ghost_map_auth γ 1 (m ∖ m0).
  Proof.
    iIntros "Hauth Hfrag". iMod (ghost_map_elems_unseal with "Hfrag") as "Hfrag".
    unseal. iApply (owna_update_2 with "Hauth Hfrag").
    rewrite map_fmap_difference.
    etrans; last apply: gmap_view_delete_big.
    rewrite big_opM_fmap. done.
  Qed.

  Theorem ghost_map_update_big {γ m} m0 m1 :
    dom m0 = dom m1 →
    ghost_map_auth γ 1 m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ] v) ==∗
    ghost_map_auth γ 1 (m1 ∪ m) ∗
        [∗ map] k↦v ∈ m1, k ↪[γ] v.
  Proof.
    iIntros (?) "Hauth Hfrag".
    iMod (ghost_map_elems_unseal with "Hfrag") as "Hfrag".
    unseal. rewrite -big_opM_owna_1 -owna_op.
    iApply (owna_update_2 with "Hauth Hfrag").
    rewrite map_fmap_union.
    rewrite -!(big_opM_fmap to_agree (λ k, gmap_view_frag k (DfracOwna 1))).
    apply: gmap_view_replace_big.
    - rewrite !dom_fmap_L. done.
    - by apply map_Forall_fmap.
  Qed.

End lemmas.
