From stdpp Require Export sets coPset.
From iris.algebra Require Export cmra functions frac.
From iris.algebra Require Import updates local_updates.
From iris.prelude Require Import options.
From Perennial.base_logic Require Export lib.own.
From iris.proofmode Require Import tactics.

Record frac_coPset :=
  { fc_carrier :> @discrete_fun positive (fun _ => optionO fracR) }.

Section ofe.
  Global Instance frac_coPset_equiv : Equiv (frac_coPset) := λ f g, (fc_carrier f) ≡ (fc_carrier g).
  Global Instance frac_coPset_dist : Dist (frac_coPset) := λ n f g, (fc_carrier f) ≡{n}≡ (fc_carrier g).
  Definition frac_coPset_ofe_mixin : OfeMixin (frac_coPset).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + intros [f] [g] [h] ?? x. trans (g x); eauto.
    - by intros n f g ? x; apply dist_S.
  Qed.
  Canonical Structure frac_coPsetO := Ofe (frac_coPset) frac_coPset_ofe_mixin.
  Global Instance frac_coPset_ofe_discrete :
    OfeDiscrete (frac_coPsetO).
  Proof. intros f f' Heq i. apply Heq. Qed.

  Program Definition frac_coPset_chain `(c : chain frac_coPsetO)
   (x : positive) : chain (optionO fracO) := {| chain_car n := (fc_carrier (c n)) x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.

  Global Instance frac_coPset_fun_inhabited : Inhabited frac_coPsetO :=
    populate {| fc_carrier := (λ _, None) |}.
End ofe.

Section frac_coPset_cmra.
  Implicit Types f g : frac_coPset.

  Local Instance frac_coPset_valid_instance : Valid (frac_coPset) := λ f,
    (∀ x, ✓ (fc_carrier f) x) ∧
    (∃ E : coPset, (∀ p : positive, is_Some (fc_carrier f p) → p ∈ E) ∧ set_infinite (⊤ ∖ E)).
  Local Instance frac_coPset_validN_instance : ValidN (frac_coPset) := λ n f,
    (∀ x, ✓ (fc_carrier f) x) ∧
    (∃ E : coPset, (∀ p : positive, is_Some (fc_carrier f p) → p ∈ E) ∧ set_infinite (⊤ ∖ E)).

  Local Instance frac_coPset_op_instance : Op (frac_coPset) :=
    λ f g, {| fc_carrier := λ x, (fc_carrier f) x ⋅ (fc_carrier g) x |}.
  Local Instance frac_coPset_pcore_instance : PCore (frac_coPset) := λ f,
   Some {| fc_carrier := λ x, core (fc_carrier f x) |}.

  Lemma frac_coPset_lookup_op f g x : fc_carrier (f ⋅ g) x = fc_carrier f x ⋅ fc_carrier g x.
  Proof. auto. Qed.

  Lemma frac_coPset_lookup_core f x : fc_carrier (core f) x = core (fc_carrier f x).
  Proof. auto. Qed.

  Lemma frac_coPset_included_spec_1 f g x : f ≼ g → (fc_carrier f) x ≼ (fc_carrier g) x.
  Proof. by intros [h Hh]; exists (fc_carrier h x); rewrite /op /frac_coPset_op_instance (Hh x). Qed.

  Lemma frac_coPset_ra_mixin : RAMixin frac_coPset.
  Proof.
    apply ra_total_mixin; eauto.
    - intros f1 f2 f3 Hf x. by rewrite ?frac_coPset_lookup_op (Hf x).
    - intros f1 f2 Hf x. by rewrite ?frac_coPset_lookup_core (Hf x).
    - intros f1 f2 Hf (Hvalf&Hdomf).
      split.
      * intros x. specialize (Hf x). apply leibniz_equiv in Hf as <-. auto.
      * destruct Hdomf as (E&Hdom&Hcofin). exists E. split; auto.
        intros x Hsome. apply Hdom. specialize (Hf x). apply leibniz_equiv in Hf as ->. auto.
    - intros f1 f2 f3 x. by rewrite ?frac_coPset_lookup_op ?assoc.
    - intros f1 f2 x. rewrite ?frac_coPset_lookup_op. apply comm, _.
    - intros f x. by rewrite frac_coPset_lookup_op frac_coPset_lookup_core cmra_core_l.
    - by intros f x; rewrite frac_coPset_lookup_core cmra_core_idemp.
    - intros f1 f2 Hf12. exists (core f2)=>x. rewrite frac_coPset_lookup_op.
      apply (frac_coPset_included_spec_1 _ _ x), (cmra_core_mono (fc_carrier f1 x)) in Hf12.
      rewrite !frac_coPset_lookup_core. destruct Hf12 as [? ->].
      rewrite assoc -cmra_core_dup //.
    - intros f1 f2 (Hf&Hdom).
      split.
      * intros x. apply cmra_valid_op_l with (fc_carrier f2 x), Hf.
      * destruct Hdom as (E&Hdom&Hcofin). exists E; split; auto.
        intros x Hsome. apply Hdom.
        rewrite frac_coPset_lookup_op.
        destruct (fc_carrier f1 x), (fc_carrier f2 x) => //=.
        { eexists; eauto. }
        { inversion Hsome. congruence. }
  Qed.
  Canonical Structure frac_coPsetR :=
    (Cmra frac_coPset (discrete_cmra_mixin _ frac_coPset_ra_mixin)).

  Global Instance frac_coPsetR_cmra_discrete:
    CmraDiscrete (frac_coPsetR).
  Proof. split; [apply _|]. intros x Hv. apply Hv. Qed.

  Local Instance frac_coPsetR_empty_instance : Unit (frac_coPset) :=
    {| fc_carrier := (fun _ => None) |}.

  Lemma frac_coPset_ucmra_mixin : UcmraMixin frac_coPset.
  Proof.
    split; try apply _ || done.
    - split.
      * intros; econstructor.
      * exists ∅; split.
        ** intros ? => //=. inversion 1. congruence.
        ** replace (⊤ ∖ ∅) with (⊤ : coPset) by set_solver. apply top_infinite.
    - intros f x. rewrite frac_coPset_lookup_op //= left_id //.
  Qed.
  Canonical Structure frac_coPsetUR := Ucmra frac_coPset frac_coPset_ucmra_mixin.
End frac_coPset_cmra.

Section frac_coPset_cmra_lemmas.

  Definition fCoPset (q : Qp) (E : coPset) : frac_coPsetR :=
    {| fc_carrier := λ p, if decide (p ∈ E) then Some q else None |}.

  Lemma fCoPset_valid1 (q : Qp) (E : coPset) :
    ✓ (fCoPset q E) → set_infinite (⊤ ∖ E).
  Proof.
    destruct 1 as (Hval&Hdom). destruct Hdom as (E'&Hp&Hcofin).
    assert (⊤ ∖ E' ⊆ ⊤ ∖ E).
    { cut (E ⊆ E'); first by set_solver.
      intros i Hin. apply Hp. exists q => //=.
      destruct decide; naive_solver. }
    eapply set_infinite_subseteq; eauto.
  Qed.

  Lemma fCoPset_valid2 (q : Qp) (E : coPset) :
    (q ≤ 1)%Qp →
    set_infinite (⊤ ∖ E) →
    ✓ fCoPset q E.
  Proof.
    intros Hle Hcofin.
    split.
    - intros x => //=; destruct (decide (x ∈ E)) => //=.
    - exists E. split; auto.
      intros x => //=; destruct (decide (x ∈ E)) => //=.
      inversion 1; congruence.
  Qed.

  Lemma fCoPset_op_plus q1 q2 E :
    fCoPset (q1 + q2) E ≡ fCoPset q1 E ⋅ fCoPset q2 E.
  Proof. intros x => //=. destruct (decide (x ∈ E)) => //=. Qed.

  Lemma fCoPset_op_union q E1 E2 :
    E1 ## E2 →
    fCoPset q (E1 ∪ E2) ≡ fCoPset q E1 ⋅ fCoPset q E2.
  Proof.
    intros Hdisj x => //=.
    repeat (destruct (decide (x ∈ _))) => //=; set_solver.
  Qed.

  Lemma fCoPset_op_difference q E1 E2 :
    E1 ⊆ E2 →
    fCoPset q E2 ≡ fCoPset q E1 ⋅ fCoPset q (E2 ∖ E1).
  Proof.
    intros. rewrite -fCoPset_op_union; last set_solver.
    by rewrite -union_difference_L.
  Qed.

  Lemma fCoPset_valid_op1 q1 q2 E1 E2 :
    (1 < q1 + q2)%Qp →
    ✓ (fCoPset q1 E1 ⋅ fCoPset q2 E2) → E1 ## E2 ∧ set_infinite (⊤ ∖ (E1 ∪ E2)).
  Proof.
    intros Hlt (Hval&Hdom).
    split.
    * destruct (decide (E1 ## E2)); auto.
      intros x Hin1 Hin2.
      specialize (Hval x).
      rewrite /fCoPset//= in Hval.
      repeat (destruct (decide _)); try set_solver; [].
      revert Hval. rewrite -Some_op Some_valid frac_valid => ?.
      eapply Qp_le_ngt; eauto.
    * destruct Hdom as (E&Hdom&Hcofin).
      assert (⊤ ∖ E ⊆ ⊤ ∖ (E1 ∪ E2)).
      { cut (E1 ∪ E2 ⊆ E); first by set_solver.
        intros x Hin. apply Hdom => //=.
        apply op_is_Some.
        destruct (decide _); first eauto.
        right.
        destruct (decide _); first eauto.
        set_solver.
      }
      eapply set_infinite_subseteq; try eassumption.
  Qed.

  Lemma fCoPset_valid_op2 q1 q2 E1 E2 :
    (q1 ≤ 1)%Qp →
    (q2 ≤  1)%Qp →
    E1 ## E2 ∧ set_infinite (⊤ ∖ (E1 ∪ E2)) → ✓ (fCoPset q1 E1 ⋅ fCoPset q2 E2).
  Proof.
    intros Hlt1 Hlt2.
    intros (Hdisj&Hinf).
    split.
    * intros x => //=.
      repeat (destruct (decide _)); try naive_solver; try set_solver.
    * exists (E1 ∪ E2). split; auto.
      intros p. rewrite //=.
      rewrite op_is_Some.
      repeat (destruct (decide _)); try naive_solver; try set_solver.
      destruct 1 as [[]|[]]; congruence.
  Qed.

  (* Based on dyn_reservation_map *)
  Lemma frac_coPset_reserve (Q : frac_coPset → Prop) :
    (∀ E, set_infinite E → Q (fCoPset 1 E)) →
    ε ~~>: Q.
  Proof.
    intros HQ. apply cmra_total_updateP=> n f.
      rewrite left_id. intros (Hval&Hdom) => /=.
      destruct Hdom as (Ef&Hdom&Hcofin).
    edestruct (coPset_split_infinite (⊤ ∖ Ef)) as
        (E1 & E2 & HEunion & HEdisj & HE1inf & HE2inf); auto.
    exists (fCoPset 1 E1).
    split; first by apply HQ. clear HQ.
    split.
    - intros x. rewrite frac_coPset_lookup_op //=.
      destruct (decide _).
      * destruct (fc_carrier f x) eqn:Heq.
        ** exfalso. cut (x ∈ Ef); first by set_solver.
           apply Hdom; eauto.
        ** rewrite //=.
      * rewrite left_id //.
    - exists (E1 ∪ Ef).
      split.
      * intros x. rewrite frac_coPset_lookup_op.
        rewrite op_is_Some. intros [Hl|Hr].
        ** set_unfold. left. destruct (decide _); eauto.
           inversion Hl; congruence.
        ** set_unfold. right. apply Hdom; auto.
      * assert (⊤ ∖ (E1 ∪ Ef) = E2) as ->; auto.
        set_solver.
  Qed.
  Lemma frac_coPset_reserve' :
    ε ~~>: (λ x, ∃ E, set_infinite E ∧ x = fCoPset 1 E).
  Proof. eauto using frac_coPset_reserve. Qed.

End frac_coPset_cmra_lemmas.

Section frac_coPset_prop.
  Context {Σ : gFunctors}.
  Context {Hin: inG Σ (frac_coPsetR)}.

  Definition ownfCP γ q E : iProp Σ := own γ (fCoPset q E).

  Lemma ownfCP_init γ : ⊢ |==> ∃ E, ownfCP γ 1 E.
  Proof.
    iMod (own_unit _ γ) as "H".
    iMod (own_updateP with "[$]") as "HE".
    { apply frac_coPset_reserve'. }
    iDestruct "HE" as (fCP Hpure) "Hown".
    destruct Hpure as (E&Hinf&->).
    iModIntro; iExists _; iFrame.
  Qed.

  Lemma ownfCP_init_empty γ : ⊢ |==> ownfCP γ 1 ∅.
  Proof. iMod (own_unit _ γ) as "H". by iFrame. Qed.

  Lemma ownfCP_op_plus γ q1 q2 E :
    ownfCP γ (q1 + q2) E ⊣⊢ ownfCP γ q1 E ∗ ownfCP γ q2 E.
  Proof. by rewrite /ownfCP fCoPset_op_plus own_op. Qed.

  Lemma ownfCP_op_union γ q E1 E2 :
    E1 ## E2 →
    ownfCP γ q E1 ∗ ownfCP γ q E2 ⊣⊢ ownfCP γ q (E1 ∪ E2).
  Proof. intros. by rewrite /ownfCP fCoPset_op_union // own_op. Qed.

  Definition ownfCP_inf γ q E : iProp Σ :=
    ⌜ set_infinite E ⌝ ∧ own γ (fCoPset q E).

  Lemma ownfCP_inf_init γ : ⊢ |==> ∃ E, ownfCP_inf γ 1 E.
  Proof.
    iMod (own_unit _ γ) as "H".
    iMod (own_updateP with "[$]") as "HE".
    { apply frac_coPset_reserve'. }
    iDestruct "HE" as (fCP Hpure) "Hown".
    destruct Hpure as (E&Hinf&->).
    iModIntro; iExists _; iSplit; first eauto. iFrame.
  Qed.

  Lemma ownfCP_inf_op_plus γ q1 q2 E :
    ownfCP_inf γ (q1 + q2) E ⊣⊢ ownfCP_inf γ q1 E ∗ ownfCP_inf γ q2 E.
  Proof.
    iSplit.
    - iDestruct 1 as (Hinf) "Hown".
      rewrite fCoPset_op_plus own_op.
      iDestruct "Hown" as "(H1&H2)".
      iFrame. eauto.
    - iDestruct 1 as "(H1&H2)".
      iDestruct "H1" as (Hinf1) "Hown1".
      iDestruct "H2" as (Hinf2) "Hown2".
      iSplit; first eauto. rewrite fCoPset_op_plus own_op; by iFrame.
  Qed.

  Lemma ownfCP_op_union_join γ q E1 E2 :
    E1 ## E2 →
    ownfCP_inf γ q E1 ∗ ownfCP_inf γ q E2 ⊢ ownfCP_inf γ q (E1 ∪ E2).
  Proof.
    iIntros (Hdisj).
    iDestruct 1 as "(H1&H2)".
    iDestruct "H1" as (Hinf1) "Hown1".
    iDestruct "H2" as (Hinf2) "Hown2".
    iSplit.
    { iPureIntro. eapply set_infinite_subseteq; try eassumption; set_solver. }
    rewrite fCoPset_op_union // own_op; by iFrame.
  Qed.

  Lemma ownfCP_op_union_split γ q E1 E2 :
    E1 ## E2 →
    ownfCP_inf γ q (E1 ∪ E2) ⊢ ownfCP γ q E1 ∗ ownfCP γ q E2.
  Proof.
    iIntros (Hdisj).
    iDestruct 1 as (Hinf) "H".
    rewrite fCoPset_op_union // own_op; by iFrame.
  Qed.

  Lemma ownfCP_inf_eq γ q E :
    ownfCP_inf γ q E ⊣⊢ ⌜ set_infinite E ⌝ ∧ ownfCP γ q E.
  Proof. auto. Qed.

  Lemma ownfCP_disj γ q1 q2 D E :
    ownfCP γ q1 D ∗ ownfCP_inf γ q2 E -∗ ⌜ E ## D ∨ ✓(q1 + q2)%Qp ⌝.
  Proof.
    iIntros "(H1&(%&H2))".
    iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hval.
    iPureIntro.
    rewrite frac_valid.
    destruct (decide ((1 < q1 + q2))%Qp) as [Hlt|Hnlt].
    - left. apply fCoPset_valid_op1 in Hval as (?&?); auto; set_solver.
    - right. apply Qp_le_ngt; auto.
  Qed.

End frac_coPset_prop.
