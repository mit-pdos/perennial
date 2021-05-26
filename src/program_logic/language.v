From iris.algebra Require Export ofe.
From iris.prelude Require Import options.

Section language_mixin.
  (** [state] is per-machine state; [global_state] is state shared across machines. *)
  Context {expr val state global_state observation : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  (** We annotate the reduction relation with observations [κ], which we will
     use in the definition of weakest preconditions to predict future
     observations and assert correctness of the predictions. *)
  Context (prim_step : expr → state → global_state → list observation → expr → state → global_state → list expr → Prop).

  Record LanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e g σ κ e' g' σ' efs : prim_step e σ g κ e' σ' g' efs → to_val e = None
  }.
End language_mixin.

Structure language := Language {
  expr : Type;
  val : Type;
  state : Type;
  global_state : Type;
  observation : Type;
  of_val : val → expr;
  to_val : expr → option val;
  prim_step : expr → state → global_state → list observation → expr → state → global_state → list expr → Prop;
  language_mixin : LanguageMixin of_val to_val prim_step
}.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.

Declare Scope val_scope.
Delimit Scope val_scope with V.
Bind Scope val_scope with val.

Global Arguments Language {_ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments prim_step {_} _ _ _ _ _ _.

Canonical Structure stateO Λ := leibnizO (state Λ).
Canonical Structure global_stateO Λ := leibnizO (global_state Λ).
Canonical Structure valO Λ := leibnizO (val Λ).
Canonical Structure exprO Λ := leibnizO (expr Λ).

(** This is the system configuration for a *one-machine execution. *)
Definition cfg (Λ : language) := (list (expr Λ) * (state Λ * global_state Λ))%type.

Class LanguageCtx {Λ : language} (K : expr Λ → expr Λ) := {
  fill_not_val e :
    to_val e = None → to_val (K e) = None;
  fill_val_inv v v' :
    is_Some (to_val (K (of_val v))) → is_Some (to_val (K (of_val v')));
  fill_step e1 σ1 g1 κ e2 σ2 g2 efs :
    prim_step e1 σ1 g1 κ e2 σ2 g2 efs →
    prim_step (K e1) σ1 g1 κ (K e2) σ2 g2 efs;
  fill_step_inv e1' σ1 g1 κ e2 σ2 g2 efs :
    to_val e1' = None → prim_step (K e1') σ1 g1 κ e2 σ2 g2 efs →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 g1 κ e2' σ2 g2 efs
}.


Inductive atomicity := StronglyAtomic | WeaklyAtomic.

Section language.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.


  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. apply language_mixin. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof. apply language_mixin. Qed.
  Lemma val_stuck e σ g κ e' σ' g' efs : prim_step e σ g κ e' σ' g' efs → to_val e = None.
  Proof. apply language_mixin. Qed.

  Global Instance language_ctx_id : LanguageCtx (@id (expr Λ)).
  Proof.
    constructor; try naive_solver.
    intros ?? Hval. rewrite to_of_val //=; eauto.
  Qed.

  Definition reducible (e : expr Λ) (σ : state Λ) (g : global_state Λ) :=
    ∃ κ e' σ' g' efs, prim_step e σ g κ e' σ' g' efs.
  (* Total WP only permits reductions without observations *)
  Definition reducible_no_obs (e : expr Λ) (σ : state Λ) (g : global_state Λ) :=
    ∃ e' σ' g' efs, prim_step e σ g [] e' σ' g' efs.
  Definition irreducible (e : expr Λ) (σ : state Λ) (g : global_state Λ) :=
    ∀ κ e' σ' g' efs, ¬prim_step e σ g κ e' σ' g' efs.
  Definition stuck (e : expr Λ) (σ : state Λ) (g : global_state Λ) :=
    to_val e = None ∧ irreducible e σ g.
  Definition not_stuck (e : expr Λ) (σ : state Λ) (g : global_state Λ) :=
    is_Some (to_val e) ∨ reducible e σ g.

  (* [Atomic WeaklyAtomic]: This (weak) form of atomicity is enough to open
     invariants when WP ensures safety, i.e., programs never can get stuck.  We
     have an example in lambdaRust of an expression that is atomic in this
     sense, but not in the stronger sense defined below, and we have to be able
     to open invariants around that expression.  See `CasStuckS` in
     [lambdaRust](https://gitlab.mpi-sws.org/FP/LambdaRust-coq/blob/master/theories/lang/lang.v).

     [Atomic StronglyAtomic]: To open invariants with a WP that does not ensure
     safety, we need a stronger form of atomicity.  With the above definition,
     in case `e` reduces to a stuck non-value, there is no proof that the
     invariants have been established again. *)
  Class Atomic (a : atomicity) (e : expr Λ) : Prop :=
    atomic σ g e' κ σ' g' efs :
      prim_step e σ g κ e' σ' g' efs →
      if a is WeaklyAtomic then irreducible e' σ' g' else is_Some (to_val e').

  Inductive step (ρ1 : cfg Λ) (κ : list (observation Λ)) (ρ2 : cfg Λ) : Prop :=
    | step_atomic e1 σ1 g1 e2 σ2 g2 efs t1 t2 :
       ρ1 = (t1 ++ e1 :: t2, (σ1, g1)) →
       ρ2 = (t1 ++ e2 :: t2 ++ efs, (σ2, g2)) →
       prim_step e1 σ1 g1 κ e2 σ2 g2 efs →
       step ρ1 κ ρ2.
  Local Hint Constructors step : core.

  Inductive nsteps : nat → cfg Λ → list (observation Λ) → cfg Λ → Prop :=
    | nsteps_refl ρ :
       nsteps 0 ρ [] ρ
    | nsteps_l n ρ1 ρ2 ρ3 κ κs :
       step ρ1 κ ρ2 →
       nsteps n ρ2 κs ρ3 →
       nsteps (S n) ρ1 (κ ++ κs) ρ3.
  Local Hint Constructors nsteps : core.

  Definition erased_step (ρ1 ρ2 : cfg Λ) := ∃ κ, step ρ1 κ ρ2.

  (** [rtc erased_step] and [nsteps] encode the same thing, just packaged
      in a different way. *)
  Lemma erased_steps_nsteps ρ1 ρ2 :
    rtc erased_step ρ1 ρ2 ↔ ∃ n κs, nsteps n ρ1 κs ρ2.
  Proof.
    split.
    - induction 1; firstorder eauto. (* FIXME: [naive_solver eauto] should be able to handle this *)
    - intros (n & κs & Hsteps). unfold erased_step.
      induction Hsteps; eauto using rtc_refl, rtc_l.
  Qed.

  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.

  Lemma not_reducible e σ g : ¬reducible e σ g ↔ irreducible e σ g.
  Proof. unfold reducible, irreducible. naive_solver. Qed.
  Lemma reducible_not_val e σ f : reducible e σ f → to_val e = None.
  Proof. intros (?&?&?&?&?&?); eauto using val_stuck. Qed.
  Lemma reducible_no_obs_reducible e σ g : reducible_no_obs e σ g → reducible e σ g.
  Proof. intros (?&?&?&?&?); eexists; eauto. Qed.
  Lemma val_irreducible e σ g : is_Some (to_val e) → irreducible e σ g.
  Proof. intros [??] ????? ?%val_stuck. by destruct (to_val e). Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.
  Lemma not_not_stuck e σ g : ¬not_stuck e σ g ↔ stuck e σ g.
  Proof.
    rewrite /stuck /not_stuck -not_eq_None_Some -not_reducible.
    destruct (decide (to_val e = None)); naive_solver.
  Qed.

  Lemma strongly_atomic_atomic e a :
    Atomic StronglyAtomic e → Atomic a e.
  Proof. unfold Atomic. destruct a; eauto using val_irreducible. Qed.

  Lemma reducible_fill `{!@LanguageCtx Λ K} e σ g :
    reducible e σ g → reducible (K e) σ g.
  Proof. unfold reducible in *. naive_solver eauto using fill_step. Qed.
  Lemma reducible_fill_inv `{!@LanguageCtx Λ K} e σ g :
    to_val e = None → reducible (K e) σ g → reducible e σ g.
  Proof.
    intros ? (e'&σ'&g'&k&efs&Hstep); unfold reducible.
    apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto 10.
  Qed.
  Lemma reducible_no_obs_fill `{!@LanguageCtx Λ K} e σ g :
    reducible_no_obs e σ g → reducible_no_obs (K e) σ g.
  Proof. unfold reducible_no_obs in *. naive_solver eauto using fill_step. Qed.
  Lemma reducible_no_obs_fill_inv `{!@LanguageCtx Λ K} e σ g :
    to_val e = None → reducible_no_obs (K e) σ g → reducible_no_obs e σ g.
  Proof.
    intros ? (e'&σ'&g'&efs&Hstep); unfold reducible_no_obs.
    apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto 10.
  Qed.
  Lemma irreducible_fill `{!@LanguageCtx Λ K} e σ g :
    to_val e = None → irreducible e σ g → irreducible (K e) σ g.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill_inv. Qed.
  Lemma irreducible_fill_inv `{!@LanguageCtx Λ K} e σ g :
    irreducible (K e) σ g → irreducible e σ g.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed.

  Lemma not_stuck_fill_inv K `{!@LanguageCtx Λ K} e σ g :
    not_stuck (K e) σ g → not_stuck e σ g.
  Proof.
    rewrite /not_stuck -!not_eq_None_Some. intros [?|?].
    - auto using fill_not_val.
    - destruct (decide (to_val e = None)); eauto using reducible_fill_inv.
  Qed.

  Lemma stuck_fill `{!@LanguageCtx Λ K} e σ g :
    stuck e σ g → stuck (K e) σ g.
  Proof. rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. Qed.

  Lemma step_Permutation (t1 t1' t2 : list (expr Λ)) κ σg1 σg2 :
    t1 ≡ₚ t1' → step (t1,σg1) κ (t2,σg2) → ∃ t2', t2 ≡ₚ t2' ∧ step (t1',σg1) κ (t2',σg2).
  Proof.
    intros Ht [e1 σ1' g1' e2 σ2' g2' efs tl tr ?? Hstep]; simplify_eq/=.
    move: Ht; rewrite -Permutation_middle (symmetry_iff (≡ₚ)).
    intros (tl'&tr'&->&Ht)%Permutation_cons_inv_r.
    exists (tl' ++ e2 :: tr' ++ efs); split; [|by econstructor].
    by rewrite -!Permutation_middle !assoc_L Ht.
  Qed.

  Lemma step_insert i t2 σ2 g2 e κ e' σ3 g3 efs :
    t2 !! i = Some e →
    prim_step e σ2 g2 κ e' σ3 g3 efs →
    step (t2, (σ2, g2)) κ (<[i:=e']>t2 ++ efs, (σ3, g3)).
  Proof.
    intros.
    edestruct (elem_of_list_split_length t2) as (t21&t22&?&?);
      first (by eauto using elem_of_list_lookup_2); simplify_eq.
    econstructor; eauto.
    by rewrite insert_app_r_alt // Nat.sub_diag /= -assoc_L.
  Qed.

  Lemma erased_step_Permutation (t1 t1' t2 : list (expr Λ)) σ1 σ2 :
    t1 ≡ₚ t1' → erased_step (t1,σ1) (t2,σ2) → ∃ t2', t2 ≡ₚ t2' ∧ erased_step (t1',σ1) (t2',σ2).
  Proof.
    intros Heq [? Hs]. pose proof (step_Permutation _ _ _ _ _ _ Heq Hs). firstorder.
     (* FIXME: [naive_solver] should be able to handle this *)
  Qed.

  Record pure_step (e1 e2 : expr Λ) := {
    pure_step_safe σ1 g1 : reducible_no_obs e1 σ1 g1;
    pure_step_det σ1 g1 κ e2' σ2 g2 efs :
      prim_step e1 σ1 g1 κ e2' σ2 g2 efs → κ = [] ∧ σ2 = σ1 ∧ g2 = g1 ∧ e2' = e2 ∧ efs = []
  }.

  Notation pure_steps_tp := (Forall2 (rtc pure_step)).

  (* TODO: Exclude the case of [n=0], either here, or in [wp_pure] to avoid it
  succeeding when it did not actually do anything. *)
  Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) :=
    pure_exec : φ → relations.nsteps pure_step n e1 e2.

  Lemma pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 :
    pure_step e1 e2 →
    pure_step (K e1) (K e2).
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible_no_obs in *. naive_solver eauto using fill_step.
    - intros σ1 g1 κ e2' σ2 g2 efs Hpstep.
      destruct (fill_step_inv e1 σ1 g1 κ e2' σ2 g2 efs) as (e2'' & -> & ?); [|exact Hpstep|].
      + destruct (Hred σ1 g1) as (? & ? & ? & ? & ?); eauto using val_stuck.
      + edestruct (Hstep σ1 g1 κ e2'' σ2 g2 efs) as (? & -> & -> & -> & ->); auto.
  Qed.

  Lemma pure_step_nsteps_ctx K `{!@LanguageCtx Λ K} n e1 e2 :
    relations.nsteps pure_step n e1 e2 →
    relations.nsteps pure_step n (K e1) (K e2).
  Proof. eauto using nsteps_congruence, pure_step_ctx. Qed.

  Lemma rtc_pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 :
    rtc pure_step e1 e2 → rtc pure_step (K e1) (K e2).
  Proof. eauto using rtc_congruence, pure_step_ctx. Qed.

  (* We do not make this an instance because it is awfully general. *)
  Lemma pure_exec_ctx K `{!@LanguageCtx Λ K} φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (K e1) (K e2).
  Proof. rewrite /PureExec; eauto using pure_step_nsteps_ctx. Qed.

  (* This is a family of frequent assumptions for PureExec *)
  Class IntoVal (e : expr Λ) (v : val Λ) :=
    into_val : of_val v = e.

  Class AsVal (e : expr Λ) := as_val : ∃ v, of_val v = e.
  (* There is no instance [IntoVal → AsVal] as often one can solve [AsVal] more
  efficiently since no witness has to be computed. *)
  Global Instance as_vals_of_val vs : TCForall AsVal (of_val <$> vs).
  Proof.
    apply TCForall_Forall, Forall_fmap, Forall_true=> v.
    rewrite /AsVal /=; eauto.
  Qed.

  Lemma as_val_is_Some e :
    (∃ v, of_val v = e) → is_Some (to_val e).
  Proof. intros [v <-]. rewrite to_of_val. eauto. Qed.

  Lemma prim_step_not_stuck e σ g κ e' σ' g' efs :
    prim_step e σ g κ e' σ' g' efs → not_stuck e σ g.
  Proof. rewrite /not_stuck /reducible. eauto 10. Qed.

  Lemma rtc_pure_step_val `{!Inhabited (state Λ)} `{!Inhabited (global_state Λ)} v e :
    rtc pure_step (of_val v) e → to_val e = Some v.
  Proof.
    intros ?; rewrite <- to_of_val.
    f_equal; symmetry; eapply rtc_nf; first done.
    intros [e' [Hstep _]].
    destruct (Hstep inhabitant inhabitant) as (?&?&?&?&Hval%val_stuck).
    by rewrite to_of_val in Hval.
  Qed.

  (** Let thread pools [t1] and [t3] be such that each thread in [t1] makes
   (zero or more) pure steps to the corresponding thread in [t3]. Furthermore,
   let [t2] be a thread pool such that [t1] under state [σ1] makes a (single)
   step to thread pool [t2] and state [σ2]. In this situation, either the step
   from [t1] to [t2] corresponds to one of the pure steps between [t1] and [t3],
   or, there is an [i] such that [i]th thread does not participate in the
   pure steps between [t1] and [t3] and [t2] corresponds to taking a step in
   the [i]th thread starting from [t1]. *)
  Lemma erased_step_pure_step_tp t1 σ1 g1 t2 σ2 g2 t3 :
    erased_step (t1, (σ1, g1)) (t2, (σ2, g2)) →
    pure_steps_tp t1 t3 →
    (σ1 = σ2 ∧ pure_steps_tp t2 t3) ∨
    (∃ i e efs e' κ,
      t1 !! i = Some e ∧ t3 !! i = Some e ∧
      t2 = <[i:=e']>t1 ++ efs ∧
      prim_step e σ1 g1 κ e' σ2 g2 efs).
  Proof.
    intros [κ [e σ g e' σ' g' efs t11 t12 ?? Hstep]] Hps; simplify_eq/=.
    apply Forall2_app_inv_l in Hps
      as (t31&?&Hpsteps&(e''&t32&Hps&?&->)%Forall2_cons_inv_l&->).
    destruct Hps as [e|e1 e2 e3 [_ Hprs]].
    - right.
      exists (length t11), e, efs, e', κ; split_and!; last done.
      + by rewrite lookup_app_r // Nat.sub_diag.
      + apply Forall2_length in Hpsteps.
        by rewrite lookup_app_r Hpsteps // Nat.sub_diag.
      + by rewrite insert_app_r_alt // Nat.sub_diag /= -assoc_L.
    - edestruct Hprs as (?&?&?&?&?); first done; simplify_eq.
      left; split; first done.
      rewrite right_id_L.
      eauto using Forall2_app.
  Qed.

End language.

Global Arguments step_atomic {Λ ρ1 κ ρ2}.

Notation pure_steps_tp := (Forall2 (rtc pure_step)).
