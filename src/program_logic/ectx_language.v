(** An axiomatization of evaluation-context based languages, including a proof
    that this gives rise to a "language" in the Iris sense. *)
From iris.prelude Require Export prelude.
From Perennial.program_logic Require Import language.
From iris.prelude Require Import options.

(** TAKE CARE: When you define an [ectxLanguage] canonical structure for your
language, you need to also define a corresponding [language] canonical
structure. Use the coercion [LanguageOfEctx] as defined in the bottom of this
file for doing that. *)

Section ectx_language_mixin.
  Context {expr val ectx state global_state observation : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).
  Context (head_step : expr → state → global_state → list observation → expr → state → global_state → list expr → Prop).

  Record EctxLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_head_stuck e1 σ1 g1 κ e2 σ2 g2 efs :
      head_step e1 σ1 g1 κ e2 σ2 g2 efs → to_val e1 = None;

    mixin_fill_empty e : fill empty_ectx e = e;
    mixin_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_inj K : Inj (=) (=) (fill K);
    mixin_fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e);
    mixin_fill_val_inv K v v' : is_Some (to_val (fill K (of_val v))) → is_Some (to_val (fill K (of_val v')));

    (** Given a head redex [e1_redex] somewhere in a term, and another
        decomposition of the same term into [fill K' e1'] such that [e1'] is not
        a value, then the head redex context is [e1']'s context [K'] filled with
        another context [K''].  In particular, this implies [e1 = fill K''
        e1_redex] by [fill_inj], i.e., [e1]' contains the head redex.)

        This implies there can be only one head redex, see
        [head_redex_unique]. *)
    mixin_step_by_val K' K_redex e1' e1_redex σ1 g1 κ e2 σ2 g2 efs :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      head_step e1_redex σ1 g1 κ e2 σ2 g2 efs →
      ∃ K'', K_redex = comp_ectx K' K'';

    (** If [fill K e] takes a head step, then either [e] is a value or [K] is
        the empty evaluation context. In other words, if [e] is not a value
        wrapping it in a context does not add new head redex positions. *)
    mixin_head_ctx_step_val K e σ1 g1 κ e2 σ2 g2 efs :
      head_step (fill K e) σ1 g1 κ e2 σ2 g2 efs → is_Some (to_val e) ∨ K = empty_ectx;
  }.
End ectx_language_mixin.

Structure ectxLanguage := EctxLanguage {
  expr : Type;
  val : Type;
  ectx : Type;
  state : Type;
  global_state : Type;
  observation : Type;

  of_val : val → expr;
  to_val : expr → option val;
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  head_step : expr → state → global_state → list observation → expr → state → global_state → list expr → Prop;

  ectx_language_mixin :
    EctxLanguageMixin of_val to_val empty_ectx comp_ectx fill head_step
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments EctxLanguage {_ _ _ _ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments empty_ectx {_}.
Global Arguments comp_ectx {_} _ _.
Global Arguments fill {_} _ _.
Global Arguments head_step {_} _ _ _ _ _ _.

(* From an ectx_language, we can construct a language. *)
Section ectx_language.
  Context {Λ : ectxLanguage}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.

  (* Only project stuff out of the mixin that is not also in language *)
  Lemma val_head_stuck e1 σ1 g1 κ e2 σ2 g2 efs :
    head_step e1 σ1 g1 κ e2 σ2 g2 efs → to_val e1 = None.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply ectx_language_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_val_inv K v v' : is_Some (to_val (fill K (of_val v))) → is_Some (to_val (fill K (of_val v'))).
  Proof. apply ectx_language_mixin. Qed.
  Lemma step_by_val K' K_redex e1' e1_redex σ1 g1 κ e2 σ2 g2 efs :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      head_step e1_redex σ1 g1 κ e2 σ2 g2 efs →
      ∃ K'', K_redex = comp_ectx K' K''.
  Proof. apply ectx_language_mixin. Qed.
  Lemma head_ctx_step_val K e σ1 g1 κ e2 σ2 g2 efs :
    head_step (fill K e) σ1 g1 κ e2 σ2 g2 efs → is_Some (to_val e) ∨ K = empty_ectx.
  Proof. apply ectx_language_mixin. Qed.

  Definition head_reducible (e : expr Λ) (σ : state Λ) (g : global_state Λ) :=
    ∃ κ e' σ' g' efs, head_step e σ g κ e' σ' g' efs.
  Definition head_reducible_no_obs (e : expr Λ) (σ : state Λ) (g : global_state Λ) :=
    ∃ e' σ' g' efs, head_step e σ g [] e' σ' g' efs.
  Definition head_irreducible (e : expr Λ) (σ : state Λ) (g : global_state Λ) :=
    ∀ κ e' σ' g' efs, ¬head_step e σ g κ e' σ' g' efs.
  Definition head_stuck (e : expr Λ) (σ : state Λ) (g : global_state Λ) :=
    to_val e = None ∧ head_irreducible e σ g.

  (* All non-value redexes are at the root.  In other words, all sub-redexes are
     values. *)
  Definition sub_redexes_are_values (e : expr Λ) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

  Inductive prim_step (e1 : expr Λ) (σ1 : state Λ) (g1 : global_state Λ) (κ : list (observation Λ))
      (e2 : expr Λ) (σ2 : state Λ) (g2 : global_state Λ) (efs : list (expr Λ)) : Prop :=
    Ectx_step K e1' e2' :
      e1 = fill K e1' → e2 = fill K e2' →
      head_step e1' σ1 g1 κ e2' σ2 g2 efs → prim_step e1 σ1 g1 κ e2 σ2 g2 efs.

  Lemma Ectx_step' K e1 σ1 g1 κ e2 σ2 g2 efs :
    head_step e1 σ1 g1 κ e2 σ2 g2 efs → prim_step (fill K e1) σ1 g1 κ (fill K e2) σ2 g2 efs.
  Proof. econstructor; eauto. Qed.

  Definition ectx_lang_mixin : LanguageMixin of_val to_val prim_step.
  Proof.
    split.
    - apply ectx_language_mixin.
    - apply ectx_language_mixin.
    - intros ???????? [??? -> -> ?%val_head_stuck].
      apply eq_None_not_Some. by intros ?%fill_val%eq_None_not_Some.
  Qed.

  Canonical Structure ectx_lang : language := Language ectx_lang_mixin.

  Definition head_atomic (a : atomicity) (e : expr Λ) : Prop :=
    ∀ σ g κ e' σ' g' efs,
      head_step e σ g κ e' σ' g' efs →
      if a is WeaklyAtomic then irreducible e' σ' g' else is_Some (to_val e').

  (** * Some lemmas about this language *)
  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma head_reducible_no_obs_reducible e σ g :
    head_reducible_no_obs e σ g → head_reducible e σ g.
  Proof. intros (?&?&?&?&?). eexists. eauto. Qed.
  Lemma not_head_reducible e σ g : ¬head_reducible e σ g ↔ head_irreducible e σ g.
  Proof. unfold head_reducible, head_irreducible. naive_solver. Qed.

  (** The decomposition into head redex and context is unique.

      In all sensible instances, [comp_ectx K' empty_ectx] will be the same as
      [K'], so the conclusion is [K = K' ∧ e = e'], but we do not require a law
      to actually prove that so we cannot use that fact here. *)
  Lemma head_redex_unique K K' e e' σ g :
    fill K e = fill K' e' →
    head_reducible e σ g →
    head_reducible e' σ g →
    K = comp_ectx K' empty_ectx ∧ e = e'.
  Proof.
    intros Heq (κ & e2 & σ2 & g2 & efs & Hred) (κ' & e2' & σ2' & g2' & efs' & Hred').
    edestruct (step_by_val K' K e' e) as [K'' HK];
      [by eauto using val_head_stuck..|].
    subst K. move: Heq. rewrite -fill_comp. intros <-%(inj (fill _)).
    destruct (head_ctx_step_val _ _ _ _ _ _ _ _ _ Hred') as [[]%not_eq_None_Some|HK''].
    { by eapply val_head_stuck. }
    subst K''. rewrite fill_empty. done.
  Qed.

  Lemma head_prim_step e1 σ1 g1 κ e2 σ2 g2 efs :
    head_step e1 σ1 g1 κ e2 σ2 g2 efs → prim_step e1 σ1 g1 κ e2 σ2 g2 efs.
  Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

  Lemma head_step_not_stuck e σ g κ e' σ' g' efs :
    head_step e σ g κ e' σ' g' efs → not_stuck e σ g.
  Proof. rewrite /not_stuck /reducible /=. eauto 10 using head_prim_step. Qed.

  Lemma fill_prim_step K e1 σ1 g1 κ e2 σ2 g2 efs :
    prim_step e1 σ1 g1 κ e2 σ2 g2 efs → prim_step (fill K e1) σ1 g1 κ (fill K e2) σ2 g2 efs.
  Proof.
    destruct 1 as [K' e1' e2' -> ->].
    rewrite !fill_comp. by econstructor.
  Qed.
  Lemma fill_reducible K e σ g : reducible e σ g → reducible (fill K e) σ g.
  Proof.
    intros (κ&e'&σ'&g'&efs&?). exists κ, (fill K e'), σ', g', efs.
    by apply fill_prim_step.
  Qed.
  Lemma fill_reducible_no_obs K e σ g : reducible_no_obs e σ g → reducible_no_obs (fill K e) σ g.
  Proof.
    intros (e'&σ'&g'&efs&?). exists (fill K e'), σ', g', efs.
    by apply fill_prim_step.
  Qed.
  Lemma head_prim_reducible e σ g : head_reducible e σ g → reducible e σ g.
  Proof. intros (κ&e'&σ'&g'&efs&?). eexists κ, e', σ', g', efs. by apply head_prim_step. Qed.
  Lemma head_prim_fill_reducible e K σ g :
    head_reducible e σ g → reducible (fill K e) σ g.
  Proof. intro. by apply fill_reducible, head_prim_reducible. Qed.
  Lemma head_prim_reducible_no_obs e σ g : head_reducible_no_obs e σ g → reducible_no_obs e σ g.
  Proof. intros (e'&σ'&g'&efs&?). eexists e', σ', g', efs. by apply head_prim_step. Qed.
  Lemma head_prim_irreducible e σ g : irreducible e σ g → head_irreducible e σ g.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.
  Lemma head_prim_fill_reducible_no_obs e K σ g :
    head_reducible_no_obs e σ g → reducible_no_obs (fill K e) σ g.
  Proof. intro. by apply fill_reducible_no_obs, head_prim_reducible_no_obs. Qed.

  Lemma prim_head_reducible e σ g :
    reducible e σ g → sub_redexes_are_values e → head_reducible e σ g.
  Proof.
    intros (κ&e'&σ'&g'&efs&[K e1' e2' -> -> Hstep]) ?.
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty /head_reducible; eauto 10.
  Qed.
  Lemma prim_head_irreducible e σ g :
    head_irreducible e σ g → sub_redexes_are_values e → irreducible e σ g.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using prim_head_reducible.
  Qed.

  Lemma head_stuck_stuck e σ g :
    head_stuck e σ g → sub_redexes_are_values e → stuck e σ g.
  Proof.
    intros [] ?. split; first done.
    by apply prim_head_irreducible.
  Qed.

  Lemma ectx_language_atomic a e :
    head_atomic a e → sub_redexes_are_values e → Atomic a e.
  Proof.
    intros Hatomic_step Hatomic_fill σ g κ e' σ' g' efs [K e1' e2' -> -> Hstep].
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty. eapply Hatomic_step. by rewrite fill_empty.
  Qed.

  Lemma head_reducible_prim_step_ctx K e1 σ1 g1 κ e2 σ2 g2 efs :
    head_reducible e1 σ1 g1 →
    prim_step (fill K e1) σ1 g1 κ e2 σ2 g2 efs →
    ∃ e2', e2 = fill K e2' ∧ head_step e1 σ1 g1 κ e2' σ2 g2 efs.
  Proof.
    intros (κ'&e2''&σ2''&g2''&efs''&HhstepK) [K' e1' e2' HKe1 -> Hstep].
    edestruct (step_by_val K) as [K'' ?];
      eauto using val_head_stuck; simplify_eq/=.
    rewrite -fill_comp in HKe1; simplify_eq.
    exists (fill K'' e2'). rewrite fill_comp; split; first done.
    apply head_ctx_step_val in HhstepK as [[v ?]|?]; simplify_eq.
    { apply val_head_stuck in Hstep; simplify_eq. }
    by rewrite !fill_empty.
  Qed.

  Lemma head_reducible_prim_step e1 σ1 g1 κ e2 σ2 g2 efs :
    head_reducible e1 σ1 g1 →
    prim_step e1 σ1 g1 κ e2 σ2 g2 efs →
    head_step e1 σ1 g1 κ e2 σ2 g2 efs.
  Proof.
    intros.
    edestruct (head_reducible_prim_step_ctx empty_ectx) as (?&?&?);
      rewrite ?fill_empty; eauto.
    by simplify_eq; rewrite fill_empty.
  Qed.

  (* Every evaluation context is a context. *)
  Global Instance ectx_lang_ctx K : LanguageCtx (fill K).
  Proof.
    split; simpl.
    - eauto using fill_not_val.
    - eauto using fill_val_inv.
    - intros ???????? [K' e1' e2' Heq1 Heq2 Hstep].
      by exists (comp_ectx K K') e1' e2'; rewrite ?Heq1 ?Heq2 ?fill_comp.
    - intros e1 σ1 g1 κ e2 σ2 g2 efs Hnval [K'' e1'' e2'' Heq1 -> Hstep].
      destruct (step_by_val K K'' e1 e1'' σ1 g1 κ e2'' σ2 g2 efs) as [K' ->]; eauto.
      rewrite -fill_comp in Heq1; apply (inj (fill _)) in Heq1.
      exists (fill K' e2''); rewrite -fill_comp; split; auto.
      econstructor; eauto.
  Qed.

  Record pure_head_step (e1 e2 : expr Λ) := {
    pure_head_step_safe σ1 g1 : head_reducible_no_obs e1 σ1 g1;
    pure_head_step_det σ1 g1 κ e2' σ2 g2 efs :
      head_step e1 σ1 g1 κ e2' σ2 g2 efs → κ = [] ∧ σ2 = σ1 ∧ g2 = g1 ∧ e2' = e2 ∧ efs = []
  }.

  Lemma pure_head_step_pure_step e1 e2 : pure_head_step e1 e2 → pure_step e1 e2.
  Proof.
    intros [Hp1 Hp2]. split.
    - intros σ g. destruct (Hp1 σ g) as (e2' & σ2 & g2 & efs & ?).
      eexists e2', σ2, g2, efs. by apply head_prim_step.
    - intros σ1 g1 κ e2' σ2 g2 efs ?%head_reducible_prim_step; eauto using head_reducible_no_obs_reducible.
  Qed.

  (** This is not an instance because HeapLang's [wp_pure] tactic already takes
      care of handling the evaluation context.  So the instance is redundant.
      If you are defining your own language and your [wp_pure] works
      differently, you might want to specialize this lemma to your language and
      register that as an instance. *)
  Lemma pure_exec_fill K φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (fill K e1) (fill K e2).
  Proof. apply: pure_exec_ctx. Qed.
End ectx_language.

Global Arguments ectx_lang : clear implicits.
Global Arguments Ectx_step {Λ e1 σ1 g1 κ e2 σ2 g2 efs}.
Coercion ectx_lang : ectxLanguage >-> language.

(* This definition makes sure that the fields of the [language] record do not
refer to the projections of the [ectxLanguage] record but to the actual fields
of the [ectxLanguage] record. This is crucial for canonical structure search to
work.

Note that this trick no longer works when we switch to canonical projections
because then the pattern match [let '...] will be desugared into projections. *)
Definition LanguageOfEctx (Λ : ectxLanguage) : language :=
  let '@EctxLanguage E V C St GSt K of_val to_val empty comp fill head mix := Λ in
  @Language E V St GSt K of_val to_val _
    (@ectx_lang_mixin (@EctxLanguage E V C St GSt K of_val to_val empty comp fill head mix)).
