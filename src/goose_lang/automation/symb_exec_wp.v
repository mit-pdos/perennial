From iris.bi Require Export bi telescopes.
From iris.proofmode Require Import tactics notation reduction.
From Perennial.program_logic Require Import weakestpre crash_weakestpre lifting.
From diaframe Require Import util_classes tele_utils solve_defs.
From diaframe.symb_exec Require Import defs.
Import bi.

(* Replacement for diaframe/symb_exec/weakestpre.v for our copy of iris.program_logic.weakestpre *)
(* This file instantiates the symbolic execution interface defined in defs for weakest preconditions *)

Set Universe Polymorphism.
Set Default Proof Using "Type".

Proposition to_tforall {TT : tele} (Ψ : TT → Prop) :
  tforall Ψ → (∀ x, Ψ x).
Proof. apply tforall_forall. Qed.

Unset Universe Polymorphism.

Ltac drop_telescope_tac tele_name intro_pat :=
  revert tele_name; refine (to_tforall _ _); intros intro_pat.

Tactic Notation "drop_telescope" constr(R) "as" simple_intropattern_list(intro_pat) :=
  drop_telescope_tac R intro_pat.


(* useful for pure execution: skips solving a trivial precondition *)
Definition template_I {PROP : bi} n (M : PROP → PROP) {TT : tele} : (TT → PROP) → PROP
  := (λ Q, ▷^n (emp -∗ ∀.. (tt : TT), M $ Q tt))%I.

Global Arguments template_I {_} n M {TT} /.


Section template_I_props.
  Context {PROP : bi}.

  Lemma template_I_strong_mono n TT (M : PROP → PROP) :
    (∀ P Q, (P -∗ Q) -∗ M P -∗ M Q) →
    template_strong_mono (template_I n M (TT := TT)).
  Proof.
    move => HM P Q /=.
    iIntros "HPQ HMP !> _" (tt).
    rewrite left_id bi_tforall_elim.
    iRevert "HMP". by iApply HM.
  Qed.

  Lemma template_I_mono TT n (M : PROP → PROP) :
    ModalityMono M →
    template_mono (template_I n M (TT := TT)).
  Proof.
    move => HM P Q /= HPQ.
    iIntros "HMP !> _" (tt).
    rewrite left_id bi_tforall_elim.
    iApply HM; last done. done.
  Qed.

End template_I_props.


Section wp_executor.

  Context `{!irisGS Λ Σ, !generationGS Λ Σ}.

  Instance wp_execute_op : ExecuteOp (iPropI Σ) (expr Λ) [tele_pair coPset; stuckness; val Λ → iPropI Σ] :=
    λ e, (λᵗ E s Φ, WP e @ s; E {{ Φ }})%I.

  Global Arguments wp_execute_op e !R /.

  Global Instance as_wp_execution e E s Φ : AsExecutionOf (WP e @ s ; E {{ Φ }})%I wp_execute_op e [tele_arg3 E; s; Φ].
  Proof. done. Qed.

  Instance wp_red_cond : ReductionCondition (iPropI Σ) (expr Λ) [tele_pair coPset; stuckness] :=
    (λ A, λᵗ E s, λ e e' M,
      ∀ Φ, M (λ a, WP e' a @ s ; E {{ Φ }}) -∗ WP e @ s ; E {{ Φ }})%I.

  Global Arguments wp_red_cond A !R e e' M /.

  Global Instance wp_red_cond_well_behaved_equiv A : Proper ((=) ==> (=) ==>
      (pointwise_relation _ (=)) ==>
      ((pointwise_relation _ (⊣⊢)) ==> (⊣⊢)) ==> (⊣⊢)) (wp_red_cond A).
  Proof.
    move => w1 w -> {w1} e1 e -> {e1} e'' e' Hee' M1 M2 HM.
    drop_telescope w as E s => /=.
    apply (anti_symm _).
    all: apply forall_mono=> Φ.
    all: rewrite HM // => a.
    all: by rewrite Hee'.
  Qed.

  Global Instance wp_red_cond_well_behaved_ent A : Proper ((=) ==> (=) ==>
      (pointwise_relation _ (=)) ==>
      ((pointwise_relation _ (flip (⊢))) ==> (flip (⊢))) ==> (⊢)) (wp_red_cond A).
  Proof.
    move => w1 w -> {w1} e1 e -> {e1} e'' e' Hee' M1 M2 HM.
    drop_telescope w as E s => /=.
    apply forall_mono=> Φ.
    apply wand_mono => //.
    apply HM => a /=.
    by rewrite Hee'.
  Qed.

  Global Instance wp_red_cond_well_behaved_tne A : Proper ((=) ==> (=) ==>
      (pointwise_relation _ (=)) ==>
      ((pointwise_relation _ (⊢)) ==> (⊢)) ==> (flip (⊢))) (wp_red_cond A).
  Proof.
    move => w1 w -> {w1} e1 e -> {e1} e'' e' Hee' M1 M2 HM.
    drop_telescope w as E s => /=.
    apply forall_mono=> Φ.
    apply wand_mono => //.
    apply HM => a.
    by rewrite Hee'.
  Qed.

  Instance language_ctx_condition : ContextCondition (expr Λ) := λ K, LanguageCtx K.

  Global Instance language_ctx_satisfies K :
    LanguageCtx K →
    SatisfiesContextCondition language_ctx_condition K.
  Proof. auto. Qed.

  Global Arguments language_ctx_condition K /.

  Instance wp_template_condition : TemplateCondition (iPropI Σ) [tele_pair coPset; stuckness; val Λ  → iPropI Σ]
    := (λ A R M R' M', template_mono M ∧ R = R' ∧ M = M').

  Global Arguments wp_template_condition _ _ _ /.

  Global Instance templateM_satisfies_wp_template_condition R n M1 M2 TT1 TT2 Ps Qs :
    ModalityMono M1 →
    ModalityMono M2 →
    SatisfiesTemplateCondition wp_template_condition R (template_M n M1 M2 TT1 TT2 Ps Qs) R (template_M n M1 M2 TT1 TT2 Ps Qs).
  Proof.
    rewrite /SatisfiesTemplateCondition /= => HM1 HM2.
    split => //.
    by apply template_M_is_mono.
  Qed.

  Global Instance wp_execute_reduction_compat :
    ExecuteReductionCompatibility wp_execute_op (λᵗ E s _, [tele_arg3 E; s]) wp_red_cond language_ctx_condition wp_template_condition.
  Proof.
    move => K e A e' M /= HK R R' M' [HM [<- <-]].
    drop_telescope R as E s Φ => /=.
    apply wand_elim_l'.
    rewrite forall_elim /=.
    iIntros "H1 H2".
    iApply wp_bind.
    iApply "H1".
    iApply HM; [ | iAssumption ].
    iIntros (a) "/= HK".
    (* TODO(tej): Perennial does not have [wp_bind_inv], so this lemma is false *)
    (* by apply wp_bind_inv. *)
  Abort.

  Lemma pure_wp_step_exec `(e : expr Λ) φ n e' E s P:
    Inhabited (state Λ) →
    Inhabited (global_state Λ) →
    PureExec φ n e e' →
    ReductionStep (wp_red_cond, [tele_arg3 E; s]) e ⊣ ⟨id⟩ ⌜φ⌝ ; P =[▷^n]=> ⟨id⟩ e' ⊣ emp.
  Proof.
    rewrite /ReductionStep' => HS HGS H1 /=.
    apply forall_intro => Φ.
    apply wand_intro_l.
    rewrite -assoc.
    apply wand_elim_l', pure_elim' => Hφ.
    apply wand_intro_r.
    rewrite !left_id (affine P) right_id /=.
    rewrite -lifting.wp_pure_step_later //.
    apply laterN_mono, wand_mono => //. eauto.
  Qed.

  Lemma pure_wp_step_exec_lc `(e : expr Λ) φ n e' E s P:
    Inhabited (state Λ) →
    Inhabited (global_state Λ) →
    PureExec φ n e e' →
    ReductionStep (wp_red_cond, [tele_arg3 E; s]) e ⊣ ⟨id⟩ ⌜φ⌝ ; P =[▷^n]=> ⟨id⟩ e' ⊣ £ n.
  Proof.
    rewrite /ReductionStep' => HS HGS H1 /=.
    apply forall_intro => Φ.
    apply wand_intro_l.
    rewrite -assoc.
    apply wand_elim_l', pure_elim' => Hφ.
    apply wand_intro_r.
    rewrite !left_id (affine P) right_id /=.
    by rewrite -lifting.wp_pure_step_later.
  Qed.

  Lemma pure_wp_step_exec_lc_fupd `(e : expr Λ) φ n e' E s P:
    Inhabited (state Λ) →
    Inhabited (global_state Λ) →
    PureExec φ n e e' →
    ReductionStep (wp_red_cond, [tele_arg3 E; s]) e ⊣ ⟨fupd E E⟩ ⌜φ⌝ ; P =[▷^n]=> ⟨fupd E E⟩ e' ⊣ £ n.
  Proof.
    rewrite /ReductionStep' => HS HGS H1 /=.
    apply forall_intro => Φ.
    apply wand_intro_l => /=.
    iIntros "[>H1 H2]"; iStopProof.
    rewrite -assoc.
    apply wand_elim_l', pure_elim' => Hφ.
    apply wand_intro_r.
    rewrite !left_id (affine P) right_id /=.
    rewrite -lifting.wp_pure_step_later //.
    apply bi.laterN_mono.
    apply bi.wand_mono; first done.
    by iMod 1.
  Qed.

  Lemma pure_wp_step_exec2 `(e : expr Λ) φ n e' E s P :
    Inhabited (state Λ) →
    Inhabited (global_state Λ) →
    PureExec φ n e e' →
    SolveSepSideCondition φ →
    ReductionTemplateStep wp_red_cond [tele] P [tele_arg3 E; s] e (tele_app (TT := [tele]) e') (template_I n (fupd E E)).
  Proof.
    rewrite /ReductionTemplateStep /SolveSepSideCondition => HS HGS H1 Hφ /=.
    apply forall_intro => Φ.
    apply wand_intro_l.
    rewrite (affine P) right_id.
    rewrite -lifting.wp_pure_step_later //.
    apply bi.laterN_mono, wand_mono, fupd_wp. eauto.
  Qed.

  Global Instance later_forall_satisfies_template_condition n R (TT : tele) M :
    ModalityMono M →
    SatisfiesTemplateCondition wp_template_condition R (template_I n M (TT := TT)) R (template_I n M).
  Proof.
    rewrite /SatisfiesTemplateCondition /=.
    split => //. by apply template_I_mono.
  Qed.

  Proposition as_unit_fun_texan P e v Q s E :
    {{{ P }}} e @ s ; E {{{ RET v; Q }}} →
    {{{ P }}} e @ s ; E {{{ (_ : ()), RET v; Q }}}.
  Proof.
    move => HT Φ.
    iIntros "HP HΦ". iApply (HT with "HP").
    iIntros "!> HQ". by iApply ("HΦ" $! tt).
  Qed.

  Proposition later_if_laterN_if {PROP : bi} (P : PROP) (p : bool) :
    ▷^ (if p then 1 else 0) P ⊣⊢@{PROP} ▷?p P.
  Proof. done. Qed.

  Proposition later_if_sep {PROP : bi} (P Q : PROP) (p : bool) :
    ▷?p (P ∗ Q) ⊣⊢@{PROP} ▷?p P ∗ ▷?p Q.
  Proof. case: p => //=. apply later_sep. Qed.

  Proposition if_bool_as_nat (n : nat) (p : bool) :
    TCOr (TCAnd (TCEq n 1) (TCEq p true)) (TCAnd (TCEq n 0) (TCEq p false)) →
    n = if p then 1 else 0.
  Proof. by case => [[-> ->] | [-> ->]]. Qed.

  (* this is basically sym-ex-fupd-exist, but stated in terms of ReductionStep' *)
  Proposition texan_to_red_cond (A B : tele) n p P e Q (f : A -t> B -t> val Λ) f' s E1 E2 :
    TCOr (TCAnd (TCEq n 1) (TCEq p true)) (TCAnd (TCEq n 0) (TCEq p false)) →
    (∀.. (a : A) (b : B), tele_app (tele_app f' a) b = of_val (tele_app (tele_app f a) b)) →
    TCOr (Atomic StronglyAtomic e) (TCEq E1 E2) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    (∀.. a : A, ∀ Φ,
      tele_app P a -∗ ▷ (∀.. (b : B), tele_app (tele_app Q a) b -∗ Φ (tele_app (tele_app f a) b)) -∗ WP e @ s; E2 {{ Φ } }) →
    ReductionStep' wp_red_cond (ε₀)%I n (fupd E1 E2) (fupd E2 E1) A B P Q e f' [tele_arg3 E1; s].
  Proof.
    rewrite /ReductionStep' => /if_bool_as_nat ->
      /tforall_forall Hf' HeE /tforall_forall HT.
    apply forall_intro => Φ.
    apply wand_intro_r.
    rewrite empty_hyp_first_eq left_id /=.
    (* NOTE: this may be provable starting here following a different strategy;
    we need to not lose WP so quickly since it gives access to
    global_state_interp *)
    match goal with
    | |- (fupd ?E1 ?E2 ?Hp ⊢ wp ?s E1 ?e ?Φ) =>
      enough (Hp ⊢ wp s E2 e (fupd E2 E1 ∘ Φ))
    end.
    - destruct HeE as [He | <-].
      * rewrite -wp_atomic.
        by apply fupd_mono.
      * rewrite -fupd_wp -wp_fupd.
        by apply fupd_mono.
    - apply bi_texist_elim => a.
      rewrite later_if_laterN_if.
      wlog:p /(p = true) => [ | -> /=].
      { case: p; [ move => H; by apply H | (move => <-; last done) => /=; by rewrite -bi.later_intro ]. }
      iIntros "[HP HΦ]".
      iApply (HT with "HP").
      iStopProof. apply later_mono, bi_tforall_mono => b.
      apply wand_mono; first done => /=.
      specialize (Hf' a); apply to_tforall with _ b in Hf'; rewrite Hf' => /=.
      (* TODO: wp_value_fupd is no longer bidirectional *)
      (* by erewrite (wp_value_fupd _ _ Φ); first rewrite fupd_trans //. *)
  Abort.

  (* here is a slightly more readable version: *)
  Proposition sym_ex_fupd_exist (A B : tele) P e Q (f : A -t> B -t> val Λ) s E1 E2 K `{LanguageCtx Λ K} Ψ :
    Atomic StronglyAtomic e ∨ (E1 = E2) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    (∀.. a : A, ∀ Φ,
      tele_app P a -∗ ▷ (∀.. (b : B), tele_app (tele_app Q a) b -∗ Φ (tele_app (tele_app f a) b)) -∗ WP e @ s; E2 {{ Φ } }) →
    (|={E1,E2}=> ∃.. (a : A), tele_app P a ∗ ▷ (∀.. (b : B), tele_app (tele_app Q a) b -∗ |={E2, E1}=> WP (K $ of_val (tele_app (tele_app f a) b)) @ s; E1 {{ Ψ }}))
      ⊢ WP (K e) @ s; E1 {{ Ψ }}.
  Proof.
    move => Hmask He.
    rewrite -wp_bind.
    match goal with
    | |- (fupd ?E1 ?E2 ?Hp ⊢ wp ?s E1 ?e ?Φ) =>
      enough (Hp ⊢ wp s E2 e (fupd E2 E1 ∘ Φ))
    end.
    - destruct Hmask as [Hat | <-].
      * rewrite -wp_atomic.
        by apply fupd_mono.
      * rewrite -fupd_wp -wp_fupd.
        by apply fupd_mono.
    - apply bi_texist_elim => a.
      revert He => /(dep_eval_tele a) HT.
      iIntros "[HP HΦ]". by iApply (HT with "HP").
  Qed.

  Global Instance reduction_step_from e s E Φ :
    ReductionStep (wp_red_cond, [tele_arg3 E; s]) e ⊣ ⟨fupd E E⟩ emp; WP e @ s; E {{ Φ }} =[▷^0]=> ∃ v, ⟨fupd E E⟩ of_val v ⊣ Φ v.
  Proof.
    rewrite /ReductionStep' /ReductionTemplateStep /=.
    apply forall_intro => Ψ.
    apply wand_intro_l.
    eapply entails_po; [ | apply wand_elim_l'; by iApply wp_strong_mono ].
    rewrite sep_comm.
    apply sep_mono_r.
    apply forall_intro => v.
    rewrite (forall_elim v) => /=.
    iIntros "HΦΨ HΦ".
    iMod "HΦΨ" as "[_ HΦΨ]".
    iMod ("HΦΨ" with "HΦ") as "HΨ".
    (* TODO: wp_value_fupd is no longer bidirectional *)
    (* erewrite (wp_value_fupd _ _ Ψ); first rewrite !left_id fupd_trans; last done.
    iIntros "HΦΨ HΦ".
    by iMod ("HΦΨ" with "HΦ") as "H". *)
  Abort.

  Proposition iris_goal_to_red_cond (A B : tele) n P e Q f' s E1 E2 pre (POST : (val Λ → iProp Σ) → A -t> B -t> iProp Σ) :
    TCOr (TCAnd (Atomic StronglyAtomic e) $
                (∃ fv, ∀.. (a : A), ∀.. (b : B), (IntoVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b)))
      )
      (TCEq E1 E2) →
    (∃ fv, (∀.. (a : A), ∀.. (b : B), (IntoVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b))) ∧
          (TCEq POST (λ Φ, tele_map (tele_map Φ) fv))) ∨
          (TCEq POST (λ Φ, tele_map (tele_map (λ fe, WP fe @ s ; E2 {{ Φ }}))%I f')) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    (∀.. a : A, ∀ Φ,
      pre ∗ tele_app P a -∗ ▷^n (∀.. (b : B), tele_app (tele_app Q a) b -∗ (tele_app (tele_app (POST Φ) a) b)) -∗ WP e @ s; E2 {{ Φ } }) →
    ReductionStep' wp_red_cond pre n (fupd E1 E2) (fupd E2 E1) A B P Q e f' [tele_arg3 E1; s].
  Proof.
    rewrite /ReductionStep' => HeE HPOST /tforall_forall HT.
    apply forall_intro => Φ.
    apply wand_intro_r => /=.
    rewrite fupd_frame_l.
    match goal with
    | |- (fupd ?E1 ?E2 ?Hp ⊢ wp ?s E1 ?e ?Φ) =>
      enough (Hp ⊢ wp s E2 e (fupd E2 E1 ∘ Φ))
    end.
    - destruct HeE as [[He1 _] | <-].
      * rewrite -wp_atomic.
        by apply fupd_mono.
      * rewrite -fupd_wp -wp_fupd.
        by apply fupd_mono.
    - apply wand_elim_r', bi_texist_elim => a.
      apply wand_intro_l. rewrite assoc.
      iIntros "[HP HΦ]". iApply (HT with "HP").
      iStopProof.
      apply laterN_mono, bi_tforall_mono => b.
      apply wand_mono => //.
      destruct HeE as [[_ He2] | <-]; last first.
      * rewrite fupd_wp.
        destruct HPOST as [[fv [Hf ->]] | ->].
        + rewrite !tele_map_app /=.
          revert Hf => /(dep_eval_tele a) /(dep_eval_tele b) <-.
          (* wp_value_fupd change *)
          admit.
          (* rewrite wp_value_fupd' //. *)
        + rewrite !tele_map_app /=.
          apply wp_mono => //= v.
          exact: fupd_intro.
      * destruct HPOST as [[fv' [Hf ->]] | ->].
        + revert Hf => /(dep_eval_tele a) /(dep_eval_tele b) <-.
          admit.
          (* rewrite !wp_value_fupd' /= fupd_trans !tele_map_app //=. *)
        + rewrite !tele_map_app /=.
          case: He2 => fv /(dep_eval_tele a) /(dep_eval_tele b) <-.
          admit.
          (* rewrite !wp_value_fupd' => /=.
          rewrite fupd_trans.
          exact: fupd_intro. *)
  Abort.

  Global Instance red_cond_emp_valid_atomic_no_Φ (A B : tele) P e Q f' fv w s E1 E2 pre :
    TCEq (tele_app (TT := [tele_pair coPset; stuckness]) (λ E _, E) w) E1 →
    TCEq (tele_app (TT := [tele_pair coPset; stuckness]) (λ _ s, s) w) s →
    Atomic StronglyAtomic e →
    TCEq (to_val e) None →
    (∀.. (a : A), ∀.. (b : B), (IntoVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b))) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    AsEmpValidWeak
      (ReductionStep' wp_red_cond pre 1 (fupd E1 E2) (fupd E2 E1) A B P Q e f' w)
      ((∀.. a : A,
      pre ∗ tele_app P a -∗ WP e @ s; E2 {{ λ v, ∃.. (b : B), ⌜v = tele_app (tele_app fv a) b⌝ ∗ tele_app (tele_app Q a) b } })) | 10.
  Proof.
    drop_telescope w as E' s' => /= -> ->.
    rewrite /AsEmpValidWeak.
    move => He1 He2 Hfv HPQ.
    (*
    eapply iris_goal_to_red_cond.
    - left. split => //. exists fv. done.
    - left. exists fv. done.
    - apply tforall_forall => a Φ /=.
      iIntros "Hpre Hlater".
      iApply (wp_step_fupd with "[Hlater]"); first done.
      { iIntros "!> !>". iApply "Hlater". } iStopProof.
      revert HPQ.
      rewrite bi_tforall_forall.
      rewrite (bi.forall_elim a) => /wand_entails ->.
      apply wp_mono => v /=.
      iIntros "[%b [-> HQ]] HΦ".
      iSpecialize ("HΦ" $! b).
      rewrite !tele_map_app.
      by iApply "HΦ".
*)
  Abort.

  Global Instance red_cond_emp_valid_value (A B : tele) n P e Q f' fv s E1 pre w :
    TCEq (tele_app (TT := [tele_pair coPset; stuckness]) (λ E _, E) w) E1 →
    TCEq (tele_app (TT := [tele_pair coPset; stuckness]) (λ _ s, s) w) s →
    (∀.. (a : A), ∀.. (b : B), (IntoVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b))) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    AsEmpValidWeak
      (ReductionStep' wp_red_cond pre n (fupd E1 E1) (fupd E1 E1) A B P Q e f' w)
      ((∀.. a : A, ∀ Φ,
      pre ∗ tele_app P a -∗ ▷^n (∀.. (b : B), tele_app (tele_app Q a) b -∗ Φ (tele_app (tele_app fv a) b)) -∗ WP e @ s; E1 {{ Φ } })) | 50.
  Proof.
    drop_telescope w as E' s' => /= -> ->.
    rewrite /AsEmpValidWeak.
    move => Hfv HPQ.
    (*
    eapply iris_goal_to_red_cond.
    - tc_solve.
    - left. exists fv. done.
    - apply tforall_forall => a Φ.
      revert HPQ.
      rewrite bi_tforall_forall.
      rewrite (bi.forall_elim a).
      rewrite (bi.forall_elim Φ) => /wand_entails ->.
      iIntros "HWP HΦ". iApply "HWP". iStopProof.
      by do 2 setoid_rewrite tele_map_app.
     *)
  Abort.

  Lemma red_cond_emp_valid_value_no_Φ (A B : tele) P e Q f' fv s E1 pre :
    (∀.. (a : A), ∀.. (b : B), (IntoVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b))) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    AsEmpValidWeak
      (ReductionStep' wp_red_cond pre 0 (fupd E1 E1) (fupd E1 E1) A B P Q e f' [tele_arg3 E1; s])
      ((∀.. a : A,
      pre ∗ tele_app P a -∗ WP e @ s; E1 {{ λ v, ∃.. (b : B), ⌜v = tele_app (tele_app fv a) b⌝ ∗ tele_app (tele_app Q a) b }})).
  Proof. (* so.. the texan version is stronger, since it allows us to eliminate laters? *)
    rewrite /AsEmpValidWeak.
    move => Hfv HPQ.
    (*
    eapply iris_goal_to_red_cond.
    - tc_solve.
    - left. exists fv. done.
    - apply tforall_forall => a Φ.
      revert HPQ.
      rewrite bi_tforall_forall.
      rewrite (bi.forall_elim a).
      move => /wand_entails -> /=.
      iIntros "HWP HΦ". iApply (wp_wand with "HWP").
      iIntros (v) "[%b [-> HQ]]".
      iSpecialize ("HΦ" with "HQ"). by rewrite !tele_map_app.
*)
  Abort.

  Global Instance red_cond_emp_valid_value_no_Φ_not_value (A B : tele) P e Q f' fv s E1 pre w :
    TCEq (tele_app (TT := [tele_pair coPset; stuckness]) (λ E _, E) w) E1 →
    TCEq (tele_app (TT := [tele_pair coPset; stuckness]) (λ _ s, s) w) s →
    TCEq (to_val e) None →
    (∀.. (a : A), ∀.. (b : B), (IntoVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b))) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    AsEmpValidWeak
      (ReductionStep' wp_red_cond pre 1 (fupd E1 E1) (fupd E1 E1) A B P Q e f' w)
      ((∀.. a : A,
      pre ∗ tele_app P a -∗ WP e @ s; E1 {{ λ v, ∃.. (b : B), ⌜v = tele_app (tele_app fv a) b⌝ ∗ tele_app (tele_app Q a) b }})) | 20.
  Proof. (* so.. the texan version is stronger, since it allows us to eliminate laters? *)
    drop_telescope w as E' s' => /= -> ->.
    rewrite /AsEmpValidWeak.
    move => He Hfv HPQ.
    (*
    eapply iris_goal_to_red_cond.
    - tc_solve.
    - left. exists fv. done.
    - apply tforall_forall => a Φ /=.
      iIntros "Hpre Hlater".
      iApply (wp_step_fupd with "[Hlater]"); first done.
      { iIntros "!> !>". iApply "Hlater". } iStopProof.
      revert HPQ.
      rewrite bi_tforall_forall.
      rewrite (bi.forall_elim a).
      move => /wand_entails ->.
      iApply wp_mono => v /=.
      iIntros "[%b [-> HQ]] HΦ".
      iSpecialize ("HΦ" $! b).
      rewrite !tele_map_app.
      by iApply "HΦ".
*)
  Abort.

  Global Instance red_cond_emp_valid_not_value (A B : tele) n P e Q f' s E1 pre w :
    TCEq (tele_app (TT := [tele_pair coPset; stuckness]) (λ E _, E) w) E1 →
    TCEq (tele_app (TT := [tele_pair coPset; stuckness]) (λ _ s, s) w) s →
    AsEmpValidWeak
      (ReductionStep' wp_red_cond pre n (fupd E1 E1) (fupd E1 E1) A B P Q e f' w)
      ((∀.. a : A, ∀ Φ,
      pre ∗ tele_app P a -∗ ▷^n (∀.. (b : B), tele_app (tele_app Q a) b -∗ WP (tele_app (tele_app f' a) b) @ s ; E1 {{ Φ }}) -∗ WP e @ s; E1 {{ Φ } })) | 25.
  Proof.
    drop_telescope w as E' s' => /= -> ->.
    rewrite /AsEmpValidWeak.
    move => HPQ.
    (*
    eapply iris_goal_to_red_cond.
    - tc_solve.
    - right. tc_solve.
    - apply tforall_forall => a Φ.
      revert HPQ.
      rewrite bi_tforall_forall.
      rewrite (bi.forall_elim a).
      rewrite (bi.forall_elim Φ) => /wand_entails ->.
      do 2 setoid_rewrite tele_map_app.
      by iIntros "$".
*)
  Abort.

End wp_executor.

(* this instance makes iSteps work on goals built by Program, which for some reason unfolds ReductionStep' goals *)
Global Instance template_step_emp_valid {PROP : bi} (pre : PROP) `(red_cond : ReductionCondition PROP E W) e n M1 M2 (A B : tele) P' f'  Q w G :
  AsEmpValidWeak (PROP := PROP) (ReductionStep' red_cond pre n M1 M2 A B P' Q e f' w) G →
  AsEmpValidWeak (PROP := PROP) (ReductionTemplateStep red_cond (A * B) pre w e (λ pr: A * B, tele_app (tele_app f' pr.1) pr.2) (template_M (PROP := PROP) n M1 M2 A B P' Q)) G.
Proof. done. Qed.

Section abducts.
  Context `{!irisGS Λ Σ, !generationGS Λ Σ}.

  Global Instance abduct_from_execution P Q e R K e_in' T e_out' MT MT' R' :
    AsExecutionOf P wp_execute_op e R →
    ReshapeExprAnd (expr Λ) e K e_in' (ReductionTemplateStep wp_red_cond T Q%I ((λᵗ E s _, [tele_arg3 E; s]) R) e_in' e_out' MT) →
    SatisfiesContextCondition language_ctx_condition K →
    SatisfiesTemplateCondition wp_template_condition R MT R' MT' →
    HINT1 Q ✱ [MT' $ flip wp_execute_op R' ∘ K ∘ e_out'] ⊫ [id]; P.
  Proof. intros. eapply execution_abduct_lem => //.
    move => K' e' A e'' M /= HK R'' R''' M' [HM [<- <-]].
    drop_telescope R'' as E s Φ => /=.
    iIntros "[H1 H2]".
    iApply wp_bind.
    iApply "H1".
    iApply HM; [ | done ].
    iIntros (a) "/= H".
    (* same wp_bind_inv issue *)
  Abort.

  Class PerennialSpec E (TT1 TT2 : tele) (P : TT1 -t> iProp Σ) (Q : TT1 -t> TT2 -t> iProp Σ) (e: expr Λ) (v : TT1 -t> TT2 -t> val Λ) :=
    perennial_spec_sound Φ : (∃.. tt1, tele_app P tt1 ∗ (∀.. tt2, tele_app (tele_app Q tt1) tt2 -∗
                                                         Φ (tele_app (tele_app v tt1) tt2)))
                             ⊢ WP e @ E {{ Φ }}.

  Global Instance perennial_lang_apply_spec e E Φ TT1 TT2 P Q v K e_in :
    ReshapeExprAnd (expr Λ) e K e_in (PerennialSpec E TT1 TT2 P Q e_in v) →
    LanguageCtx K →
    HINT1 ε₀ ✱ [ ∃.. tt1 : TT1, tele_app P tt1 ∗
        (∀.. tt2 : TT2, tele_app (tele_app Q tt1) tt2 -∗
                        WP (K $ of_val (tele_app (tele_app v tt1) tt2)) @ E {{ Φ }} ) ] ⊫
      [id]; WP e @ E {{ Φ }}.
  Proof.
    rewrite /PerennialSpec.
    case => -> He_in HK.
    unfold Abduct. simpl.
    iIntros "[_ [%tt1 [HP HQ]]]".
    iApply wp_bind. iApply He_in.
    iExists tt1. iFrame.
  Qed.

  Instance perennial_spec_red E TT1 TT2 P Q e v :
    AsEmpValidWeak
      (PerennialSpec E TT1 TT2 P Q e v)
      (∀ Φ,
         (∀.. tt1, tele_app P tt1 ∗
                     (∀.. tt2, tele_app (tele_app Q tt1) tt2 -∗
                     Φ (tele_app (tele_app v tt1) tt2)) -∗
                   WP e @ E {{ Φ }})).
  Proof.
    move => H.
    rewrite /PerennialSpec.
    iIntros (Φ) "[%tt1 [HP HΦ]]".
    iApply H; iFrame.
  Qed.

  Global Instance perennial_spec_red_no_Φ_not_value E TT1 TT2 P Q e v :
    TCEq (to_val e) None →
    AsEmpValidWeak
      (PerennialSpec E TT1 TT2 P Q e v)
      (∀.. tt1, tele_app P tt1 -∗
                   WP e @ E {{ λ v', ∃.. tt2, ⌜v' = tele_app (tele_app v tt1) tt2⌝ ∗ tele_app (tele_app Q tt1) tt2 }}).
  Proof.
    move => Hnotval H.
    rewrite /PerennialSpec.
    iIntros (Φ) "[%tt1 [HP HΦ]]".
    iDestruct (H with "HP") as "Hwp".
    iApply (wp_strong_mono with "[Hwp]"); [done..|].
    iIntros (v') "[%tt2 [-> HQ]]".
    iModIntro.
    iApply ("HΦ" with "HQ").
  Qed.

  Global Instance collect_modal_wp_value s e v Φ E :
    IntoVal e v →
    HINT1 ε₀ ✱ [fupd E E $ Φ v] ⊫ [id]; WP e @ s ; E {{ Φ }} | 10.
  Proof.
    rewrite /IntoVal /Abduct /= empty_hyp_first_eq left_id => <-.
    iMod 1 as "H".
    iApply wp_value'; auto.
  Qed.

  Global Instance prepend_modal_wp_expr e Φ E s :
    PrependModality (WP e @ s ; E {{ Φ }})%I (fupd E E) (WP e @ s; E {{ Φ }})%I | 20.
  Proof.
    rewrite /PrependModality.
    apply (anti_symm _).
    - by rewrite -{2}fupd_wp.
    - apply fupd_intro.
  Qed.

  (* not exporting these instances, they don't seem to help *)
  #[local] Instance collect_nc_modal_wp_value s e v Φ E :
    IntoVal e v →
    HINT1 ε₀ ✱ [ncfupd E E $ Φ v] ⊫ [id]; WP e @ s ; E {{ Φ }} | 15.
  Proof.
    rewrite /IntoVal /Abduct /= empty_hyp_first_eq left_id => <-.
    iMod 1 as "H".
    iApply wp_value; done.
  Qed.

  #[local] Instance prepend_nc_modal_wp_expr e Φ E s :
    PrependModality (WP e @ s ; E {{ Φ }})%I (ncfupd E E) (WP e @ s; E {{ Φ }})%I | 20.
  Proof.
    rewrite /PrependModality.
    apply (anti_symm _).
    - by rewrite -{2}ncfupd_wp.
    - apply ncfupd_intro.
  Qed.

End abducts.
