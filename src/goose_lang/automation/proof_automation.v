(** * Instantiate Diaframe for GooseLang *)

From diaframe Require Export proofmode_base.
From diaframe.lib Require Import iris_hints.
From diaframe.symb_exec Require Import defs.
From Perennial.goose_lang.automation Require Import symb_exec_wp spec_notation.
From diaframe Require Import steps.pure_solver.
From Perennial.goose_lang Require Export proofmode notation.
From Perennial.goose_lang Require Import struct.struct.

(**
mostly taken from
https://gitlab.mpi-sws.org/iris/diaframe/-/blob/master/diaframe_heap_lang/specs.v

but this tutorial was also helpful initially:
https://gitlab.mpi-sws.org/iris/diaframe/-/blob/master/tutorial/ex5_custom_proof_automation.v
 *)

Set Default Proof Using "Type".

Section wp.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  Global Instance automate_pure_exec n e e' φ Φ :
    PureExec φ n e e' →
    HINT1
      ε₀ ✱
      [⌜φ⌝ ∗ ▷^n (WP e' {{ Φ }})] ⊫
      [id];
      WP e {{ Φ }}.
  Proof.
    iSteps.
    iApply lifting.wp_pure_step_later; first done.
    iSteps.
  Qed.

  Global Instance sym_exec_ref t Φ :
    HINT1 ε₀ ✱
          [⌜has_zero t⌝ ∗ ▷ (∀ (l:loc), l ↦[t] (zero_val t) -∗ Φ #l)]
          ⊫ [id]; WP (ref (zero_val t)) {{ Φ }}.
  Proof.
    iSteps.
    wp_apply wp_ref_of_zero; auto.
  Qed.

End wp.

(* allow any definition to be unfolded (TODO: can we somehow only do this at
the start of the proof?) *)
#[export] Existing Instance AsRecV_recv.

Ltac find_reshape e K e' TC :=
lazymatch e with
| fill ?Kabs ?e_inner =>
  reshape_expr e_inner ltac:(fun K' e'' =>
    unify K (fill Kabs ∘ fill K'); unify e' e'';
    notypeclasses refine (ConstructReshape e (fill Kabs ∘ fill K') e'' _ (eq_refl) _); tc_solve )
| _ =>
  reshape_expr e ltac:(fun K' e'' =>
    unify K (fill K'); unify e' e'';
    notypeclasses refine (ConstructReshape e (fill K') e'' _ (eq_refl) _); tc_solve )
end.

Global Hint Extern 4 (ReshapeExprAnd expr ?e ?K ?e' ?TC) =>
  find_reshape e K e' TC : typeclass_instances.

Global Hint Extern 4 (ReshapeExprAnd (language.expr ?L) ?e ?K ?e' ?TC) =>
  unify L goose_lang;
  find_reshape e K e' TC : typeclass_instances.

Section side_condition_lemmas.
  Context `{ext: ffi_syntax}.

  Lemma val_neq_lit_neq (l1 l2 : base_lit) : l1 ≠ l2 → LitV l1 ≠ LitV l2.
  Proof. move => H [= /H //]. Qed.

  Lemma lit_neq_w64_neq (l1 l2 : w64) : l1 ≠ l2 → LitInt l1 ≠ LitInt l2.
  Proof. move => H [= /H //]. Qed.

  Lemma lit_neq_bool_neq (l1 l2 : bool) : l1 ≠ l2 → LitBool l1 ≠ LitBool l2.
  Proof. move => H [= /H //]. Qed.

  Lemma injr_neq_val_neq (v1 v2 : val) : v1 ≠ v2 → InjRV v1 ≠ InjRV v2.
  Proof. move => H [= /H //]. Qed.

  Lemma injl_neq_val_neq (v1 v2 : val) : v1 ≠ v2 → InjLV v1 ≠ InjLV v2.
  Proof. move => H [= /H //]. Qed.

  Global Instance simplify_lit_val_neq (l1 l2 : base_lit) : SimplifyPureHypSafe (LitV l1 ≠ LitV l2) (l1 ≠ l2).
  Proof. split; first (move => + Hl; by subst). apply val_neq_lit_neq. Qed.

  Global Instance simplify_lit_int_neq (l1 l2 : w64) : SimplifyPureHypSafe (LitInt l1 ≠ LitInt l2) (l1 ≠ l2).
  Proof. split; first (move => + Hl; by subst). apply lit_neq_w64_neq. Qed.

  Global Instance simplify_lit_bool_neq (l1 l2 : bool) : SimplifyPureHypSafe (LitBool l1 ≠ LitBool l2) (l1 ≠ l2).
  Proof. split; first (move => + Hl; by subst). apply lit_neq_bool_neq. Qed.

  Global Instance simplify_injr_neq (l1 l2 : val) : SimplifyPureHypSafe (InjRV l1 ≠ InjRV l2) (l1 ≠ l2).
  Proof. split; first (move => + Hl; by subst). apply injr_neq_val_neq. Qed.

  Global Instance simplify_injl_neq (l1 l2 : val) : SimplifyPureHypSafe (InjLV l1 ≠ InjLV l2) (l1 ≠ l2).
  Proof. split; first (move => + Hl; by subst). apply injl_neq_val_neq. Qed.

  Global Instance simplify_injl_injr_eq (l1 l2 : val) : SimplifyPureHypSafe (InjLV l1 = InjRV l2) False.
  Proof. split => H; last done. inversion H. Qed.

  Global Instance simplify_injl_injl_eq (l1 l2 : val) : SimplifyPureHypSafe (InjRV l1 = InjLV l2) False.
  Proof. split => H; last done. inversion H. Qed.
End side_condition_lemmas.

Ltac solveValEq :=
  (progress f_equal); trySolvePureEq.

Ltac trySolvePureEqAdd1 :=
  lazymatch goal with
  | |- @eq ?T ?l ?r =>
    match constr:((T, l)) with
    | (val, _) => solveValEq
    | (base_lit, _) => solveValEq
    end
  end.

Global Hint Extern 4 (_ = _) => trySolvePureEqAdd1 : solve_pure_eq_add.

Ltac trySolvePureAdd1 :=
  match goal with
  | |- LitV ?v1 ≠ LitV ?v2 =>
    assert_fails (has_evar v1);
    assert_fails (has_evar v2);
    eapply val_neq_lit_neq; solve [pure_solver.trySolvePure]
  | |- LitInt ?v1 ≠ LitInt ?v2 =>
    assert_fails (has_evar v1);
    assert_fails (has_evar v2);
    eapply lit_neq_w64_neq; solve [pure_solver.trySolvePure]
  | |- LitBool ?v1 ≠ LitBool ?v2 =>
    assert_fails (has_evar v1);
    assert_fails (has_evar v2);
    eapply lit_neq_bool_neq; solve [pure_solver.trySolvePure]
  | |- InjRV ?v1 ≠ InjRV ?v2 =>
    assert_fails (has_evar v1);
    assert_fails (has_evar v2);
    eapply injr_neq_val_neq; solve [pure_solver.trySolvePure]
  | |- InjLV ?v1 ≠ InjLV ?v2 =>
    assert_fails (has_evar v1);
    assert_fails (has_evar v2);
    eapply injl_neq_val_neq; solve [pure_solver.trySolvePure]
  | |- vals_compare_safe _ _ => (by left) || (by right)
  end.

Global Hint Extern 4 => trySolvePureAdd1 : solve_pure_add.

(** modeled after
https://gitlab.mpi-sws.org/iris/diaframe/-/blob/master/diaframe_heap_lang/specs.v
*)

Class PureExecNoRec
  `{ffi_sem: ffi_semantics} φ n e1 e2 :=
  is_pure_exec : PureExec (Λ := goose_lang) φ n e1 e2.

(* Diaframe does this, not sure why *)
Unset Universe Polymorphism.

Section goose_lang_instances.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  Open Scope expr_scope.

  Global Instance pure_wp_step_exec_inst1 `(e : expr) φ n e' E s:
    PureExecNoRec φ n e e' → (* TODO: prevent unfolding explicit recs *)
    ReductionTemplateStep wp_red_cond (TeleO*TeleO) (ε₀)%I [tele_arg3 E;s] e
      (λ pr, tele_app (TT := [tele]) (tele_app (TT := [tele]) e' pr.1) pr.2)
      (template_M n id id TeleO TeleO ⌜φ⌝%I emp%I) | 80.
      (* used when φ is an equality on a new evar: this will cause SolveSepSideCondition to fail *)
      (* this is a ReductionTemplateStep: if it were a ReductionStep, the priority of as_template_step would be considered, not that of this instance *)
  Proof.
    intros.
    refine (pure_wp_step_exec _ _ _ _ _ _ _ _ _ _). exact H.
  Qed.

  Global Instance pure_wp_step_exec_inst2 (e : expr) φ n e' E s:
    PureExecNoRec φ n e e' →
    SolveSepSideCondition φ →
    ReductionTemplateStep wp_red_cond [tele] (ε₀)%I [tele_arg3 E; s] e (tele_app (TT := [tele]) e') (template_I n (fupd E E))%I | 8.
  Proof.
    intros. eapply pure_wp_step_exec2 => //.
    - tc_solve.
    - tc_solve.
  Qed.

  Global Instance load_step_wp l E1 E2 s :
    SPEC ⟨E1, E2⟩ v q, {{ ▷ l ↦{q} v }} ! #l @ s {{ RET v; l ↦{q} v }}.
  Proof.
    iSteps as (v q) "Hl".
    iApply (wp_load with "Hl").
    iSteps.
  Qed.

  Global Instance load_type_step_wp l E1 E2 s t :
    SPEC ⟨E1, E2⟩ v q, {{ ▷ l ↦[t]{q} v }} ![t] #l @ s {{ RET v; l ↦[t]{q} v }}.
  Proof.
    (*
    iSteps as (v q) "Hl".
    iApply (wp_load with "Hl").
    iSteps.
    *)
  Abort.

  Global Instance alloc_step_wp e v t s:
    IntoVal e v →
    val_ty v t →
    SPEC {{ True }} ref_to t e @ s {{ l, RET #l; l ↦[t] v }} | 20.
  Proof.
    move => <- Hty.
    iSteps.
    iApply wp_ref_to => //.
    iSteps.
  Qed.

  Global Instance store_step_wp l v' E1 E2 s :
    SPEC ⟨E1, E2⟩ v, {{ ▷ l ↦ v }} #l <- v' @ s {{ RET #(); l ↦ v' }}.
  Proof.
    (* TODO: why does load_step_wp work but not this? *)
    (*
    iSteps as (v) "Hl".
    iApply (wp_store with "Hl").
    iSteps.
*)
  Abort.

  Opaque vals_compare_safe.


  (* There is no PureExec for an If statement with an abstract boolean. We create a reduction step for
      the case where this boolean is a bool_decide. *)

  Global Instance if_step_bool_decide P `{Decision P} e1 e2 E s :
    ReductionStep (wp_red_cond, [tele_arg3 E; s]) if: #(bool_decide P) then e1 else e2 ⊣ ⟨id⟩ emp; ε₀ =[▷^1]=>
      ∃ b : bool, ⟨id⟩ (if b then e1 else e2)%V ⊣ ⌜b = true⌝ ∗ ⌜P⌝ ∨ ⌜b = false⌝ ∗ ⌜¬P⌝| 50.
  Proof.
    (* texan_to_red_cond does not work here, since (if b then e1 else e2) is not a value! *)
    rewrite /ReductionStep' /=.
    apply bi.forall_intro => Φ.
    iIntros "_ [_ H]".
    case_bool_decide; wp_pures => /=.
    - iApply ("H" $! true). eauto.
    - iApply ("H" $! false). eauto.
  Qed.

  Global Instance if_step_bool_decide_neg P `{Decision P} e1 e2 E s :
    ReductionStep (wp_red_cond, [tele_arg3 E; s]) if: #(bool_decide (¬P)) then e1 else e2 ⊣ ⟨id⟩ emp; ε₀ =[▷^1]=>
      ∃ b : bool, ⟨id⟩ (if b then e1 else e2)%V ⊣ ⌜b = true⌝ ∗ ⌜¬P⌝ ∨ ⌜b = false⌝ ∗ ⌜P⌝ | 49.
  Proof.
    rewrite /ReductionStep' /=.
    apply bi.forall_intro => Φ.
    iIntros "_ [_ H]".
    case_bool_decide => /=.
    - wp_pures.
      iApply ("H" $! true). eauto.
    - wp_pures.
      iApply ("H" $! false). eauto.
  Qed.

  Global Instance if_step_negb_bool_decide P `{Decision P} e1 e2 E s :
    ReductionStep (wp_red_cond, [tele_arg3 E; s]) if: #(negb $ bool_decide P) then e1 else e2 ⊣ ⟨id⟩ emp; ε₀ =[▷^1]=>
      ∃ b : bool, ⟨id⟩ (if b then e1 else e2)%V ⊣ ⌜b = true⌝ ∗ ⌜¬P⌝ ∨ ⌜b = false⌝ ∗ ⌜P⌝ | 49.
  Proof.
    rewrite /ReductionStep' /=.
    apply bi.forall_intro => Φ.
    iIntros "_ [_ H]".
    case_bool_decide => /=.
    - wp_pures.
      iApply ("H" $! false). eauto.
    - wp_pures.
      iApply ("H" $! true). eauto.
  Qed.

End goose_lang_instances.
