(** * Instantiate Diaframe for GooseLang *)

From diaframe Require Export proofmode_base.
From diaframe.lib Require Import iris_hints.
From diaframe.symb_exec Require Import defs.
From Perennial.goose_lang.automation Require Export symb_exec_wp spec_notation.
From diaframe Require Import steps.pure_solver.
From Perennial.goose_lang Require Export proofmode notation typed_mem.

From iris_named_props Require Export named_props.

(**
mostly taken from
https://gitlab.mpi-sws.org/iris/diaframe/-/blob/master/diaframe_heap_lang/specs.v

but this tutorial was also helpful initially:
https://gitlab.mpi-sws.org/iris/diaframe/-/blob/master/tutorial/ex5_custom_proof_automation.v
 *)

Set Default Proof Using "Type".

(* allow any definition to be unfolded (TODO: can we somehow only do this at
the start of the proof?) *)
#[export] Existing Instance AsRecV_recv.

(*
Section unfold_functions.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

  (*
  Fixpoint occurs_in (s : string) (body : expr) : bool :=
    match body with
    | Val _ => false
    | Var s' => if decide (s = s') then true else false
    | Rec b x e => if decide (BNamed s ≠ b ∧ BNamed s ≠ x) then occurs_in s e else false
    | App f a => (occurs_in s f) || (occurs_in s a)
    | UnOp _ e => occurs_in s e
    | BinOp _ l r => (occurs_in s l) || (occurs_in s r)
    | If c t e => (occurs_in s c) || (occurs_in s t) || (occurs_in s e)
    | Pair l r => (occurs_in s l) || (occurs_in s r)
    | Fst e => (occurs_in s e)
    | Snd e => (occurs_in s e)
    | InjL e => (occurs_in s e)
    | InjR e => (occurs_in s e)
    | Case c l r => (occurs_in s c) || (occurs_in s l) || (occurs_in s r)
    | Fork e => (occurs_in s e)
    | AllocN n e => (occurs_in s n) || (occurs_in s e)
    | Free e => (occurs_in s e)
    | Load e => (occurs_in s e)
    | Store l e => (occurs_in s l) || (occurs_in s e)
    | CmpXchg l e1 e2 => (occurs_in s l) || (occurs_in s e1) || (occurs_in s e2)
    | Xchg l e1 => (occurs_in s l) || (occurs_in s e1)
    | FAA l n => (occurs_in s l) || (occurs_in s n)
    | NewProph => false
    | Resolve a1 a2 a3 => (occurs_in s a1) || (occurs_in s a2) || (occurs_in s a3)
    end.
*)

  Definition is_recursive_fun (v : val) :=
    false
    (*
    match v with
    | RecV (BNamed f) x e => occurs_in f e
    | _ => false
    end
*)
  .

  Global Instance pure_wp_step_exec_inst_last `(e : expr) φ n e' E s :
    ((∀ f x e, SolveSepSideCondition (is_recursive_fun (RecV f x e) = false) →
                AsRecV (RecV f x e) f x e) →
      PureExec φ n e e') →
    SolveSepSideCondition φ →
    ReductionTemplateStep wp_red_cond [tele] (ε₁)%I [tele_arg3 E; s] e (tele_app (TT := [tele]) e') (template_I n (fupd E E)).
  Proof.
    intros. eapply pure_wp_step_exec2 => //; tc_solve.
  Qed.

End unfold_functions.
*)

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

(*
Class PureExecNoRec
  `{ffi_sem: ffi_semantics} φ n e1 e2 :=
  is_pure_exec : PureExec (Λ := goose_lang) φ n e1 e2.

(* Diaframe does this, not sure why *)
Unset Universe Polymorphism.
*)

Section goose_lang_instances.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  Open Scope expr_scope.

  Global Instance automate_pure_exec n e_out K e e' φ Φ :
    (* Instruct Diaframe how to reduce pure reductions. The evaluation context indirection
      is necessary since [pure_exec_ctx] is not available to direct type class search *)
    ReshapeExprAnd expr e_out K e (PureExec φ n e e') →
    LanguageCtx K →
    HINT1
      ε₀ ✱
    (* The [▷ (emp -∗ R)] pattern ensures Diaframe performs later introduction. If it is
      omitted, Diaframe may end up in goals of the form [|={⊤}=> ▷ R], and it is unclear
      for such goals whether one should introduce the later (and forego access to the [fupd]),
      or use the [fupd] first. Diaframe will therefore halt automation on these goals,
      if it cannot find a way to get [R]. *)
      [⌜φ⌝ ∗ ▷^n (emp -∗ WP K e' {{ Φ }})] ⊫
      [id];
      WP e_out {{ Φ }} | 20.
  (* We give this higher cost than looking for a PerennialSpec, to prevent
    unfolding functions with a known specification *)
  Proof.
    case => -> He HK.
    iSteps.
    iApply lifting.wp_pure_step_later.
    - by apply pure_exec_ctx.
    - done.
    - iSteps.
  Qed.
(*
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
*)

  Global Instance ncfupd_mono E :
    ModalityMono (ncfupd E E).
  Proof.
    move => P Q -> //.
  Qed.

  Global Instance ncfupd_strong_modality E :
    ModalityStrongMono (ncfupd E E).
  Proof.
    split.
    - tc_solve.
    - iIntros (P Q) "[>$ $] //".
  Qed.

  (* There is no PureExec for an If statement with an abstract boolean. We create a reduction step for
      the case where this boolean is a bool_decide. *)
(*
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
*)

End goose_lang_instances.

(*
Global Hint Extern 4 (PureExecNoRec _ _ ?e1 _) =>
  lazymatch e1 with
  | (App (Val ?v1) (Val ?v2)) =>
    assert_fails (assert (∃ f x erec,
      TCAnd (AsRecV v1 f x erec) $
      TCAnd (TCIf (TCEq f BAnon) False TCTrue)
            (SolveSepSideCondition (is_recursive_fun (RecV f x erec) = true))) by (do 3 eexists; tc_solve));
    unfold PureExecNoRec; tc_solve
  | _ => unfold PureExecNoRec; tc_solve
  end : typeclass_instances.
*)

Global Hint Extern 4 (val_ty _ _) => val_ty : solve_pure_add.
