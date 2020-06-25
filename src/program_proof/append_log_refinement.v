From Perennial.goose_lang.examples Require Import append_log.
From Perennial.goose_lang.lib Require Import encoding crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import append_log_hocap.
From Perennial.program_proof Require Import append_log_refinement_triples.
From Perennial.goose_lang.ffi Require Import append_log_ffi.
From Perennial.goose_lang Require Import logical_reln_defns logical_reln_adeq spec_assert.
From Perennial.program_logic Require Import ghost_var.

Existing Instances log_spec_ext log_spec_ffi_model log_spec_ext_semantics log_spec_ffi_interp log_spec_interp_adequacy.

Section refinement.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!refinement_heapG Σ}.
Context `{stagedG Σ}.

Existing Instance logG0.
Context `{Hin: inG Σ (authR (optionUR (exclR log_stateO)))}.
Context `{Hin_nat_ctx: inG Σ (authR (optionUR (exclR (leibnizO (nat * (spec_lang.(language.expr) →
                                                                       spec_lang.(language.expr)))))))}.
Context (SIZE: nat).
Context (SIZE_nonzero: 0 < SIZE).
Context (SIZE_bounds: int.nat SIZE = SIZE).

Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field (* spec_ffi_interp_field  *) spec_ffi_interp_adequacy_field.

Notation sstate := (@state (@spec_ext_op_field log_spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ext_op_field log_spec_ext)).
Notation sval := (@val (@spec_ext_op_field log_spec_ext)).

Class appendG (Σ: gFunctors) :=
  { append_stagedG :> stagedG Σ;
    append_stateG :> inG Σ (authR (optionUR (exclR log_stateO)));
    append_nat_ctx :> inG Σ (authR (optionUR (exclR (leibnizO (nat * (spec_lang.(language.expr) →
                                                                       spec_lang.(language.expr)))))))
  }.

Definition append_names := unit.
Definition append_get_names (Σ: gFunctors) (hG: appendG Σ) := tt.
Definition append_update (Σ: gFunctors) (hG: appendG Σ) (n: append_names) := hG.

Definition LVL_INIT : nat := 100.
Definition LVL_INV : nat := 75.
Definition LVL_OPS : nat := 50.
Existing Instance logG0.

Definition append_inv {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {cG: crashG Σ} {aG : appendG Σ} :=
  (∃ γ, log_inv SIZE γ LVL_INV%nat)%I.
Definition append_init {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {cG: crashG Σ} {aG : appendG Σ}
  : iProp Σ := (∃ γ, log_init (P γ) SIZE).
Definition append_crash_cond {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {cG: crashG Σ} {aG : appendG Σ}
  : iProp Σ := (∃ γ, log_crash_cond (P γ) SIZE).
Definition appendN : coPset := (∅ : coPset).
Definition append_val_interp {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {cG: crashG Σ} {aG : appendG Σ}
           (ty: @ext_tys (@val_tys _ log_ty)) : val_semTy :=
  λ vspec vimpl, (∃ (lspec: loc) (limpl: loc) γ,
            ⌜ vspec = #lspec ∧ vimpl = #limpl ⌝ ∗ is_log SIZE γ LVL_INV limpl ∗ log_open lspec)%I.

Instance appendTy_model : specTy_model log_ty.
Proof using SIZE.
 refine
  {| styG := appendG;
     sty_names := append_names;
     sty_get_names := append_get_names;
     sty_update := append_update;
     sty_inv := @append_inv;
     sty_init := @append_init;
     sty_crash_cond := @append_crash_cond;
     styN := appendN;
     sty_lvl_init := LVL (LVL_INIT);
     sty_lvl_ops := LVL (LVL_OPS);
     sty_val_interp := @append_val_interp |}.
 - intros ? [] [] => //=.
 - intros ? [] => //=.
 - intros ?? [] [] => //=.
 - rewrite /sN/appendN. apply disjoint_empty_r.
 - abstract (intros; iIntros "H"; iDestruct "H" as (??? (->&->)) "H" => //=).
Defined.
(* XXX: some of the fields should be opaque/abstract here, because they're enormous proof terms.
  perhaps specTy_model should be split into two typeclasses? *)

Existing Instances subG_stagedG.

Definition appendΣ := #[stagedΣ;
                          GFunctor (authR (optionUR (exclR log_stateO)));
                          GFunctor ((authR (optionUR (exclR (leibnizO (nat * (spec_lang.(language.expr) →
                                                                       spec_lang.(language.expr))))))))].

Instance subG_appendPreG: ∀ Σ, subG appendΣ Σ → appendG Σ.
Proof. solve_inG. Qed.
Definition append_initP (σimpl: @state disk_op disk_model) (σspec : @state log_op log_model) : Prop :=
  (null_non_alloc σspec.(heap)) ∧
  (σimpl.(world) = init_disk ∅ SIZE) ∧
  (σspec.(world) = UnInit).
Definition append_update_pre (Σ: gFunctors) (hG: appendG Σ) (n: append_names) : appendG Σ := hG.

Program Instance appendTy_update_model : specTy_update appendTy_model :=
  {| sty_preG := appendG;
            styΣ := appendΣ;
            subG_styPreG := subG_appendPreG;
            sty_update_pre := @append_update_pre |}.
Next Obligation. rewrite //=. Qed.
Next Obligation. rewrite //=. intros ?? [] => //=. Qed.

Notation append_nat_K :=
(leibnizO (nat * ((@spec_lang log_spec_ext log_spec_ffi_model log_spec_ext_semantics).(language.expr)
                           → (@spec_lang log_spec_ext log_spec_ffi_model log_spec_ext_semantics).(language.expr)))).

Lemma append_init_obligation1: sty_init_obligation1 appendTy_update_model append_initP.
Proof.
  rewrite /sty_init_obligation1//=.
  iIntros (? hG hRG hC hAppend σs σi Hinit) "Hdisk".
  rewrite /log_start /append_init/log_init.
  inversion Hinit as [Hnn [Heqi Heqs]]. rewrite Heqs Heqi.
  iIntros "(Huninit_frag&Hlog_frag)". rewrite /P//=.
  rewrite /thread_tok_full.
  iMod (ghost_var_alloc ((O, id) : append_nat_K)) as (γ) "Hown".
  iModIntro. iExists tt, γ. iLeft. iFrame.
  rewrite /append_log_proof.uninit_log.
  iExists _.
  iSplitL "Hdisk".
  - by iApply disk_array_init_disk.
  - rewrite replicate_length //=.
Qed.

Lemma append_init_obligation2: sty_init_obligation2 append_initP.
Proof. intros ?? (?&?&?). rewrite //=. Qed.

Definition append_op_trans (op: log_spec_ext.(@spec_ext_op_field).(@external)) : @val disk_op :=
  match op with
  | AppendOp => Log__Append
  | GetOp => Log__Get
  | ResetOp => Log__Reset
  | InitOp => (λ:<>, Init #SIZE)%V
  | OpenOp => Open
  end.

Inductive append_trans : @val log_op -> @val disk_op -> Prop :=
| AppendTrans (x: string) op:
    append_trans (λ: x, ExternalOp op (Var x)) (append_op_trans op).


Lemma append_rules_obligation:
  @sty_rules_obligation _ _ disk_semantics _ _ _ _ _ _ appendTy_model append_trans.
Proof.
  intros vs0 vs v0 v0' t1 t2 Htype0 Htrans.
  inversion Htype0 as [op Heq Htype]; subst.
  destruct op; inversion Htype; inversion Htrans; subst.
  - admit.
  - admit.
  - iIntros (?????) "#Hinv #Hspec #Hval".
    iIntros (j K Hctx).
    rewrite //=.
    iIntros "Hj".
    rewrite /append_val_interp. iDestruct "Hval" as (lspec limpl γ Heq) "(His_log&Hlog_open)".
    destruct Heq as (->&->). iDestruct "Hinv" as (?) "Hinv".
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)".
    }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. econstructor; eauto. }
    rewrite /LVL_OPS.
    wpc_apply (@wpc_Log__Reset with "[$] []").
    { eauto. }
    { rewrite /LVL_INV. lia. }
    iSplit; first done. iNext. iIntros. iExists _. eauto.
  - inversion Htype; subst.
    iIntros (?????) "#Hinv #Hspec #Hval".
    iIntros (j K Hctx).
    rewrite //=.
    iIntros "Hj".
    rewrite /append_val_interp.
    iDestruct "Hval" as %[-> ->]. iDestruct "Hinv" as (?) "Hinv".
    wpc_pures; first done.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)".
    }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. econstructor; eauto. }
    wpc_apply (@wpc_Init with "[$] []").
    { eauto. }
    { eauto. }
    { rewrite /LVL_INV. lia. }
    iSplit; first done. iNext. iIntros (?) "(#His_log&Hj)".
    iDestruct "Hj" as (?) "(Hj&Hopen)".
    iExists _. iFrame.
    iExists _, _, _, _. iSplit.
    { iPureIntro; split; eauto. }
    iSplitR ""; eauto.
    iExists _, _, _. eauto.
  - inversion Htype; subst.
    iIntros (?????) "#Hinv #Hspec #Hval".
    iIntros (j K Hctx).
    rewrite //=.
    iIntros "Hj".
    rewrite /append_val_interp.
    iDestruct "Hval" as %[-> ->]. iDestruct "Hinv" as (?) "Hinv".
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)".
    }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. econstructor; eauto. }
    wpc_apply (@wpc_Open with "[$] []").
    { eauto. }
    { rewrite /LVL_INV. lia. }
    iSplit; first done. iNext. iIntros (?) "(#His_log&Hj)".
    iDestruct "Hj" as (?) "(Hj&Hopen)".
    iExists _. iFrame.
    iExists _, _, _. iSplit.
    { iPureIntro; split; eauto. }
    iFrame. iFrame "#".
Admitted.

Lemma append_crash_inv_obligation:
  @sty_crash_inv_obligation _ _ disk_semantics _ _ _ _ _ _ appendTy_model.
Proof using SIZE.
  clear SIZE_bounds.
  rewrite /sty_crash_inv_obligation//=.
  iIntros (? hG hC hRG hAppend e Φ) "Hinit Hspec Hwand".
  rewrite /append_inv/append_init/log_inv.
  iDestruct ("Hinit") as (γ) "Hinit".
  rewrite /append_crash_cond.
  iPoseProof (append_log_na_crash_inv_obligation Nlog _ POpened (PStartedOpening _)
                                                 _ _ _ _ _ _ LVL_INIT
                                                 LVL_INV LVL_OPS with "Hinit [Hwand]") as ">(Hinv&Hwp)".
  { rewrite /LVL_INIT/LVL_INV. lia. }
  { rewrite /LVL_INIT/LVL_OPS. lia. }
  { iIntros "Hinv". iApply "Hwand". iExists _. eauto. }
  iModIntro. iSplitL "Hinv".
  { iExists _. iApply "Hinv". }
  iApply (wpc_mono with "Hwp"); eauto.
  iIntros "(_&H)". iExists _. iFrame.
Qed.

Lemma append_crash_obligation:
  @sty_crash_obligation _ _ disk_semantics _ _ _ _ _ _ appendTy_model.
Proof using SIZE.
  clear SIZE_bounds.
  rewrite /sty_crash_obligation//=.
  iIntros (? hG hC hRG hAppend) "Hinv Hcrash_cond".
  iMod (ghost_var_alloc ((O, id) : append_nat_K)) as (γtok) "Hown".
  iDestruct "Hinv" as (γ1) "#Hlog_inv".
  rewrite /append_crash_cond.
  iDestruct "Hcrash_cond" as (γ2 ls) "(Hstate_to_crash&HP)".
  rewrite/ log_state_to_crash.
  iModIntro. iNext. iIntros (hG').
  iModIntro. iIntros (hC' σs Hrel).
  destruct Hrel as (?&?&_&Heq&_).
  iIntros "Hctx".
  rewrite /append_init/log_init.
  destruct (σs.(world)) eqn:Hworld_case; try iDestruct "Hctx" as %[].
  - iAssert (⌜ ls = UnInit ∨ ls = Initing ⌝ ∗ log_ctx UnInit ∗ log_frag [])%I with "[HP Hctx]" as (Heqls) "(Hctx&Hfrag)".
    {
      rewrite /log_ctx/P.
      iDestruct "Hctx" as "(?&?)".
      destruct ls; try (iDestruct "HP" as "(?&?&?)" || iDestruct "HP" as "(?&?)");
        try (iFrame; eauto; done).
      - iDestruct (log_uninit_auth_closed_frag with "[$] [$]") as %[].
      - iDestruct (log_uninit_auth_closed_frag with "[$] [$]") as %[].
      - iDestruct "HP" as (?) "(HP&?)".
        iDestruct (log_uninit_auth_opened with "[$] [$]") as %[].
    }
    iExists _. unshelve (iExists _).
    { econstructor.
      { symmetry; eauto. }
      repeat econstructor.
    }
    iFrame. iIntros (hRG' (Heq1&Heq2)) "Hrestart".
    iModIntro.
    iExists tt, γtok. iLeft.
    rewrite /logG0//=/log_frag//=. rewrite Heq2. rewrite Heq1.
    iFrame. subst.
    rewrite /append_log_proof.uninit_log.
    rewrite /disk_array. rewrite /diskG0.
    rewrite Heq.
    destruct Heqls as [-> | ->]; iFrame.
  - rewrite /P/log_ctx.
    iAssert (⌜ ls = Closed s ∨ ls = Opening s  ⌝ ∗
             log_ctx (Closed s) ∗ log_frag s)%I with "[HP Hctx]" as (Heqls) "(Hctx&Hfrag)".
    {
      rewrite /log_ctx/P.
      iDestruct "Hctx" as "(?&?)".
      destruct ls; try (iDestruct "HP" as "(?&?&?)" || iDestruct "HP" as "(?&?)");
        try (iFrame; eauto; done).
      - iDestruct (log_closed_auth_uninit_frag with "[$] [$]") as %[].
      - iDestruct (log_closed_auth_uninit_frag with "[$] [$]") as %[].
      - iDestruct (log_auth_frag_unif with "[$] [$]") as %->. iFrame. eauto.
      - iDestruct (log_auth_frag_unif with "[$] [$]") as %->. iFrame. eauto.
      - iDestruct "HP" as (?) "(HP&?)".
        iDestruct (log_closed_auth_opened with "[$] [$]") as %[].
    }
    iExists _. unshelve (iExists _).
    { econstructor.
      { symmetry; eauto. }
      simpl.
      repeat econstructor.
    }
    iFrame. iIntros (hRG' (Heq1&Heq2)) "Hrestart".
    iModIntro.
    iExists tt, γtok. iRight.
    rewrite /logG0//=/log_frag//=. rewrite Heq2. rewrite Heq1.
    iFrame. subst.
    rewrite /append_log_proof.uninit_log.
    rewrite /disk_array. rewrite /diskG0.
    destruct Heqls as [-> | ->];
      iExists _; iFrame;
      iFrame; subst;
      (* XXX: need a typeclass? or lemma? to say that these kinds of
         disk assertions are "stable" when we go from hG to hG' because
         disk ffi generation number doesn't change *)
      rewrite /append_log_proof.uninit_log;
      rewrite /append_log_proof.crashed_log;
      rewrite /append_log_proof.is_log';
      rewrite /append_log_proof.is_hdr;
      rewrite /disk_array; rewrite /diskG0;
      rewrite Heq;
      iFrame.
  - rewrite /P/log_ctx.
    iAssert (∃ l0, ⌜ ls = Opened s l0  ⌝ ∗ log_ctx (Opened s l) ∗ log_frag s)%I with "[HP Hctx]" as (? Heqls) "(Hctx&Hfrag)".
    {
      rewrite /log_ctx/P.
      iDestruct "Hctx" as "(?&?)".
      destruct ls; try (iDestruct "HP" as "(?&?&?)" || iDestruct "HP" as "(?&?)");
        try (iFrame; eauto; done).
      - iDestruct (log_uninit_auth_opened with "[$] [$]") as %[].
      - iDestruct (log_uninit_auth_opened with "[$] [$]") as %[].
      - iDestruct (log_closed_auth_opened with "[$] [$]") as %[].
      - iDestruct (log_closed_auth_opened with "[$] [$]") as %[].
      - iDestruct "HP" as (?) "(HP&?)".
        iDestruct (log_auth_frag_unif with "[$] [$]") as %->.
        iDestruct (log_open_unif with "[$] [$]") as %->. iFrame.
        iExists _. iFrame; eauto.
    }
    iExists _. unshelve (iExists _).
    { econstructor.
      { symmetry; eauto. }
      simpl.
      repeat econstructor.
    }
    iFrame. iIntros (hRG' (Heq1&Heq2)) "Hrestart".
    iModIntro.
    iExists tt, γtok. iRight.
    rewrite /logG0//=/log_frag//=. rewrite Heq2. rewrite Heq1.
    iFrame. subst.
    rewrite /append_log_proof.uninit_log.
    rewrite /disk_array. rewrite /diskG0.
      iExists _; iFrame;
      iFrame; subst;
      (* XXX: need a typeclass? or lemma? to say that these kinds of
         disk assertions are "stable" when we go from hG to hG' because
         disk ffi generation number doesn't change *)
      rewrite /append_log_proof.uninit_log;
      rewrite /append_log_proof.crashed_log;
      rewrite /append_log_proof.is_log';
      rewrite /append_log_proof.is_hdr;
      rewrite /disk_array; rewrite /diskG0;
      rewrite Heq;
      iFrame.
Qed.

Existing Instances log_semantics.
Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field spec_ffi_interp_field spec_ffi_interp_adequacy_field.
(* XXX: might need to change typed_translate / refinement to use the spec_ wrappers around type classes *)

Lemma append_refinement (es: @expr log_op) σs e σ (τ: @ty log_ty.(@val_tys log_op)):
  typed_translate.expr_transTy _ _ _ append_trans ∅ es e τ →
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  append_initP σ σs →
  refinement.trace_refines e e σ es es σs.
Proof.
  intros. intros ?.
  efeed pose proof sty_adequacy; eauto using append_init_obligation1, append_init_obligation2,
                                 append_crash_inv_obligation, append_crash_obligation,
                                 append_rules_obligation.
Qed.

End refinement.
