From Perennial.goose_lang.lib Require Import encoding crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import twophase.typed_translate twophase.wrapper_proof twophase.twophase_refinement_defs twophase.twophase_sub_logical_reln_defs.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang Require Import logical_reln_defns logical_reln_adeq spec_assert metatheory.
From Perennial.program_logic Require Import ghost_var.

From Goose Require github_com.mit_pdos.goose_nfsd.txn.

Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp jrnl_spec_interp_adequacy.

Section refinement.
Context {PARAMS : jrnlInit_params}.
Context (N : namespace).

Notation jrnl_nat_K :=
(leibnizO (nat * ((@spec_lang jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics).(language.expr)
                           → (@spec_lang jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics).(language.expr)))).

Lemma jrnl_init_obligation1: sty_init_obligation1 jrnlTy_update_model jrnl_initP.
Proof.
  rewrite /sty_init_obligation1//=.
  iIntros (? hG hRG hJrnl σs σi Hinit) "Hdisk".
  rewrite /jrnl_start /jrnl_init/jrnl_init.
  inversion Hinit as [Hnn [Heqi Heqs]]. rewrite Heqs Heqi.
  iIntros "(Hclosed_frag&Hjrnl_frag)".
  eauto.
Qed.

Lemma jrnl_init_obligation2: sty_init_obligation2 jrnl_initP.
Proof.
  intros ?? (?&?&?). rewrite //=. split_and!; eauto. eexists; split; eauto.
  admit.
Admitted.

Lemma jrnl_rules_obligation:
  @sty_rules_obligation _ _ disk_semantics _ _ _ _ _ _ jrnlTy_model jrnl_trans.
Proof.
  intros vs0 vs v0 v0' t1 t2 Htype0 Htrans.
  inversion Htype0 as [op Heq]; subst.
  - iIntros (????) "#Hinv #Hspec #Hval".
    iIntros (j K Hctx) "Hj".
    admit.
Admitted.

Lemma jrnl_crash_inv_obligation:
  @sty_crash_inv_obligation _ _ disk_semantics _ _ _ _ _ _ jrnlTy_model.
Proof.
  rewrite /sty_crash_inv_obligation//=.
  iIntros (? hG hRG hJrnl e Φ) "Hinit Hspec Hwand".
  rewrite /jrnl_inv/jrnl_init/jrnl_inv.
Admitted.

Lemma jrnl_crash_obligation:
  @sty_crash_obligation _ _ disk_semantics _ _ _ _ _ _ jrnlTy_model.
Proof.
  rewrite /sty_crash_obligation//=.
  iIntros (? hG hRG hJrnl) "Hinv Hcrash_cond".
Admitted.

Lemma jrnl_inv_twophase_pre `{hBuf: sep_buftxn_invariant.buftxnG Σ} {hG: heapG Σ} {hRG: refinement_heapG Σ}
      {hJrnl : twophase_refinement_defs.jrnlG Σ} vs v:
    jrnl_inv -∗
    val_interp (smodel := jrnlTy_model) (hS := hJrnl) (@extT jrnl_val_ty JrnlT) vs v -∗
    ∃ (l : loc) γ γ' objs_dom dinit, ⌜ v = #l ⌝ ∗ is_twophase_pre N l γ γ' dinit objs_dom.
  Admitted.

Ltac unfold_expr_vars :=
    match goal with
    | [ H : _ ∉ expr_vars _ |- _ ] => rewrite /expr_vars -/expr_vars in H
    | [ H : _ ∉ val_vars _ |- _ ] => rewrite /val_vars -/val_vars in H
    end.

Lemma atomic_body_expr_subst :
  ∀ Γ x e e' t v,
    x ∉ dom (gset string) Γ →
    x ∉ expr_vars e →
    atomic_body_expr_transTy Γ (Var x) e e' t →
    atomic_body_expr_transTy Γ (of_val v) e (subst x v e') t.
Proof.
  intros ?????? Hnot_in1 Hnot_in2 Htyping.
  remember (Var x) as tph' eqn:Heq. revert Hnot_in1 Hnot_in2. revert Heq.
  induction Htyping using @expr_typing_ind with
      (P := (λ Γ tph' es e t
               (HTYPE: atomic_body_expr_transTy Γ tph' es e t),
             tph' = Var x →
             x ∉ dom (gset string) Γ →
             x ∉ expr_vars es →
             atomic_body_expr_transTy Γ (of_val v) es (subst x v e) t))
      (P0 := (λ Γ tph' vs vi t
              (HTYPE: atomic_body_val_transTy Γ tph' vs vi t),
              tph' = Var x →
              x ∉ dom (gset string) Γ →
              x ∉ val_vars vs →
              atomic_body_val_transTy Γ (of_val v) vs vi t));
    try (intros; subst; simpl; econstructor; eauto; done);
    try (intros; subst; simpl;
         econstructor; eauto;
         [ eapply IHHtyping1; eauto; unfold_expr_vars; set_solver |
           eapply IHHtyping2; eauto; unfold_expr_vars; set_solver ]; done);
    try (intros; subst; simpl;
         econstructor; eauto;
         [ eapply IHHtyping1; eauto; unfold_expr_vars; set_solver |
           eapply IHHtyping2; eauto; unfold_expr_vars; set_solver |
           eapply IHHtyping3; eauto; unfold_expr_vars; set_solver ]; done).
  - intros. subst. simpl.
    destruct (decide _).
    * subst; try econstructor; eauto.
      exfalso. eapply H1. set_solver.
    * econstructor. eauto.
  - intros; subst; simpl.
    econstructor; eauto.
    rewrite decide_True.
    { eapply IHHtyping; eauto; rewrite /expr_vars -/expr_vars //= in H1; destruct f; destruct x0 => //=;
      rewrite //= in H1; rewrite /insert/ctx_insert ?dom_insert; set_solver. }
    { rewrite /expr_vars -/expr_vars //= in H1. destruct f, x0; set_solver. }
  - intros; subst; simpl.
    rewrite decide_True //.
    econstructor.
    * eapply IHHtyping1; eauto; unfold_expr_vars; set_solver.
    * eapply IHHtyping2; eauto; unfold_expr_vars; set_solver.
  - intros; subst; simpl.
    rewrite decide_True //.
    econstructor.
    * eapply IHHtyping1; eauto; unfold_expr_vars; set_solver.
    * eapply IHHtyping2; eauto; unfold_expr_vars; set_solver.
  - intros; subst; simpl.
    econstructor.
    * eapply IHHtyping; eauto. unfold_expr_vars; set_solver.
    * eapply IHHtyping0; eauto; unfold_expr_vars; set_solver.
  - intros; subst; simpl.
    econstructor.
    * eapply IHHtyping; eauto. unfold_expr_vars; set_solver.
    * eapply IHHtyping0; eauto; unfold_expr_vars; set_solver.
Qed.

Lemma jrnl_atomic_obligation:
  @sty_atomic_obligation _ _ disk_semantics _ _ _ _ _ _ jrnlTy_model jrnl_atomic_transTy.
Proof.
  rewrite /sty_atomic_obligation//=.
  iIntros (? hG hRG hJrnl el1 el2 tl e1 e2 t Γsubst Htrans) "Hinv Hspec Htrace HΓ HhasTy".
  iIntros (j K Hctx) "Hj".
  inversion Htrans; subst.
  simpl.
  rewrite lookup_delete.
  rewrite -fmap_delete.
  rewrite ?delete_notin; last first.
  { apply not_elem_of_dom. erewrite <-dom_fmap. eauto. }

  wpc_bind (subst_map _ el2).
  spec_bind (subst_map _ el1) as Hctx.
  iDestruct ("HhasTy" with "[//] Hj") as "H".
  rewrite /sty_lvl_ops/=.
  iApply (wpc_strong_mono with "H"); auto.
  iSplit; last by (iModIntro; eauto).
  iIntros (v) "Hv". iModIntro.
  wpc_bind (op_wrappers.TwoPhase__Begin' v).
  iApply wp_wpc.
  iDestruct "Hv" as (vs) "(Hj&Hinterp)".
  iDestruct (jrnl_inv_twophase_pre with "[$] [$]") as "H".
  iDestruct "H" as (l γ γ' ?? ->) "H".
  wp_apply (wp_TwoPhase__Begin' with "[$]").
  iIntros (tph_val) "Hstarted".
  iApply wp_wpc.
  wp_pures.
  rewrite decide_True //.
  wp_pures.
  apply (atomic_body_expr_subst _ _ _ _ _ #tph_val) in H2; swap 1 3.
  { eauto. }
  { intros Hin. eapply H0. rewrite elem_of_dom in Hin *.
    intros (v&?). apply: elem_of_dom_2. eapply H; eauto. }
  wp_bind (subst _ _ _).
  rewrite subst_map_subst_comm //; last first.
  { rewrite dom_fmap. rewrite dom_fmap in H0 *. eauto. }
  (* Apply the fundamental lemma here *)
Admitted.

Existing Instances jrnl_semantics.
Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field spec_ffi_interp_field spec_ffi_interp_adequacy_field.
(* XXX: might need to change typed_translate / refinement to use the spec_ wrappers around type classes *)

Lemma jrnl_refinement (es: @expr jrnl_op) σs e σ (τ: @ty jrnl_ty.(@val_tys jrnl_op)):
  typed_translate.expr_transTy _ _ _ jrnl_trans jrnl_atomic_transTy ∅ es e τ →
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  jrnl_initP σ σs →
  refinement.trace_refines e e σ es es σs.
Proof.
  intros. intros ?.
  efeed pose proof sty_adequacy; eauto using jrnl_init_obligation1, jrnl_init_obligation2,
                                 jrnl_crash_inv_obligation, jrnl_crash_obligation,
                                 jrnl_rules_obligation, jrnl_atomic_obligation.
Qed.
End refinement.
