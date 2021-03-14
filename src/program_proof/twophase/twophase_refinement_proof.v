From Perennial.goose_lang.lib Require Import encoding crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import twophase.typed_translate twophase.wrapper_proof twophase.twophase_refinement_defs twophase.twophase_sub_logical_reln_defs.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang Require Import logical_reln_defns logical_reln_adeq spec_assert metatheory.
From Perennial.base_logic Require Import ghost_var.
From Perennial.program_proof Require Import lockmap_proof.

From Goose Require github_com.mit_pdos.goose_nfsd.txn.

Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp jrnl_spec_interp_adequacy.

Section refinement.
Context {PARAMS : twophaseInit_params}.
Context (N : namespace).

Notation jrnl_nat_K :=
(leibnizO (nat * ((@spec_lang jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics).(language.expr)
                           → (@spec_lang jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics).(language.expr)))).

Lemma jrnl_init_obligation1: sty_init_obligation1 twophaseTy_update_model twophase_initP.
Proof.
  rewrite /sty_init_obligation1//=.
  iIntros (? hG hRG hJrnl σs σi Hinit) "Hdisk".
  rewrite /jrnl_start /twophase_init.
  inversion Hinit as [Hnn [Heqi Heqs]]. rewrite Heqs Heqi.
  iIntros "(Hclosed_frag&Hjrnl_frag)".
  eauto.
Qed.

Lemma jrnl_init_obligation2: sty_init_obligation2 twophase_initP.
Proof.
  intros ?? (?&?&?). rewrite //=. split_and!; eauto. eexists; split; eauto.
  admit.
Admitted.

Lemma jrnl_rules_obligation:
  @sty_rules_obligation _ _ disk_semantics _ _ _ _ _ _ twophaseTy_model jrnl_trans.
Proof.
  intros vs0 vs v0 v0' t1 t2 Htype0 Htrans.
  inversion Htype0 as [op Heq]; subst.
  - iIntros (????) "#Hinv #Hspec #Hval".
    iIntros (j K Hctx) "Hj".
    admit.
Admitted.

Lemma jrnl_crash_inv_obligation:
  @sty_crash_inv_obligation _ _ disk_semantics _ _ _ _ _ _ twophaseTy_model.
Proof.
  rewrite /sty_crash_inv_obligation//=.
  iIntros (? hG hRG hJrnl e Φ) "Hinit Hspec Hwand".
  rewrite /twophase_init/twophase_inv.
Admitted.

Lemma jrnl_crash_obligation:
  @sty_crash_obligation _ _ disk_semantics _ _ _ _ _ _ twophaseTy_model.
Proof.
  rewrite /sty_crash_obligation//=.
  iIntros (? hG hRG hJrnl) "Hinv Hcrash_cond".
Admitted.

Lemma jrnl_inv_twophase_pre {Σ} {hG: heapG Σ} {hRG: refinement_heapG Σ}
      {hJrnl : twophaseG Σ} vs v:
    twophase_inv -∗
    val_interp (smodel := twophaseTy_model) (hS := hJrnl) (@extT jrnl_val_ty JrnlT) vs v -∗
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

Definition subst_tuple_conv (x : (@subst_tuple disk_op (jrnl_spec_ext) jrnl_ty)) :
                               twophase_sub_logical_reln_defs.subst_tuple :=
  {| twophase_sub_logical_reln_defs.subst_ty := subst_ty x;
     twophase_sub_logical_reln_defs.subst_sval := subst_sval x;
     twophase_sub_logical_reln_defs.subst_ival := subst_ival x |}.

Definition filtered_subst (Γsubst : gmap string (@subst_tuple disk_op (jrnl_spec_ext) jrnl_ty )) (Γ': Ctx) :=
  subst_tuple_conv <$>
    (filter (λ x: string * ((@subst_tuple disk_op jrnl_spec_ext jrnl_ty)), is_Some (Γ' !! fst x)) Γsubst).

Lemma  filtered_subst_lookup1 (Γ' : Ctx) (Γsubst : gmap string (@subst_tuple disk_op (jrnl_spec_ext) jrnl_ty )) i :
  is_Some (Γ' !! i) →
  filter (λ x : string * ty, is_Some (Γ' !! x.1))
         (subst_ty <$> Γsubst) !! i = (subst_ty <$> Γsubst) !! i.
Proof.
  intros Hsome.
  destruct ((subst_ty <$> Γsubst) !! i) eqn:Heq.
  { apply map_filter_lookup_Some_2; eauto. }
  apply map_filter_lookup_None_2; eauto.
Qed.

Notation spec_ty := jrnl_ty.
Notation sty := (@ty (@val_tys _ spec_ty)).

Global Instance styG_twophaseG Σ: (styG (specTy_model := twophaseTy_model)) Σ → twophaseG Σ.
Proof. rewrite /styG//=. Defined.

Lemma atomic_convertible_val_interp {Σ} {hG: heapG Σ} {hRG : refinement_heapG Σ}
     {hS: (styG (specTy_model := twophaseTy_model)) Σ}
    (t : sty) es e dinit objs_dom γ γ' tph_val :
  atomic_convertible t →
  @val_interp _ _ _ _ _ _ _ _ _ _ hG hRG twophaseTy_model hS t es e -∗
  atomically_val_interp (htpG := hS) N PARAMS dinit objs_dom γ γ' tph_val t es e.
Proof.
  revert es e.
  rewrite /styG in hS * => //=.
  rewrite /twophaseTy_model in hS *.
  induction t => es e; try (inversion 1; done).
  - iIntros ((?&?)) "H".
    rewrite /val_interp -/val_interp.
    iDestruct "H" as (v1 v2 vs1 vs2 (Heq&Heqs)) "H".
    subst. iDestruct "H" as "(Hv1&Hv2)".
    rewrite /=.
    iExists _, _, _, _. iSplit; first eauto.
    iSplitL "Hv1".
    { iApply IHt1; eauto. }
    { iApply IHt2; eauto. }
  - iIntros (Hdeconv) "H".
    rewrite /val_interp -/val_interp.
    rewrite atomically_val_interp_list_unfold.
    iDestruct "H" as (?? Heq) "H".
    rewrite /listT_interp. iExists _, _; iSplit; first eauto.
    clear Heq.
    iInduction lvs as [| v lvs] "IH" forall (lv).
    * simpl. destruct lv; eauto.
    * simpl. destruct lv; eauto.
      iDestruct "H" as "(Hhd&Htl)".
      iSplitL "Hhd".
      { by iApply IHt. }
      iApply "IH"; eauto.
  - iIntros ((?&?)) "H".
    rewrite /val_interp -/val_interp.
    iDestruct "H" as "[H|H]"; iDestruct "H" as (v vs (Heq&Heqs)) "H"; subst; rewrite /=; [ iLeft | iRight ].
    { iExists _, _. iSplit; first eauto. by iApply IHt1. }
    { iExists _, _. iSplit; first eauto. by iApply IHt2. }
Qed.

Lemma atomically_deconvertible_val_interp `{hG: !heapG Σ} {hRG : refinement_heapG Σ} {hS: styG Σ}
      (t : sty) es e dinit objs_dom γ γ' tph_val :
  atomic_deconvertible t →
  atomically_val_interp (htpG := (styG_twophaseG _ hS)) N PARAMS dinit objs_dom γ γ' tph_val t es e -∗
  @val_interp _ _ _ _ _ _ _ _ _ _ hG hRG twophaseTy_model hS t es e.
Proof.
  revert es e.
  induction t => es e; try (inversion 1; done).
  - iIntros ((?&?)) "H".
    rewrite /val_interp -/val_interp.
    iDestruct "H" as (v1 v2 vs1 vs2 (Heq&Heqs)) "H".
    subst. iDestruct "H" as "(Hv1&Hv2)".
    rewrite /=.
    iExists _, _, _, _. iSplit; first eauto.
    iSplitL "Hv1".
    { iApply IHt1; eauto. }
    { iApply IHt2; eauto. }
  - iIntros (Hdeconv) "H".
    rewrite /val_interp -/val_interp.
    rewrite atomically_val_interp_list_unfold.
    iDestruct "H" as (?? Heq) "H".
    rewrite /listT_interp. iExists _, _; iSplit; first eauto.
    clear Heq.
    iInduction lvs as [| v lvs] "IH" forall (lv).
    * simpl. destruct lv; eauto.
    * simpl. destruct lv; eauto.
      iDestruct "H" as "(Hhd&Htl)".
      iSplitL "Hhd".
      { by iApply IHt. }
      iApply "IH"; eauto.
  - iIntros ((?&?)) "H".
    rewrite /val_interp -/val_interp.
    iDestruct "H" as "[H|H]"; iDestruct "H" as (v vs (Heq&Heqs)) "H"; subst; rewrite /=; [ iLeft | iRight ].
    { iExists _, _. iSplit; first eauto. by iApply IHt1. }
    { iExists _, _. iSplit; first eauto. by iApply IHt2. }
Qed.

Lemma filtered_subst_projection1 Γsubst Γ' :
  (∀ (x : string) (ty0 : ty),
      Γ' !! x = Some ty0 →
      (subst_ty <$> Γsubst) !! x = Some ty0 ∧ atomic_convertible ty0) →
  twophase_sub_logical_reln_defs.subst_ty <$> filtered_subst Γsubst Γ' = Γ'.
Proof.
  intros Hlookup.
  apply map_eq => i.
  specialize (Hlookup i).
  rewrite /filtered_subst.
  rewrite -map_fmap_compose //=.
  destruct (Γ' !! i) eqn:Heq.
  {
    transitivity (filter (λ x : string * _, is_Some (Γ' !! x.1)) (subst_ty <$> Γsubst) !! i).
    {symmetry. rewrite map_filter_fmap //=. }
    replace (Γ' !! i) with ((subst_ty <$> Γsubst) !! i); last first.
    { edestruct Hlookup as (Heq'&_); eauto. rewrite Heq'. eauto. }
    apply filtered_subst_lookup1; eauto.
  }
  rewrite Heq.
  rewrite lookup_fmap.
  apply fmap_None.
  apply map_filter_lookup_None_2; right. intros => //=.
  intros (?&Heq'). clear -Heq Heq'. rewrite Heq in Heq'. discriminate.
Qed.

Lemma subst_map_subtyping_sval Γsubst Γ' e1 x ebdy t :
  (∀ (x : string) (ty0 : sty),
    Γ' !! x = Some ty0 → (subst_ty <$> Γsubst) !! x = Some ty0 ∧ atomic_convertible ty0) →
  atomic_body_expr_transTy Γ' x e1 ebdy t →
  (subst_map (subst_sval <$> Γsubst) e1) =
  (subst_map (twophase_sub_logical_reln_defs.subst_sval <$> filtered_subst Γsubst Γ') e1).
Proof. Admitted.

Lemma subst_map_subtyping_ival Γsubst Γ' e1 ebdy tph tph_val t :
  (∀ (x : string) (ty0 : sty),
    Γ' !! x = Some ty0 → (subst_ty <$> Γsubst) !! x = Some ty0 ∧ atomic_convertible ty0) →
  atomic_body_expr_transTy Γ' (of_val tph_val) e1 (subst tph tph_val ebdy) t →
  (subst_map (subst_ival <$> Γsubst) (subst tph tph_val ebdy)) =
  (subst_map (twophase_sub_logical_reln_defs.subst_ival <$> filtered_subst Γsubst Γ') (subst tph tph_val ebdy)).
Proof. Admitted.

Lemma jrnl_atomic_obligation:
  @sty_atomic_obligation _ _ disk_semantics _ _ _ _ _ _ twophaseTy_model jrnl_atomic_transTy.
Proof using N PARAMS.
  rewrite /sty_atomic_obligation//=.
  iIntros (? hG hRG hJrnl el1 el2 tl e1 e2 t Γsubst Htrans) "Hinv #Hspec #Htrace #HΓ HhasTy".
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
  { intros Hin. eapply H0. revert Hin. rewrite elem_of_dom.
    intros (v&?). apply: elem_of_dom_2. eapply H; eauto. }
  wp_bind (subst _ _ _).
  rewrite subst_map_subst_comm //; last first.
  { rewrite dom_fmap. rewrite dom_fmap in H0 *. eauto. }
  iDestruct (atomically_fundamental_lemma N PARAMS dinit objs_dom γ γ' tph_val Γ') as "Hhas_semTy".
  { eauto. }
  rewrite /twophase_sub_logical_reln_defs.ctx_has_semTy.
  iDestruct ("Hhas_semTy" $! (filtered_subst Γsubst Γ') with "[] [$] [] [] [Hstarted]") as "H".
  { iPureIntro. apply filtered_subst_projection1; auto. }
  { rewrite /filtered_subst.
    iApply big_sepM_fmap => /=.
    iApply big_sepM_filter.
    iApply (big_sepM_mono with "HΓ").
    iIntros (k x Hlookup) "Hval Hfilter".
    iDestruct "Hfilter" as %(?&Heq).
    iApply (@atomic_convertible_val_interp with "Hval").
    { eapply H in Heq. destruct Heq as (Heq&Hconv).
      rewrite /= lookup_fmap Hlookup /= in Heq.
      inversion Heq; subst. eauto. }
  }
  { iPureIntro. apply id_ctx'. }
  { simpl.
    erewrite <-subst_map_subtyping_sval; eauto.
  }
  erewrite <-subst_map_subtyping_ival; eauto.
  iDestruct (wpc_wp with "H") as "H".
  iApply (wp_wand with "H [-]").
  iIntros (v') "Hv".
  iDestruct "Hv" as (vs') "(Hstarted&Hinterp)".
  rewrite /op_wrappers.TwoPhase__ConditionalCommit'.
  wp_pures.
  rewrite /=.
  iDestruct "Hinterp" as "[Hnone|Hsome]".
  {
    iDestruct "Hnone" as (vsnone vnone (->&->)) "Hunit".
    iDestruct "Hunit" as %(->&->).
    wp_pures.
    iMod (twophase_started_abort with "Hstarted") as "(Hrel&Hj)".
    wp_apply (wp_TwoPhase__ReleaseAll' with "Hrel").
    wp_pures. iExists _. iFrame. iLeft. eauto.
  }
  {
    iDestruct "Hsome" as (vssome vsome (->&->)) "Hv".
    wp_pures.
    rewrite /twophase.TwoPhase__Commit.
    wp_pures.
    wp_apply (wp_TwoPhase__CommitNoRelease' with "[$]").
    iIntros (ok) "H".
    destruct ok.
    - iDestruct "H" as "(Hrel&Hj)".
      wp_pures.
      wp_apply (wp_TwoPhase__ReleaseAll' with "[$]").
      wp_pures. iExists _. iFrame.
      rewrite /val_interp -/val_interp.
      iRight. iExists _, _. iSplit; first eauto. simpl; auto.
      iApply (atomically_deconvertible_val_interp with "[$]"); eauto.
      naive_solver.
    - wp_pures.
      iMod (twophase_started_abort with "H") as "(H&Hj)".
      wp_apply (wp_TwoPhase__ReleaseAll' with "[$]").
      wp_pures. iExists _. iFrame.
      rewrite /val_interp -/val_interp.
      iLeft. iExists _, _. iSplit; first eauto. simpl; auto.
  }
Qed.

Existing Instances jrnl_semantics.
Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field spec_ffi_interp_field spec_ffi_interp_adequacy_field.
(* XXX: might need to change typed_translate / refinement to use the spec_ wrappers around type classes *)

Lemma jrnl_refinement (es: @expr jrnl_op) σs e σ (τ: @ty jrnl_ty.(@val_tys jrnl_op)):
  typed_translate.expr_transTy _ _ _ jrnl_trans jrnl_atomic_transTy ∅ es e τ →
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  twophase_initP σ σs →
  refinement.trace_refines e e σ es es σs.
Proof using N PARAMS.
  intros. intros ?.
  efeed pose proof sty_adequacy; eauto using jrnl_init_obligation1, jrnl_init_obligation2,
                                 jrnl_crash_inv_obligation, jrnl_crash_obligation,
                                 jrnl_rules_obligation, jrnl_atomic_obligation.
Qed.
End refinement.
