From Perennial.goose_lang.lib Require Import encoding crash_lock.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import
     txn.typed_translate txn.wrapper_proof txn.wrapper_init_proof
     txn.twophase_refinement_defs txn.twophase_sub_logical_reln_defs
     txn.typed_translate_facts
     alloc.alloc_proof.
From Perennial.goose_lang Require Import crash_modality.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang Require Import logical_reln_defns logical_reln_adeq spec_assert metatheory.
From Perennial.base_logic Require Import ghost_var.
From Perennial.program_proof Require Import lockmap_proof.

From Goose Require github_com.mit_pdos.go_journal.obj.

Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp jrnl_spec_interp_adequacy.

Section refinement.
Context (JRNL_KIND_SIZE : nat).

Definition dinit0 sz : gmap Z Block :=
  gset_to_gmap block0 (list_to_set $ seqZ 513 (sz-513)).

Lemma dom_dinit0:
  ∀ sz : Z,
    dom (gset Z) (dinit0 sz) = list_to_set (seqZ 513 (sz - 513)).
Proof.
  intros sz.
  rewrite /dinit0.
  rewrite dom_gset_to_gmap.
  auto with f_equal lia.
Qed.

Opaque crash_borrow.pre_borrow.

Lemma jrnl_init_obligation1: sty_init_obligation1 (twophaseTy_update_model JRNL_KIND_SIZE) (twophase_initP JRNL_KIND_SIZE).
Proof.
  rewrite /sty_init_obligation1//=.
  iIntros (? hG hRG hJrnl σs gs σi gi Hinit) "Hdisk".
  rewrite /jrnl_start /twophase_init.
  destruct Hinit as (sz&kinds&Hsize2&Hnn&Heqi&Heqs&Hdom&Hkind_size).
  rewrite Heqs Heqi.
  iIntros "(Hclosed_frag&Hjrnl_frag)".
  iDestruct "Hjrnl_frag" as "(Hsmapstos&Hcrashtoks&Hcrash_ctx&Hkinds&Hdom&Hfull)".
  rewrite /twophase_crash_cond_full.
  iMod (sep_jrnl_recovery_proof.is_txn_durable_init
          (dinit0 (sz + 513)) kinds sz with "[Hdisk]") as "H".
  { rewrite dom_dinit0. repeat f_equal. lia. }
  { eauto. }
  { lia. }
  { iDestruct (disk_array_init_disk with "Hdisk") as "Hdisk".
    rewrite -recovery_proof.repeat_to_replicate.
    rewrite repeat_app disk_array_app.
    iDestruct "Hdisk" as "[Hlog Hd]".
    rewrite repeat_length.
    replace (0 + (Z.of_nat 513))%Z with 513%Z by lia.
    iSplitL "Hlog"; first by iExact "Hlog".
    iExactEq "Hd". f_equal.
  }
  rewrite /LVL_INIT.
  iIntros "Hpre".
  iDestruct "H" as (γ) "(%Hγ&His_txn_durable&#Hlb&Himapstos)".
  iExists tt, γ, _, _, (recovery_proof.kind_heap0 kinds).
  iFrame "His_txn_durable".
  iModIntro.
  iDestruct "Hpre" as "($&Hpre)".
  rewrite -?sep_assoc.
  iSplit.
  {
    iPureIntro. eauto.
    eapply map_Forall_impl; first eapply kind_heap0_ok.
    { intros a Hin. revert Hin. rewrite Hdom elem_of_list_to_set elem_of_list_fmap; intros (x&->&Hin).
      apply elem_of_seqZ in Hin. clear -Hsize2 Hin. rewrite /block_bytes in Hsize2.
      word.
    }
    { intros i (?&?) (?&?&?).
      split_and!; eauto. congruence. }
  }
  iSplit.
  { rewrite /named. iExactEq "Hdom". f_equal. rewrite dom_fmap_L //. }
  iSplit.
  { rewrite /named. iExactEq "Hkinds". f_equal. rewrite //=. }
  iFrame "Hfull Hclosed_frag Hcrash_ctx".
  rewrite /=.
  iEval (rewrite big_sepM_fmap) in "Hsmapstos".
  iEval (rewrite big_sepM_fmap) in "Hcrashtoks".
  iDestruct (big_sepM_sep with "[$Hsmapstos $Hcrashtoks]") as "H".
  iDestruct (big_sepM_sep with "[$H $Himapstos]") as "H".
  iSplitL "H".
  - iApply (big_sepM_mono with "H").
    { iIntros (?? Hlookup) "(Hkind&Hmod&Hdurable)".
      iFrame. }
  - iFrame "%". iApply (crash_borrow.pre_borrowN_big_sepM with "[$]").
    eauto.
Qed.

Lemma jrnl_init_obligation2: sty_init_obligation2 (twophase_initP JRNL_KIND_SIZE).
Proof.
  intros ???? (sz&?&Hsize2&?&?&?&Hdom&Hksz). rewrite //=. split_and!; eauto.
  eexists; split; eauto. eapply wf_jrnl_alt, kind_heap0_ok.
  { intros a Hin. revert Hin. rewrite Hdom elem_of_list_to_set elem_of_list_fmap; intros (?&->&Hin).
    apply elem_of_seqZ in Hin. clear -Hsize2 Hin. rewrite /block_bytes in Hsize2.
    word.
  }
Qed.

Lemma jrnl_rules_obligation:
  @sty_rules_obligation _ _ disk_semantics _ _ _ _ _ _ (twophaseTy_model JRNL_KIND_SIZE) jrnl_trans.
Proof.
  intros vs0 vs v0 v0' t1 t2 Htype0 Htrans.
  inversion Htype0 as [op Heq|op Heq]; subst.
  - iIntros (????) "#Hinv #Hspec #Hval".
    iIntros (j K Hctx) "Hj".
    iDestruct "Hval" as %[-> ->].
    inversion Htrans. subst.
    iApply wp_wpc.
    iMod (ghost_step_lifting_puredet with "[$Hj]") as "(Hj&_)".
    { econstructor. apply head_prim_step_trans. econstructor. eauto. }
    { solve_ndisj. }
    { iDestruct "Hspec" as "(?&?)". eauto. }
    wp_apply (wp_Init JRNL_KIND_SIZE (nroot.@"H") with "[Hj]").
    { solve_ndisj. }
    { solve_ndisj. }
    { iFrame "# ∗". }
    iIntros (l') "(Hj&Hopen&H)". iNamed "H".
    iExists _. iFrame "Hj". rewrite /val_interp//=/twophase_val_interp.
    iExists _, _, _, _, _.
    iFrame "Htwophase Hopen". eauto.
  - iIntros (????) "#Hinv #Hspec #Hval".
    iIntros (j K Hctx) "Hj".
    iDestruct "Hval" as %(n&->&->).
    inversion Htrans. subst.
    iApply wp_wpc.
    iMod (ghost_step_lifting_puredet with "[$Hj]") as "(Hj&_)".
    { econstructor. apply head_prim_step_trans. econstructor. eauto. }
    { solve_ndisj. }
    { iDestruct "Hspec" as "(?&?)". eauto. }
    iMod (ghost_step_jrnl_mkalloc with "[$] [$Hj]") as "H".
    { solve_ndisj. }
    iDestruct "H" as (l [Hgt0 Hmod8]) "(Hj&Halloc)".
    wp_apply (wp_MkMaxAlloc).
    { eauto. }
    { eauto. }
    iIntros (l') "Halloc'".
    iExists _. iFrame "Hj".
    iExists _, _, _. iFrame. eauto.
Qed.

Lemma fmap_unit_jrnl_dom_equal (jd jd': gmap addr_proof.addr obj) :
  dom (gset _) jd = dom (gset _) jd' →
  (λ _, ()) <$> jd = (λ _, ()) <$> jd'.
Proof.
  intros Hdom.
  apply map_eq => i.
  destruct (decide (i ∈ dom (gset (u64 * u64)) jd)) as [Hin|Hnin].
  { assert (Hin': i ∈ dom (gset (u64 * u64)) jd').
    { rewrite -Hdom; eauto. }
    rewrite ?lookup_fmap.
    apply elem_of_dom in Hin as (?&->).
    apply elem_of_dom in Hin' as (?&->).
    rewrite //=.
  }
  { assert (Hnin': ¬ i ∈ dom (gset (u64 * u64)) jd').
    { rewrite -Hdom; eauto. }
    rewrite ?lookup_fmap.
    apply not_elem_of_dom in Hnin as ->.
    apply not_elem_of_dom in Hnin' as ->.
    rewrite //=.
  }
Qed.

Opaque crash_borrow.crash_borrow.

Lemma jrnl_crash_inv_obligation:
  @sty_crash_inv_obligation _ _ disk_semantics _ _ _ _ _ _ (twophaseTy_model JRNL_KIND_SIZE).
Proof.
  rewrite /sty_crash_inv_obligation//=.
  iIntros (? hG hRG hJrnl) "H Hspec #Hspec_crash_ctx".
  iDestruct "H" as (????) "(Hcrash_cond&Hauth&Htok&Hclosed_frag&Hpre&HpreM)".
  iAssert (jrnl_dom (dom _ mt)) with "[Hcrash_cond]" as "#Hdom".
  { iDestruct "Hcrash_cond" as "(H1&?&?&H2)". iFrame. }
  rewrite /twophase_init/twophase_inv.
  iDestruct (crash_borrow.crash_borrow_init_cancel
                           (∃ γ dinit logm mt',
                               ([∗ map] _ ↦ _ ∈ mt', crash_borrow.pre_borrow) ∗
                                  twophase_crash_cond_full JRNL_KIND_SIZE γ dinit logm mt')%I
                           (∃ γ dinit logm mt',
                                  twophase_crash_cond_full JRNL_KIND_SIZE γ dinit logm mt')%I
          with "[$] [Hcrash_cond HpreM] []") as "Hinit". (* "(Hna_crash_inv&Hcancel)". *)
  { iExists _, _, _, _. iFrame "HpreM". iExact "Hcrash_cond". }
  { iModIntro. iIntros "H".
    iNamed "H". iExists _, _, _, _. iDestruct "H" as "(_&$)". }
  iMod (ghost_var_alloc (0, expr_id)) as (γghost) "Hghost".
  rewrite /twophase_crash_tok.
  iApply (init_cancel_fupd ⊤).
  iModIntro.
  iApply (init_cancel_wand with "Hinit [-Htok Hauth]").
  {
    iIntros "Hborrow".
    iMod (inv_alloc twophaseInitN _ (twophase_inv_inner JRNL_KIND_SIZE γghost) with
              "[Hclosed_frag Hborrow Hghost]") as "#Hinv".
    { iNext. iLeft. iFrame. }
    iModIntro.
    { iExists _. iFrame "Hinv Hspec_crash_ctx". }
  }
  iIntros "H".
  iNamed "H".
  iDestruct "H" as "Hcancel".
  iRename "Hdom" into "Hdom'".
  iNamed "Hcancel".
  iDestruct "Hdom" as "#Hdom".
  iDestruct (jrnl_dom_agree with "[$Hdom] [$Hdom']") as %Hdom.
  rewrite /twophase_crash_cond.
  rewrite /twophase_crash_tok.
  rewrite /jrnl_mapsto_own.
  iEval (setoid_rewrite sep_assoc) in "Hmapstos".
  iDestruct (big_sepM_sep with "Hmapstos") as "(H1&H2)".
  iSplitL "H1 Htxn_durable".
  { iExists _, _, _, _. iFrame. eauto. }
  iFrame.
  iExists {| jrnlData := (bufObj_to_obj <$> _); jrnlKinds := ∅; jrnlAllocs := ∅ |}.
  iSplitL "H2".
  { iApply big_sepM_fmap. iExact "H2". }
  rewrite /=.
  rewrite /spec_crash_ctx.
  rewrite /source_crash_ctx.
  rewrite /jrnl_full_crash_tok.
  erewrite (fmap_unit_jrnl_dom_equal (bufObj_to_obj <$> mt) (bufObj_to_obj <$> mt')); last first.
  { rewrite !dom_fmap_L //=. }
  eauto.
Qed.

Lemma jrnl_crash_obligation:
  @sty_crash_obligation _ _ disk_semantics _ _ _ _ _ _ (twophaseTy_model JRNL_KIND_SIZE).
Proof.
  rewrite /sty_crash_obligation//=.
  iIntros (? hG hRG hJrnl) "Hinv Hcrash_cond".
  iModIntro. iNext.
  iIntros (hG'). iModIntro.
  iIntros (σs) "H". iDestruct "H" as (??) "(_&H)".
  iDestruct "H" as %[Heq1 Heq2].
  iIntros "Hctx".
  iExists
    (RecordSet.set trace add_crash
       (RecordSet.set world (λ w : @ffi_state jrnl_model, match w with
                                                | Closed s => Closed (clearAllocs s)
                                                | Opened s => Closed (clearAllocs s)
                                              end : @ffi_state jrnl_model)
          (RecordSet.set heap (λ _ : gmap loc (nonAtomic val), ∅) σs))).
  unshelve (iExists _).
  { econstructor.
    { reflexivity. }
    rewrite //=. repeat econstructor. destruct σs.(world) => //=. }
  iFrame "Hctx".
  iIntros (hRG' Heq) "Hrestart". rewrite //=.
  assert (∃ s, σs.(world) = Closed s ∨ σs.(world) = Opened s) as (s&Hcase).
  { destruct σs.(world); eauto. }
  iAssert (jrnl_restart _ (Closed s))%I with "[Hrestart]" as "Hrestart".
  { destruct Hcase as [Hcase|Hcase]; rewrite Hcase; eauto. }
  rewrite //=.
  rewrite /jrnl_state_restart.
  iDestruct "Hrestart" as "(Hclosed&Hcrash_toks&Hcrash_ctx&#Hkinds&#Hdom&Hfull)".
  iIntros "Hpre".
  iModIntro. iExists tt.
  rewrite /twophase_init.  iFrame "Hfull Hclosed".
  rewrite /twophase_crash_cond.
  rewrite /twophase_update.
  iDestruct "Hcrash_cond" as (????) "H".
  iRename "Hdom" into "Hdom'".
  iNamed "H".
  iDestruct "Hdom" as "#Hdom".
  iExists γ, dinit, logm, mt. rewrite /twophase_crash_cond_full.
  rewrite -sep_assoc.
  iSplit; first eauto.
  rewrite -sep_assoc.
  iSplitL "Htxn_durable".
  {
    rewrite /sep_jrnl_recovery_proof.is_txn_durable.
    iNamed "Htxn_durable". iFrame "Hlogm Hasync_ctx".
    specialize (@recovery_proof.is_txn_durable_stable) => Hcrash.
    rewrite /IntoCrash in Hcrash.
    iPoseProof (Hcrash _ _ hG _ with "Hlower_durable") as "H".
    rewrite /post_crash. iApply ("H" $! _ _ hG').
    eauto.
  }
  iAssert (⌜ dom (gset _) mt = dom (gset _) (jrnlData s)⌝)%I with "[]" as %Hdomeq.
  { rewrite /jrnl_dom.
    destruct Heq as (Heq_data&Heq_kinds&Heq_dom&Heq_data_name&Heq_kinds_name&Heq_dom_name).
    rewrite /jrnl_mapsto/jrnl_kinds.
    rewrite Heq_dom Heq_dom_name.
    iDestruct (jrnl_dom_agree with "Hdom Hdom'") as %Hdom; eauto.
  }
  rewrite Hdomeq. iFrame "Hdom'".
  iDestruct (big_sepM_dom with "Hcrash_toks") as "Hcrash_toks".
  rewrite -Hdomeq.
  iDestruct (big_sepM_dom with "Hcrash_toks") as "Hcrash_toks".
  iCombine "Hmapstos Hcrash_toks" as "Hmapstos".
  rewrite -big_sepM_sep.
  rewrite -sep_assoc.
  iSplitL "".
  {
    destruct Heq as (Heq_data&Heq_kinds&Hdom&Heq_data_name&Heq_kinds_name&_).
    rewrite /jrnl_mapsto/jrnl_kinds.
    rewrite Heq_kinds Heq_kinds_name.
    iFrame "#".
  }
  iSplitL "Hmapstos".
  {
    iFrame "%".
    iApply (big_sepM_mono with "Hmapstos").
    { iIntros (???) "(($&Hjrnl)&Htok)".
      rewrite /jrnl_mapsto_own.
      iNamed "Hjrnl".
      iNamed "Hjrnl_mapsto".
      rewrite /jrnlG0//=.
      destruct Heq as (Heq_data&Heq_kinds&Hdom&Heq_data_name&Heq_kinds_name&_).
      rewrite /jrnl_mapsto/jrnl_kinds.
      rewrite Heq_data Heq_data_name Heq_kinds Heq_kinds_name.
      iFrame.
    }
  }
  iDestruct "Hpre" as "($&HpreM)".
  iSplitL "Hcrash_ctx".
  { iExactEq "Hcrash_ctx".
    f_equal.
    eapply fmap_unit_jrnl_dom_equal; eauto => //=.
    rewrite dom_fmap_L //=. }
  iApply (crash_borrow.pre_borrowN_big_sepM with "HpreM"). eauto.
Qed.


Lemma jrnl_inv_twophase_pre {Σ} {hG: heapGS Σ} {hRG: refinement_heapG Σ}
      {hJrnl : twophaseG Σ} vs v:
    twophase_inv JRNL_KIND_SIZE -∗
    val_interp (smodel := twophaseTy_model JRNL_KIND_SIZE) (hS := hJrnl) (@extT jrnl_val_ty JrnlT) vs v -∗
    ∃ (l : loc) γ γ' objs_dom dinit, ⌜ v = #l ⌝ ∗ is_twophase_pre l γ γ' dinit objs_dom.
Proof.
  iIntros "H1 H2".
  iDestruct "H2" as (l γ γ' dinit objs_dom -> ->) "(H&?)".
  iExists l, γ, γ', objs_dom, dinit. iSplit; first eauto.
  iExact "H".
Qed.

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
    * eapply IHHtyping; eauto; unfold_expr_vars; set_solver.
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

Lemma binder_delete_filtered_subst Γsubst Γ x :
  binder_delete x (filtered_subst Γsubst Γ) = filtered_subst Γsubst (binder_delete x Γ).
Proof.
  rewrite /filtered_subst. rewrite -binder_delete_fmap.
  f_equal. destruct x.
  - rewrite //=.
  - rewrite //=.
    apply map_eq => i.
    destruct (decide (s = i)).
    * subst. rewrite lookup_delete.
      symmetry. apply map_filter_lookup_None_2; eauto.
      right. intros. rewrite lookup_delete //=.
    * rewrite lookup_delete_ne //.
      destruct (decide (is_Some (Γ !! i))).
      ** rewrite ?(map_filter_lookup_key_in _ (λ i, is_Some (Γ !! i))) //.
         rewrite ?(map_filter_lookup_key_in _ (λ i, is_Some (delete s Γ !! i))) //.
         rewrite lookup_delete_ne //.
      ** rewrite ?(map_filter_lookup_key_notin _ (λ i, is_Some (Γ !! i))) //.
         rewrite ?(map_filter_lookup_key_notin _ (λ i, is_Some (delete s Γ !! i))) //.
         rewrite lookup_delete_ne //.
Qed.

Lemma binder_delete_filtered_subst2 Γsubst Γ x :
  binder_delete x (filtered_subst Γsubst Γ) = filtered_subst (binder_delete x Γsubst) Γ.
Proof.
  destruct x => /=; auto.
  rewrite /filtered_subst -fmap_delete map_filter_delete //.
Qed.

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

Global Instance styG_twophaseG Σ: (styG (specTy_model := twophaseTy_model JRNL_KIND_SIZE)) Σ → twophaseG Σ.
Proof. rewrite /styG//=. Defined.

Lemma atomic_convertible_val_interp {Σ} {hG: heapGS Σ} {hRG : refinement_heapG Σ}
     {hS: (styG (specTy_model := twophaseTy_model JRNL_KIND_SIZE)) Σ}
    (t : sty) es e dinit objs_dom γ γ' tph_val :
  atomic_convertible t →
  @val_interp _ _ _ _ _ _ _ _ _ _ hG hRG (twophaseTy_model JRNL_KIND_SIZE) hS t es e -∗
  atomically_val_interp (htpG := hS) JRNL_KIND_SIZE dinit objs_dom γ γ' tph_val t es e.
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
    iInduction lvs as [| v lvs] "IH" forall (lv IHt).
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
  - rewrite //= /val_interp/twophase_val_interp //=.
    destruct x; eauto.
Qed.

Lemma atomically_deconvertible_val_interp `{hG: !heapGS Σ} {hRG : refinement_heapG Σ} {hS: styG Σ}
      (t : sty) es e dinit objs_dom γ γ' tph_val :
  atomic_deconvertible t →
  atomically_val_interp (htpG := (styG_twophaseG _ hS)) JRNL_KIND_SIZE dinit objs_dom γ γ' tph_val t es e -∗
  @val_interp _ _ _ _ _ _ _ _ _ _ hG hRG (twophaseTy_model JRNL_KIND_SIZE) hS t es e.
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
  - rewrite //= /val_interp/twophase_val_interp //=.
    destruct x; eauto.
    intros [].
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

Lemma lookup_binder_insert_ne  x y v (m : Ctx) :
  x ≠ BNamed y →
  <[x := v]> m !! y = m !! y.
Proof.
  intros Hneq. destruct x; rewrite //= ?lookup_insert_ne //=; congruence.
Qed.

Lemma lookup_binder_delete_ne {A} x y (m : gmap _ A) :
  x ≠ BNamed y →
  binder_delete x m !! y = m !! y.
Proof.
  intros Hneq. destruct x; rewrite //= ?lookup_delete_ne //=; congruence.
Qed.

Lemma filtered_subst_insert_filter Γsubst Γ (x : binder) v :
  match x with
  | BAnon => True
  | BNamed x => Γsubst !! x = None
  end →
  filtered_subst Γsubst (<[x := v]> Γ) = filtered_subst Γsubst Γ.
Proof.
  intros Hnone. apply map_eq=>i.
  rewrite /filtered_subst.
  rewrite ?lookup_fmap. f_equal.
  f_equal.
  apply map_filter_ext.
  intros i' x' Hlookup.
  rewrite /=. destruct x => //=. rewrite lookup_insert_ne //=.
  congruence.
Qed.

Lemma subst_map_subtyping_sval' Γsubst Γ' e1 x ebdy t :
  (∀ (x : string) (ty0 : sty) ty0',
    Γ' !! x = Some ty0 → (subst_ty <$> Γsubst) !! x = Some ty0' → ty0 = ty0' ∧ atomic_convertible ty0) →
  atomic_body_expr_transTy Γ' x e1 ebdy t →
  (subst_map (subst_sval <$> Γsubst) e1) =
  (subst_map (twophase_sub_logical_reln_defs.subst_sval <$> filtered_subst Γsubst Γ') e1).
Proof.
  intros Hmap Htrans. revert Γsubst Hmap.
  induction Htrans => Γsubst Hmap; try (rewrite /= ?IHHtrans ?IHHtrans1 ?IHHtrans2 ?IHHtrans3 //=).
  - rewrite //=.
    rewrite ?lookup_fmap //=.
    destruct (Γsubst !! x) eqn:Heq.
    * rewrite /=. edestruct Hmap as (Heq'&Hconv); eauto.
      { rewrite ?lookup_fmap Heq. eauto. }
      rewrite ?lookup_fmap //=.
      erewrite map_filter_lookup_Some_2; eauto.
    * rewrite /=. erewrite map_filter_lookup_None_2; eauto.
  - f_equal.
    rewrite -binder_delete_fmap.
    rewrite -binder_delete_fmap.
    rewrite -binder_delete_fmap.
    rewrite -binder_delete_fmap.
    rewrite binder_delete_filtered_subst2.
    rewrite binder_delete_filtered_subst2.
    rewrite IHHtrans; last first.
    { intros y ty ty' Hlookup.
      rewrite lookup_fmap.
      destruct (decide (x = BNamed y)).
      { subst. rewrite //= lookup_delete; naive_solver. }
      rewrite lookup_binder_delete_ne //.
      destruct (decide (f = BNamed y)).
      { subst. rewrite lookup_delete; naive_solver. }
      rewrite lookup_binder_delete_ne //.
      rewrite ?lookup_binder_insert_ne // in Hlookup.
      intros. eapply Hmap; eauto.
      rewrite lookup_fmap //.
    }
    rewrite ?filtered_subst_insert_filter //=.
    { destruct x; auto => //=. rewrite lookup_delete //. }
    { destruct f; auto => //=.
      destruct x.
      * rewrite /= lookup_delete //.
      * rewrite /=. destruct (decide (s0 = s)); subst.
        ** rewrite lookup_delete //.
        ** rewrite lookup_delete_ne // lookup_delete //.
    }
Qed.

Lemma subst_map_subtyping_sval Γsubst Γ' e1 x ebdy t :
  (∀ (x : string) (ty0 : sty),
    Γ' !! x = Some ty0 → (subst_ty <$> Γsubst) !! x = Some ty0 ∧ atomic_convertible ty0) →
  atomic_body_expr_transTy Γ' x e1 ebdy t →
  (subst_map (subst_sval <$> Γsubst) e1) =
  (subst_map (twophase_sub_logical_reln_defs.subst_sval <$> filtered_subst Γsubst Γ') e1).
Proof.
  intros. eapply subst_map_subtyping_sval'; eauto.
  naive_solver.
Qed.

Lemma subst_map_subtyping_ival' Γsubst Γ' e1 (v : val) ebdy t :
  (∀ (x : string) (ty0 : sty) ty0',
    Γ' !! x = Some ty0 → (subst_ty <$> Γsubst) !! x = Some ty0' → ty0 = ty0' ∧ atomic_convertible ty0) →
  atomic_body_expr_transTy Γ' v e1 ebdy t →
  (subst_map (subst_ival <$> Γsubst) ebdy) =
  (subst_map (twophase_sub_logical_reln_defs.subst_ival <$> filtered_subst Γsubst Γ') ebdy).
Proof.
  intros Hmap Htrans. revert Γsubst Hmap.
  remember (of_val v) as tph eqn:Heq0. rewrite -Heq0 in Htrans.
  induction Htrans => Γsubst Hmap; try (rewrite /= ?IHHtrans ?IHHtrans1 ?IHHtrans2 ?IHHtrans3 //=).
  - rewrite //=.
    rewrite ?lookup_fmap //=.
    destruct (Γsubst !! x) eqn:Heq.
    * rewrite /=. edestruct Hmap as (Heq'&Hconv); eauto.
      { rewrite ?lookup_fmap Heq. eauto. }
      rewrite ?lookup_fmap //=.
      erewrite map_filter_lookup_Some_2; eauto.
    * rewrite /=. erewrite map_filter_lookup_None_2; eauto.
  - f_equal.
    rewrite -binder_delete_fmap.
    rewrite -binder_delete_fmap.
    rewrite -binder_delete_fmap.
    rewrite -binder_delete_fmap.
    rewrite binder_delete_filtered_subst2.
    rewrite binder_delete_filtered_subst2.
    rewrite IHHtrans; last first.
    { intros y ty ty' Hlookup.
      rewrite lookup_fmap.
      destruct (decide (x = BNamed y)).
      { subst. rewrite //= lookup_delete; naive_solver. }
      rewrite lookup_binder_delete_ne //.
      destruct (decide (f = BNamed y)).
      { subst. rewrite lookup_delete; naive_solver. }
      rewrite lookup_binder_delete_ne //.
      rewrite ?lookup_binder_insert_ne // in Hlookup.
      intros. eapply Hmap; eauto.
      rewrite lookup_fmap //.
    }
    { eauto. }
    rewrite ?filtered_subst_insert_filter //=.
    { destruct x; auto => //=. rewrite lookup_delete //. }
    { destruct f; auto => //=.
      destruct x.
      * rewrite /= lookup_delete //.
      * rewrite /=. destruct (decide (s0 = s)); subst.
        ** rewrite lookup_delete //.
        ** rewrite lookup_delete_ne // lookup_delete //.
    }
  - rewrite Heq0. f_equal.
  - rewrite Heq0. f_equal.
  - rewrite Heq0. f_equal.
  - rewrite Heq0. f_equal.
Qed.

Lemma subst_map_subtyping_ival Γsubst Γ' e1 ebdy tph tph_val t :
  (∀ (x : string) (ty0 : sty),
    Γ' !! x = Some ty0 → (subst_ty <$> Γsubst) !! x = Some ty0 ∧ atomic_convertible ty0) →
  atomic_body_expr_transTy Γ' (of_val tph_val) e1 (subst tph tph_val ebdy) t →
  (subst_map (subst_ival <$> Γsubst) (subst tph tph_val ebdy)) =
  (subst_map (twophase_sub_logical_reln_defs.subst_ival <$> filtered_subst Γsubst Γ') (subst tph tph_val ebdy)).
Proof.
  intros. eapply subst_map_subtyping_ival'; eauto.
  naive_solver.
Qed.

Local Definition N := nroot.@"tpref".

Lemma jrnl_atomic_obligation:
  @sty_atomic_obligation _ _ disk_semantics _ _ _ _ _ _ (twophaseTy_model JRNL_KIND_SIZE) jrnl_atomic_transTy.
Proof.
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
  iSplit; last by (eauto).
  iIntros (v) "Hv". iModIntro.
  wpc_bind (txn.Begin v).
  iApply wp_wpc.
  iDestruct "Hv" as (vs) "(Hj&Hinterp)".
  iDestruct (jrnl_inv_twophase_pre with "[$] [$]") as "H".
  iDestruct "H" as (l γ γ' ?? ->) "H".
  wp_apply (wp_Txn__Begin' N  with "[$]").
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
  iDestruct (atomically_fundamental_lemma JRNL_KIND_SIZE dinit objs_dom γ γ' tph_val Γ') as "Hhas_semTy".
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
  rewrite /op_wrappers.Txn__ConditionalCommit'.
  wp_pure1.
  wp_bind (Rec _ _ _).
  iDestruct "Hinterp" as "[Hnone|Hsome]".
  {
    iDestruct "Hnone" as (vsnone vnone (->&->)) "Hunit".
    iDestruct "Hunit" as %(->&->).
    iDestruct (twophase_started_abort with "Hstarted") as "H".
    iApply (wpc_nval_elim_wp with "H"); auto. wp_pures.
    iIntros "!> (Hrel&Hj)".
    wp_apply (wp_Txn__ReleaseAll' with "Hrel").
    wp_pures. iExists _. iFrame. iLeft. eauto.
  }
  {
    iDestruct "Hsome" as (vssome vsome (->&->)) "Hv".
    wp_pures.
    rewrite /txn.Txn__Commit.
    wp_pures.
    wp_apply (wp_Txn__commitNoRelease' with "[$]").
    iIntros (ok) "H".
    destruct ok.
    - iDestruct "H" as "(Hrel&Hj)".
      wp_pures.
      wp_apply (wp_Txn__ReleaseAll' with "[$]").
      wp_pures. iExists _. iFrame. iModIntro.
      rewrite /val_interp -/val_interp.
      iRight. iExists _, _. iSplit; first eauto. simpl; auto.
      iApply (atomically_deconvertible_val_interp with "Hv"); eauto.
      naive_solver.
    - iDestruct "H" as "(Hrel&Hj)".
      wp_pures.
      wp_apply (wp_Txn__ReleaseAll' with "[$]").
      wp_pures. iExists _. iFrame. iModIntro.
      rewrite /val_interp -/val_interp.
      iLeft. iExists _, _. iSplit; first eauto. simpl; auto.
  }
Qed.

End refinement.
