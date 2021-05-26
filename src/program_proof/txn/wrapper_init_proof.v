From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import map.impl list.impl list.list_slice slice.typed_slice.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang.ffi Require Import disk.
From Goose.github_com.mit_pdos.go_journal Require Import obj txn.
From Perennial.program_proof Require Import lockmap_proof.
From Perennial.program_proof Require Import txn.op_wrappers.
From Perennial.program_proof Require Import addr.addr_proof buf.buf_proof obj.obj_proof.
From Perennial.program_proof Require Import jrnl.sep_jrnl_proof.
From Perennial.program_proof Require Import txn.txn_proof.
From Perennial.program_proof Require Import txn.wrapper_proof.
From Perennial.program_proof Require Import txn.twophase_refinement_defs.
From Perennial.program_logic Require Import na_crash_inv.
From Perennial.goose_lang.lib.list Require Import list.
From Perennial.goose_lang Require Import spec_assert crash_borrow.

From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.program_proof Require Import disk_prelude.

Section proof.
  Context `{!heapGS Σ}.
  Context `{!lockmapG Σ}.
  Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp
           jrnl_spec_interp_adequacy.
  Context `{hRG: !refinement_heapG Σ}.
  Context `{aG: twophaseG Σ}.
  Existing Instance jrnlG0.
  Context (JRNL_SIZE : nat).

  Notation spec_ext := jrnl_spec_ext.
  Notation sval := (@val (@spec_ffi_op_field spec_ext)).

  Implicit Types (N: namespace).
  Definition twophase_obj_cfupd_cancel γ γ' d :=
   ((|C={⊤}_(S (S LVL))=> ∃ mt',
       ⌜ dom (gset _) mt' = d ⌝ ∗
       ⌜γ.(jrnl_txn_names).(txn_kinds) = γ'.(jrnl_txn_names).(txn_kinds)⌝ ∗
       ⌜ map_Forall (mapsto_valid γ') mt' ⌝ ∗
       "Hmapstos" ∷ ([∗ map] a ↦ obj ∈ mt',
         "Hdurable_mapsto" ∷ durable_mapsto_own γ' a obj ∗
         "Hjrnl_mapsto" ∷ jrnl_mapsto_own a obj) ∗
      "%Hdomsize" ∷ ⌜ size mt' = JRNL_SIZE ⌝))%I.

  Theorem wpc_Init N d γ dinit logm mt mj (Hlt: (/2 < mj)%Qp) :
    N ## invN →
    N ## invariant.walN →
    map_Forall (mapsto_valid γ) mt →
    {{{
      "Hpre" ∷ ([∗ map] _ ↦ _ ∈ mt, pre_borrow) ∗
      "Htxn_durable" ∷ is_txn_durable γ dinit logm ∗
      "Hmapstos" ∷ ([∗ map] a ↦ obj ∈ mt,
        "Hdurable_mapsto" ∷ durable_mapsto_own γ a obj ∗
        "Hjrnl_mapsto" ∷ jrnl_mapsto_own a obj
      ) ∗
      "%Hdomsize" ∷ ⌜ size mt = JRNL_SIZE ⌝ ∗
      "#Hspec_ctx" ∷ spec_ctx ∗
      "#Hspec_crash_ctx" ∷ spec_crash_ctx jrnl_crash_ctx ∗
      "#Hjrnl_open" ∷ jrnl_open ∗
      "#Hjrnl_kinds_lb" ∷ jrnl_kinds γ.(jrnl_txn_names).(txn_kinds) ∗
      "#Hjrnl_dom" ∷ jrnl_dom (dom _ mt)
    }}}
      let: "twophasePre" := struct.alloc txn.Log (MkLog (disk_val d), (lockmap.MkLockMap #(), #())) in
      Var "twophasePre" @ S (S LVL); ⊤
    {{{
      γ' (l: loc), RET #l;
      "Htwophase" ∷ is_twophase_pre l γ γ' dinit (dom (gset addr) mt) ∗
      "Hcancel_txn" ∷ txn_cfupd_cancel dinit γ' ∗
      "Hcancel_obj" ∷ wpc_crash_modality ⊤ mj (twophase_obj_cfupd_cancel γ γ' (dom (gset addr) mt))
    }}}
    {{{ ∃ γ' logm' mt',
       ⌜ dom (gset _) mt' = dom (gset _) mt ⌝ ∗
       ⌜γ.(jrnl_txn_names).(txn_kinds) = γ'.(jrnl_txn_names).(txn_kinds)⌝ ∗
       ⌜ map_Forall (mapsto_valid γ') mt' ⌝ ∗
      is_txn_durable γ' dinit logm' ∗
      "Hmapstos" ∷ ([∗ map] a ↦ obj ∈ mt',
        "Hdurable_mapsto" ∷ durable_mapsto_own γ' a obj ∗
        "Hjrnl_mapsto" ∷ jrnl_mapsto_own a obj
      ) ∗
      "%Hdomsize" ∷ ⌜ size mt' = JRNL_SIZE ⌝
    }}}.
  Proof.
    iIntros (HinvN HwalN Hvalids Φ Φc) "Hpre HΦ".
    iNamed "Hpre".
    iApply wpc_cfupd.
    wpc_apply (wpc_MkLog Njrnl with "Htxn_durable").
    1-2: solve_ndisj.
    iSplit.
    {
      iDestruct "HΦ" as "[HΦ _]".
      iIntros "H". iDestruct "H" as (γ' logm') "(Hdur&Hcase)".
      iDestruct "Hcase" as "[%|#Hcinv]".
      { subst. iModIntro. iApply "HΦ". iExists _, _, mt. by iFrame. }
      iDestruct (big_sepM_sep with "Hmapstos") as "(Hm1&Hm2)".
      rewrite /named.
      iMod (exchange_durable_mapsto with "[$Hcinv Hm1]") as "Hm1".
      { iApply (big_sepM_mono with "Hm1"). iIntros (???) "H".
        iDestruct "H" as "(?&?)". iFrame. }
      iModIntro. iApply "HΦ". iExists _, _, mt. iFrame.
      iSplit; first eauto.
      iDestruct "Hcinv" as "(?&%)".
      iSplit; first eauto.
      iSplit; first eauto.
      { iPureIntro. eapply map_Forall_impl; try eassumption.
        intros. eapply exchange_mapsto_valid; try eassumption. }
      iFrame "%".
      iApply big_sepM_sep. iFrame.
    }
    iModIntro.
    iIntros (? txnl) "
      (#Histxn&#Histxn_system&Htxn_cancel&#Htxn_cinv)".
    iApply ncfupd_wpc.
    iSplit.
    {
      iDestruct "HΦ" as "[HΦ _]".
      iModIntro.
      rewrite /txn_cfupd_cancel.
      rewrite own_discrete_elim.
      iMod "Htxn_cancel"; first by lia.
      iDestruct (big_sepM_sep with "Hmapstos") as "(Hm1&Hm2)".
      rewrite /named.
      iMod (exchange_durable_mapsto with "[Hm1]") as "Hm1".
      { iFrame "Htxn_cinv". iApply (big_sepM_mono with "Hm1"). iIntros (???) "H".
        iDestruct "H" as "(?&?)". iFrame. }
      iIntros "HC". iDestruct "Htxn_cancel" as ">Htxn_cancel".
      iDestruct "Htxn_cancel" as (?) "Htxn_cancel".
      iModIntro. iApply "HΦ". iExists _, _, mt. iFrame "Htxn_cancel".
      iSplit; first eauto.
      iDestruct "Htxn_cinv" as "(?&%)".
      iSplit; first eauto.
      iSplit; first eauto.
      { iPureIntro. eapply map_Forall_impl; try eassumption.
        intros. eapply exchange_mapsto_valid; try eassumption. }
      iFrame "%".
      iApply big_sepM_sep. iFrame.
    }
    iMod (twophase_init_locks with "Hpre Histxn_system Htxn_cinv Hmapstos") as "Hcrash".
    1-2: set_solver.
    {
      intros a Hin.
      apply elem_of_dom in Hin.
      destruct Hin as [obj Hacc].
      apply Hvalids in Hacc.
      destruct Hacc as (Hvalid&_&_).
      assumption.
    }
    iNamed.
    iModIntro.
    iApply (init_cancel_elim' _ _ _ _ _ _ _ mj Hlt with "Hlinvs").
    iIntros "Hlinvs".

    iCache with "HΦ Htxn_cancel".
    {
      iDestruct "HΦ" as "[HΦ _]".
      iIntros "Hcrash".
      rewrite /txn_cfupd_cancel. rewrite own_discrete_elim.
      iMod "Htxn_cancel"; first by lia.
      iMod "Hcrash".
      { lia. }
      iIntros "#HC".
      iDestruct "Htxn_cancel" as (?) ">Htxn_cancel".
      iModIntro.
      iApply "HΦ".
      iDestruct (big_sepM_dom with "Hcrash") as "H".
      iDestruct (big_sepS_exists_sepM with "H") as (mt' Hdom) "H".
      iExists _, _, mt'. iFrame "Htxn_cancel".
      iDestruct "Htxn_cinv" as "(?&%)".
      iSplit; first eauto.
      iSplit; first eauto.
      iSplit.
      { iIntros (i o Hin).
        iDestruct (big_sepM_lookup with "[$]") as "(?&?&$)"; eauto. }
      rewrite -Hdomsize. rewrite ?Map.map_size_dom.
      rewrite Hdom. iSplitR ""; last by eauto.
      iApply (big_sepM_mono with "H").
      iIntros (???) "($&$&_)".
    }
    wpc_frame.
    wp_apply (
      wp_MkLockMap _ (twophase_linv_flat jrnl_mapsto_own γ γ')
      with "[Hlinvs]"
    ).
    {
      iApply (big_sepS_impl with "Hlinvs").
      iIntros (addr_flat) "!> %Hin $".
    }
    iIntros (locksl ?) "#Hlocks".
    wp_apply wp_allocStruct; first by auto.
    iIntros (prel) "Hprel".
    iDestruct (struct_fields_split with "Hprel") as "(?&?&_)".
    iNamed.
    iMod (readonly_alloc_1 with "log") as "#Hpre.log".
    iMod (readonly_alloc_1 with "locks") as "#Hpre.locks".
    wp_pures.
    iIntros "!> [? H2]".
    iNamed.
    iIntros "Hwpc".

    iApply "HΦ".
    {
      iFrame "Htxn_cancel".
      iSplitR "Hwpc".
      {
        iFrame.
        iExists _, _, _.
        iFrame "#".
        iPureIntro.
        intros addr Hin.
        apply elem_of_dom in Hin.
        destruct Hin as [obj Hacc].
        apply Hvalids in Hacc.
        destruct Hacc as (Hvalid&_&_).
        assumption.
      }
      iApply (wpc_crash_modality_wand with "Hwpc").
      {
        iNamed 1.
        iModIntro. iIntros "HC". iMod ("Hcrash" with "[$]") as "Hcrash".
        iModIntro.
        iDestruct (big_sepM_dom with "Hcrash") as "H".
        iDestruct (big_sepS_exists_sepM with "H") as (mt' Hdom) "H".
        iExists mt'.
        iDestruct "Htxn_cinv" as "(_&%)".
        iSplit; first eauto.
        iSplit; first eauto.
        iSplit.
        { iIntros (i o Hin).
          iDestruct (big_sepM_lookup with "[$]") as "(?&?&$)"; eauto. }
        rewrite -Hdomsize. rewrite ?Map.map_size_dom.
        rewrite Hdom. iSplitR ""; last by eauto.
        iApply (big_sepM_mono with "H").
        iIntros (???) "($&$&_)".
      }
    }
  Qed.

  Theorem wp_Init N d j K `{LanguageCtx _ K} (vs: sval) :
    N ## invN →
    N ## invariant.walN →
    {{{
      "#Hspec_ctx" ∷ spec_ctx ∗
      "#Htwophase_inv" ∷ twophase_inv JRNL_SIZE ∗
      "Hj" ∷ j ⤇ (K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext) OpenOp vs))
    }}}
      Init (disk_val d) @ NotStuck; ⊤
    {{{
      (l: loc), RET #l;
      j ⤇ (K #true) ∗
      jrnl_open ∗
      ∃ γ γ' dinit (mt : gmap addr object),
       "Htwophase" ∷ is_twophase_pre l γ γ' dinit (dom (gset addr) mt)
    }}}.
  Proof.
    iIntros (HinvN HwalN (*Hvalids*) Φ) "Hpre HΦ".
    iNamed "Hpre".
    iDestruct "Htwophase_inv" as (γghost) "(Htwophase_inv&Hspec_crash_ctx)".
    iApply ncfupd_wp.
    iInv "Htwophase_inv" as "Hinv" "Hclo".
    rewrite /twophase_inv_inner.
    iDestruct "Hinv" as "[Hinv1|>Hinv3]"; last first.
    { iMod (jrnl_opened_open_false with "[$] [$] [$]") as %[].
      { solve_ndisj. } }
    iDestruct "Hinv1" as "(Hna&>Hclosed_frag&>Hghost_var)".
    iMod (ghost_step_jrnl_open with "[$] [$] [$]") as "(Hj&#Hopen)".
    { solve_ndisj. }
    iMod ("Hclo" with "[]").
    { iRight. iNext. iFrame "#Hopen". }
    iModIntro.
    rewrite /Init. wp_pure _.
    rewrite /twophase_na_crash_inv.
    iClear "Htwophase_inv".

    iApply (wpc_wp _ (S (S LVL)) _ _ _ True%I).
    iApply (wpc_crash_borrow_open_cancel with "Hna").
    { eauto. }
    iSplit; first done.
    iIntros "H". iNamed "H". iDestruct "H" as "(Hpre&H)". iNamed "H".
    iIntros (mj Hlt).
    wpc_apply (wpc_Init _ _ γ dinit logm with "[Hpre Htxn_durable Hmapstos] [HΦ Hj]"); try eassumption.
    { iFrame "Hpre". iSplitL "Htxn_durable".
      { iExact "Htxn_durable". }
      iFrame "Hmapstos".
      iFrame "#".
      eauto.
    }
    iSplit.
    * iIntros "H".
      iSplit; first done.
      iDestruct "H" as (??? Heq Heq' Hforall) "(Hdurable&Hmapstos)".
      iNamed.
      iExists _, _, _, _. iFrame.
      rewrite Heq Heq'. iFrame "#".
      eauto.
    * iNext. iIntros (γ' l) "H". iNamed "H".
      rewrite /txn_cfupd_cancel.
      iSplitL "Hcancel_obj Hcancel_txn".
      {
        iApply (wpc_crash_modality_intro_C). iIntros "#HC".
        iApply (wpc_crash_modality_wand with "Hcancel_obj").
        iIntros "Hobj".
        rewrite own_discrete_elim. iMod ("Hcancel_txn" with "[$]") as ">Htxn".
        iDestruct "Htxn" as (logm') "Htxn".
        iMod ("Hobj" with "[$]") as "Hobj".
        iDestruct "Hobj" as (mt'' Hdom Heqkinds Hforall) "Hmapstos".
        iExists _, _, _, _. iFrame.
        rewrite Hdom Heqkinds. iFrame "#Hdom".
        eauto.
      }
      iSplit; first done.
      iApply "HΦ".
      iFrame "Hj".
      iSplit; first by iFrame "Hopen".
      iExists _, _, _, _. by iFrame.
  Qed.
End proof.
