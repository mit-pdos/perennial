From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import map.impl list.impl list.list_slice slice.typed_slice.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang.ffi Require Import disk.
From Goose.github_com.mit_pdos.goose_nfsd Require Import txn twophase.
From Perennial.program_proof Require Import lockmap_proof.
From Perennial.program_proof Require Import twophase.op_wrappers.
From Perennial.program_proof Require Import addr.addr_proof buf.buf_proof txn.txn_proof.
From Perennial.program_proof Require Import buftxn.sep_buftxn_proof.
From Perennial.program_proof Require Import twophase.twophase_proof.
From Perennial.program_logic Require Import na_crash_inv.
From Perennial.goose_lang.lib.list Require Import list.
From Perennial.goose_lang Require Import spec_assert.

From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.program_proof Require Import proof_prelude.

Section proof.
  Context `{!buftxnG Σ}.
  Context `{!heapG Σ}.
  Context `{!lockmapG Σ}.
  Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp
           jrnl_spec_interp_adequacy.
  Context `{hRG: !refinement_heapG Σ}.
  Existing Instance jrnlG0.

  Notation spec_ext := jrnl_spec_ext.
  Notation sval := (@val (@spec_ext_op_field spec_ext)).

  Implicit Types (N: namespace).

  Definition val_of_obj o :=
    match o with
    | objBit b => #b
    | objBytes o => val_of_list ((λ u, LitV (LitByte u)) <$> o)
    end.

  Definition LVL := 100%nat.

  Definition bufObj_to_obj bufObj : obj :=
    match objData bufObj with
    | bufBit b => objBit b
    | bufInode data | bufBlock data => objBytes data
    end.

  Definition jrnl_mapsto_own a bufObj : iProp Σ :=
    "Hmapsto" ∷ jrnl_mapsto a 1 (bufObj_to_obj bufObj) ∗
    "Htok" ∷ jrnl_crash_tok a.

  Global Instance jrnl_mapsto_own_Timeless a bufObj:
    Timeless (jrnl_mapsto_own a bufObj).
  Proof. refine _. Qed.

  Global Instance jrnl_mapsto_own_Discretizable a bufObj:
    Discretizable (jrnl_mapsto_own a bufObj).
  Proof. refine _. Qed.

  Definition jrnl_maps_kinds_valid γ (σj1 σj2: jrnl_map) :=
    jrnlKinds σj1 = γ.(buftxn_txn_names).(txn_kinds) ∧
    jrnlKinds σj2 = γ.(buftxn_txn_names).(txn_kinds).

  Definition jrnl_maps_have_mt (mt_changed: gmap addr versioned_object) (σj1 σj2: jrnl_map) :=
    bufObj_to_obj <$> (committed <$> mt_changed) = jrnlData σj1 ∧
    bufObj_to_obj <$> (modified <$> mt_changed) = jrnlData σj2.

  Definition is_twophase_pre l (γ γ' : buftxn_names) dinit (objs_dom: gset addr) : iProp Σ :=
    ∃ (txnl locksl : loc) ghs,
      "#Hpre.txn" ∷ readonly (l ↦[TwoPhasePre.S :: "txn"] #txnl) ∗
      "#Hpre.locks" ∷ readonly (l ↦[TwoPhasePre.S :: "locks"] #locksl) ∗
      "#Histxn_system" ∷ is_txn_system Nbuftxn γ ∗
      "#Histxn" ∷ is_txn txnl γ.(buftxn_txn_names) dinit ∗
      "#HlockMap" ∷ is_lockMap locksl ghs (set_map addr2flat objs_dom)
        (twophase_linv_flat LVL jrnl_mapsto_own γ γ') ∗
      "#Hspec_ctx" ∷ spec_ctx ∗
      "#Hspec_crash_ctx" ∷ spec_crash_ctx jrnl_crash_ctx ∗
      "#Hjrnl_open" ∷ jrnl_open ∗
      "#Hjrnl_kinds_lb" ∷ jrnl_kinds γ.(buftxn_txn_names).(txn_kinds) ∗
      "#Hjrnl_dom" ∷ jrnl_dom objs_dom ∗
      "#Htxn_cinv" ∷ txn_cinv Nbuftxn γ γ' ∗
      "%Haddrs_valid" ∷ ⌜set_Forall valid_addr objs_dom⌝.

  Definition is_twophase_started l γ γ' dinit objs_dom j K e1 e2 : iProp Σ :=
    ∃ σj1 σj2 mt_changed (ls: sval),
      (* mark: do we need is_twophase_pre in here too? *)
      "Hj" ∷ j ⤇ K (Atomically ls e1) ∗
      "Htwophase" ∷ is_twophase_raw
        l γ γ' dinit LVL jrnl_mapsto_own objs_dom mt_changed ∗
      "#Hspec_ctx" ∷ spec_ctx ∗
      "#Hspec_crash_ctx" ∷ spec_crash_ctx jrnl_crash_ctx ∗
      "#Hjrnl_open" ∷ jrnl_open ∗
      "#Hjrnl_kinds_lb" ∷ jrnl_kinds γ.(buftxn_txn_names).(txn_kinds) ∗
      "#Hjrnl_dom" ∷ jrnl_dom objs_dom ∗
      "%Halways_steps" ∷ ⌜always_steps e1 σj1 e2 σj2⌝ ∗
      "%Hjrnl_maps_kinds" ∷ ⌜jrnl_maps_kinds_valid γ σj1 σj2⌝ ∗
      "%Hjrnl_maps_mt" ∷ ⌜jrnl_maps_have_mt mt_changed σj1 σj2⌝ ∗
      "%HLCtxt"∷ ⌜ LanguageCtx K ⌝.

  Definition is_twophase_releasable l γ γ' (objs_dom: gset addr) : iProp Σ :=
    ∃ locks_held mt_changed σj1 σj2,
      (* mark: do we need is_twophase_pre in here too? *)
      "Hlocks" ∷ is_twophase_locks
        l γ γ' LVL jrnl_mapsto_own (set_map addr2flat objs_dom) locks_held ∗
      "Hlinvs" ∷ ([∗ list] flat_a ∈ locks_held, (
        "Hlinv" ∷ twophase_linv_flat LVL jrnl_mapsto_own γ γ' flat_a
      )) ∗
      "%Hlocks_held" ∷ ⌜
        set_map addr2flat (dom (gset addr) mt_changed) =
        (list_to_set locks_held: gset u64)
      ⌝ ∗
      "%Hjrnl_maps_kinds" ∷ ⌜jrnl_maps_kinds_valid γ σj1 σj2⌝ ∗
      "%Hjrnl_maps_mt" ∷ ⌜jrnl_maps_have_mt mt_changed σj1 σj2⌝.

  Lemma objSz_bufObj_to_obj o :
    objSz (bufObj_to_obj o) = bufSz (objKind o).
  Proof.
    rewrite /bufObj_to_obj.
    destruct (objData o).
    - reflexivity.
    - rewrite /objSz vec_to_list_length //.
    - rewrite /objSz vec_to_list_length //.
  Qed.

  Lemma data_has_obj_wf data a o :
    data_has_obj data a o →
    length data ≤ block_bytes.
  Proof.
    intros Hdata.
    destruct o as [k [b|data'|data']].
    - rewrite /data_has_obj /= in Hdata.
      destruct Hdata as [bit [-> Hbit]].
      rewrite /= /block_bytes.
      lia.
    - rewrite /data_has_obj /= in Hdata.
      rewrite -Hdata vec_to_list_length /inode_bytes /block_bytes.
      lia.
    - rewrite /data_has_obj /= in Hdata.
      rewrite -Hdata vec_to_list_length.
      lia.
  Qed.

  Lemma is_twophase_wf_jrnl l γ γ' dinit k objs_dom mt_changed σj1 σj2 :
    jrnl_maps_kinds_valid γ σj1 σj2 →
    jrnl_maps_have_mt mt_changed σj1 σj2 →
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit k jrnl_mapsto_own objs_dom mt_changed -∗
    "%Hwf_jrnl1" ∷ ⌜wf_jrnl σj1⌝ ∗
    "%Hwf_jrnl1" ∷ ⌜wf_jrnl σj2⌝.
  Proof.
    iIntros (Hjrnl_maps_kinds Hjrnl_maps_mt) "?".
    iNamed.
    iDestruct (is_twophase_raw_get_mt_in_spec with "Htwophase")
      as "%Hmt_in_dom".
    iNamed "Htwophase".
    iPureIntro.
    rewrite /wf_jrnl /offsets_aligned /sizes_correct.
    destruct Hjrnl_maps_kinds as [-> ->].
    destruct Hjrnl_maps_mt as [<- <-].
    split.
    - split.
      + intros a Hin.
        apply elem_of_dom in Hin.
        destruct Hin as [obj Hin].
        rewrite !lookup_fmap in Hin.
        destruct (mt_changed !! a) as [vobj|] eqn:Hacc;
          last by inversion Hin.
        apply Hvalids in Hacc.
        destruct Hacc as (Haddr&Hoff&Hγ).
        eexists _.
        split; first by eassumption.
        assumption.
      + intros a obj Hin.
        rewrite !lookup_fmap in Hin.
        destruct (mt_changed !! a) as [vobj|] eqn:Hacc;
          last by inversion Hin.
        apply Hvalids in Hacc.
        destruct Hacc as (Haddr&Hoff&Hγ).
        inversion Hin as [Hobj].
        rewrite Hγ.
        eexists _.
        split; first by reflexivity.
        rewrite objSz_bufObj_to_obj //.
    - split.
      + intros a Hin.
        apply elem_of_dom in Hin.
        destruct Hin as [obj Hin].
        rewrite !lookup_fmap in Hin.
        destruct (mt_changed !! a) as [vobj|] eqn:Hacc;
          last by inversion Hin.
        apply Hvalids in Hacc.
        destruct Hacc as (Haddr&Hoff&Hγ).
        eexists _.
        split; first by eassumption.
        assumption.
      + intros a obj Hin.
        rewrite !lookup_fmap in Hin.
        destruct (mt_changed !! a) as [vobj|] eqn:Hacc;
          last by inversion Hin.
        apply Hvalids in Hacc.
        destruct Hacc as (Haddr&Hoff&Hγ).
        inversion Hin as [Hobj].
        rewrite Hγ.
        eexists _.
        split; first by reflexivity.
        rewrite objSz_bufObj_to_obj //.
  Qed.

  Global Instance log_heap_async_inhabited:
    Inhabited (log_heap.async (gmap addr object)).
  Proof.
    econstructor. refine (log_heap.Build_async ∅ []).
  Qed.

  Theorem wpc_Init N (d: loc) γ dinit logm mt :
    N ## invN →
    N ## invariant.walN →
    map_Forall (mapsto_valid γ) mt →
    {{{
      "Htxn_durable" ∷ is_txn_durable γ dinit logm ∗
      "Hmapstos" ∷ ([∗ map] a ↦ obj ∈ mt,
        "Hdurable_mapsto" ∷ durable_mapsto_own γ a obj ∗
        "Hjrnl_mapsto" ∷ jrnl_mapsto_own a obj
      ) ∗
      "#Hspec_ctx" ∷ spec_ctx ∗
      "#Hspec_crash_ctx" ∷ spec_crash_ctx jrnl_crash_ctx ∗
      "#Hjrnl_open" ∷ jrnl_open ∗
      "#Hjrnl_kinds_lb" ∷ jrnl_kinds γ.(buftxn_txn_names).(txn_kinds) ∗
      "#Hjrnl_dom" ∷ jrnl_dom (dom _ mt)
    }}}
      Init #d @ S (S LVL); ⊤
    {{{
      γ' (l: loc), RET #l;
      "Htwophase" ∷ is_twophase_pre l γ γ' dinit (dom (gset addr) mt)
    }}}
    {{{ ∃ γ' logm' mt', ⌜ dom (gset _) mt' = dom (gset _) mt ⌝ ∗
      is_txn_durable γ' dinit logm' ∗
      "Hmapstos" ∷ ([∗ map] a ↦ obj ∈ mt',
        "Hdurable_mapsto" ∷ durable_mapsto_own γ' a obj ∗
        "Hjrnl_mapsto" ∷ jrnl_mapsto_own a obj
      )
    }}}.
  Proof.
    iIntros (HinvN HwalN Hvalids Φ Φc) "Hpre HΦ".
    iNamed "Hpre".
    wpc_call.
    {
      iExists _, _, mt.
      by iFrame.
    }
    iApply wpc_cfupd.
    wpc_apply (wpc_MkTxn Nbuftxn with "Htxn_durable").
    1-2: solve_ndisj.
    iSplit.
    {
      iDestruct "HΦ" as "[HΦ _]".
      iModIntro.
      iIntros "H". iDestruct "H" as (γ' logm') "(Hdur&Hcase)".
      iDestruct "Hcase" as "[%|Hcinv]".
      { subst. iModIntro. iApply "HΦ". iExists _, _, mt. by iFrame. }
      iDestruct (big_sepM_sep with "Hmapstos") as "(Hm1&Hm2)".
      rewrite /named.
      iMod (exchange_durable_mapsto with "[$Hcinv Hm1]") as "Hm1".
      { iApply (big_sepM_mono with "Hm1"). iIntros (???) "H".
        iDestruct "H" as "(?&?)". iFrame. }
      iModIntro. iApply "HΦ". iExists _, _, mt. iFrame.
      iSplit; first eauto.
      iApply big_sepM_sep. iFrame.
    }
    iModIntro.
    iIntros (? txnl) "
      (#Histxn&#Histxn_system&Htxn_cancel&#Htxn_cinv)".
    iApply ncfupd_wpc.
    iSplit.
    {
      iDestruct "HΦ" as "[HΦ _]".
      iModIntro. iModIntro.
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
      iApply big_sepM_sep. iFrame.
    }
    iMod (twophase_init_locks with "Histxn_system Htxn_cinv Hmapstos") as "(Hlinvs&Hcrash)".
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
    iCache with "HΦ Htxn_cancel Hcrash".
    {
      iDestruct "HΦ" as "[HΦ _]".
      iModIntro.
      iMod "Htxn_cancel"; first by lia.
      iMod "Hcrash".
      eauto.
      iIntros "#HC".
      iDestruct "Htxn_cancel" as (?) ">Htxn_cancel".
      iModIntro.
      iApply "HΦ".
      iDestruct (big_sepM_dom with "Hcrash") as "H".
      iDestruct (big_sepS_exists_sepM with "H") as (mt' Hdom) "H".
      iExists _, _, mt'. iFrame "Htxn_cancel".
      iFrame. eauto.
    }
    wpc_frame.
    wp_apply (
      wp_MkLockMap _ (twophase_linv_flat _ jrnl_mapsto_own γ γ')
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
    iMod (readonly_alloc_1 with "txn") as "#Hpre.txn".
    iMod (readonly_alloc_1 with "locks") as "#Hpre.locks".
    wp_pures.
    iIntros "[? ?]".
    iNamed.

    iApply "HΦ".
    iExists _, _, _.
    iFrame "#".
    iPureIntro.
    intros addr Hin.
    apply elem_of_dom in Hin.
    destruct Hin as [obj Hacc].
    apply Hvalids in Hacc.
    destruct Hacc as (Hvalid&_&_).
    assumption.
  Qed.

  Lemma map_Forall_exists {A B} `{Countable K} (m: gmap K A) P :
    map_Forall (λ a x, ∃ y, P a x y) m →
    ∃ (m': gmap K B),
      dom (gset K) m = dom (gset K) m' ∧
      map_Forall (λ a xy, P a xy.1 xy.2) (map_zip m m').
  Proof.
    induction m as [|a x m_sub] using map_ind.
    {
      intros _.
      exists ∅.
      split; first by rewrite !dom_empty_L //.
      intros k x Hacc.
      rewrite map_zip_lookup_none_1 in Hacc; last by auto.
      inversion Hacc.
    }
    intros Hex.
    apply map_Forall_insert_1_1 in Hex as Hex1.
    apply map_Forall_insert_1_2 in Hex as Hex2; last by assumption.
    apply IHm in Hex2.
    destruct Hex1 as [y Hex1].
    destruct Hex2 as [m'_sub [Hdoms Hm'_sub]].
    exists (<[a:=y]>m'_sub).
    split; first by rewrite !dom_insert_L -Hdoms //.
    rewrite map_zip_insert.
    apply map_Forall_insert_2; assumption.
  Qed.

  Lemma map_Forall_zip_snd {A B} `{Countable K} (m1: gmap K A) (m2: gmap K B) P :
    dom (gset K) m2 ⊆ dom (gset K) m1 →
    map_Forall (λ a xy, P a xy.2) (map_zip m1 m2) →
    map_Forall P m2.
  Proof.
    intros Hdoms Hforall k y Hacc.
    apply mk_is_Some in Hacc as Hacc'.
    apply elem_of_dom in Hacc'.
    apply (iffLR (elem_of_subseteq _ _) Hdoms k) in Hacc'.
    apply elem_of_dom in Hacc'.
    destruct Hacc' as [x Hacc'].
    pose proof (map_zip_lookup_some _ _ _ _ _ Hacc' Hacc) as Hacc_zip.
    apply Hforall in Hacc_zip.
    assumption.
  Qed.

  Theorem wp_TwoPhase__Begin' N prel γ γ' dinit objs_dom j K {HCTX: LanguageCtx K} (ls: sval) e1 :
    {{{
      "Htwophase" ∷ is_twophase_pre prel γ γ' dinit objs_dom ∗
      "Hatom" ∷ j ⤇ K (Atomically ls e1)
    }}}
      Begin #prel
    {{{ tphl, RET #tphl;
        is_twophase_started tphl γ γ' dinit objs_dom j K e1 e1 }}}.
  Proof.
    iIntros (Φ) "Hpre HΦ".
    iNamed "Hpre".
    iNamed "Htwophase".
    wp_apply (wp_TwoPhase__Begin_raw with "[$]"); [ rewrite /LVL; lia | assumption |..].
    iIntros (?) "?".
    iNamed.

    iApply "HΦ".
    iExists (∅, _), (∅, _), _, _.
    iFrame "∗ #".
    iPureIntro.
    split.
    2: {
      split; first by rewrite /jrnl_maps_kinds_valid //.
      rewrite /jrnl_maps_have_mt !fmap_empty //.
    }
    apply always_steps_refl.
    rewrite /wf_jrnl /offsets_aligned dom_empty_L //.
  Qed.

  Theorem wp_TwoPhase__CommitNoRelease' l γ γ' dinit objs_dom j K e1 v :
    {{{ is_twophase_started l γ γ' dinit objs_dom j K e1 (SOMEV v) }}}
      TwoPhase__CommitNoRelease #l
    {{{ (ok:bool), RET #ok;
        "Htwophase" ∷ is_twophase_releasable l γ γ' objs_dom ∗
        "Hj" ∷ (
          if ok then
            j ⤇ K (SOMEV v)
          else
            j ⤇ K NONEV
        )
    }}}.
  Proof.
    iIntros (Φ) "Htwophase HΦ".
    iNamed "Htwophase".
    iDestruct (is_twophase_raw_get_valid with "Htwophase") as "%Hvalids".
    iApply wp_ncfupd.
    unshelve (wp_apply (
      wp_TwoPhase__CommitNoRelease_raw
      _ _ _ _ _ _ _ _
      (j ⤇ K (SOMEV v))%I
      (|NC={⊤}=> j ⤇ K NONEV)%I
      with "[$Htwophase Hj]"
    )).
    1-2: refine _.
    {
      iSplit.
      - iIntros "!> ?".
        iNamed.
        iAssert (
          [∗ map] a ↦ o ∈ jrnlData σj1,
            "Hmapsto" ∷ jrnl_mapsto a 1 o ∗
            "Htok" ∷ jrnl_crash_tok a
        )%I with "[Hcommitted]" as "Hcommitted".
        {
          destruct Hjrnl_maps_mt as [<- _].
          rewrite !big_sepM_fmap //.
        }
        iDestruct (big_sepM_sep with "Hcommitted") as "[Hmapstos Htoks]".
        destruct Hjrnl_maps_kinds as [<- _].
        iDestruct (
          ghost_step_jrnl_atomically_crash
          with "Hspec_crash_ctx Hmapstos Htoks Hjrnl_kinds_lb Hjrnl_open Hj"
        ) as "H"; (* "> [Hmapstos Htoks]" *) [eassumption|set_solver|].
        iMod (cfupd_weaken_all with "H") as "[Hmapstos Htoks]".
        { lia. }
        { auto. }
        iModIntro.
        iApply big_sepM_sep.
        destruct Hjrnl_maps_mt as [<- <-].
        rewrite !big_sepM_fmap.
        iFrame.
      - iIntros "!> ?".
        iNamed.
        iAssert (
          [∗ map] a ↦ o ∈ jrnlData σj1,
            "Hmapsto" ∷ jrnl_mapsto a 1 o ∗
            "Htok" ∷ jrnl_crash_tok a
        )%I with "[Hcommitted]" as "Hcommitted".
        {
          destruct Hjrnl_maps_mt as [<- _].
          rewrite !big_sepM_fmap //.
        }
        iDestruct (big_sepM_sep with "Hcommitted") as "[Hmapstos Htoks]".
        destruct Hjrnl_maps_kinds as [<- _].
        iSplit.
        2: {
          iFrame.
          iSplitR "Hj"; last first.
          { iMod (ghost_step_jrnl_atomically_abort with "[$] [$] [$]") as "$"; auto. }
          iApply big_sepM_sep.
          destruct Hjrnl_maps_mt as [<- _].
          rewrite !big_sepM_fmap.
          iFrame.
        }
        iDestruct (
          ghost_step_jrnl_atomically
          with "Hspec_ctx Hmapstos Hjrnl_kinds_lb Hjrnl_open Hj"
        ) as "> [Hj Hmapstos]"; [eassumption|set_solver|].
        iModIntro.
        iFrame.
        destruct Hjrnl_maps_mt as [<- <-].
        rewrite !big_sepM_fmap.
        iApply big_sepM_sep.
        iFrame.
    }
    iIntros (??) "Hpost".
    iNamed "Hpost".
    iApply "HΦ".
    iSplitL "Hlocks Hlinvs".
    {
      iExists _, _, _, _.
      iDestruct (is_twophase_locks_get_pures with "Hlocks")
        as "#Hlocks_pures".
      iNamed "Hlocks_pures".
      iFrame "∗ %".
      rewrite -big_sepS_list_to_set; last by assumption.
      rewrite -Hlocks_held.
      iApply big_sepS_set_map; last by iFrame.

      intros a1 a2 Hacc1 Hacc2 Heq.
      apply elem_of_dom in Hacc1.
      apply elem_of_dom in Hacc2.
      destruct Hacc1 as [vo1 Hacc1].
      destruct Hacc2 as [vo2 Hacc2].
      apply Hvalids in Hacc1.
      apply Hvalids in Hacc2.
      rewrite /mapsto_valid in Hacc1.
      rewrite /mapsto_valid in Hacc2.
      apply addr2flat_eq; intuition.
    }
    destruct ok; first by iFrame.
    iMod "HQ"; eauto.
  Qed.

  Lemma na_crash_inv_open_modify_ncfupd_sepM `{Countable A} {B} k E (P: A → B → iProp Σ) Q Q' R m:
    ([∗ map] i ↦ x ∈ m,
      na_crash_inv (S k) (Q i x) (P i x)
    ) -∗
    (
      ([∗ map] i ↦ x ∈ m,
        ▷ (Q i x)
      ) -∗
      |NC={E}=> □ ([∗ map] i ↦ x ∈ m,
        (
          ▷ (Q' i x) -∗
          |C={⊤}_k=> ▷ (P i x)
        )
      ) ∗
      ([∗ map] i ↦ x ∈ m,
        ▷ (Q' i x)
      ) ∗
      R
    ) -∗
    |NC={E}=>
    R ∗
    ([∗ map] i ↦ x ∈ m,
      na_crash_inv (S k) (Q' i x) (P i x)
    ).
  Proof.
    revert R.
    induction m as [|i x m] using map_ind.
    {
      iIntros (?) "_ Hrestore".
      iDestruct ("Hrestore" with "[]") as "> (_&_&$)";
        first by (iApply big_sepM_empty; trivial).
      iApply big_sepM_empty; trivial.
    }
    iIntros (?) "Hcrash_invs Hrestores".
    iDestruct (big_sepM_insert with "Hcrash_invs")
      as "[Hcrash_inv Hcrash_invs]";
      first by assumption.
    iDestruct (
      IHm
      (
        na_crash_inv (S k) (Q' i x) (P i x) ∗
        R
      )%I
      with "Hcrash_invs [Hrestores Hcrash_inv]"
    ) as "> [[Hcrash_inv HR] Hcrash_invs]".
    {
      iIntros "HQs".
      iDestruct (
        na_crash_inv_open_modify_ncfupd _ _ _ _ _
        (
          ([∗ map] i↦x ∈ m, ▷ Q' i x) ∗
          □ ([∗ map] i↦x ∈ m, (▷ Q' i x -∗ |C={⊤}_k=> ▷ P i x)) ∗
          R
        )%I
        with "Hcrash_inv [Hrestores HQs]"
      ) as "> [(HQ's&#Hstatuses&HR) Hcrash_inv]".
      {
        iIntros "HQ".
        iDestruct ("Hrestores" with "[HQs HQ]") as "> (#Hstatuses&HQ's&HR)".
        {
          iApply big_sepM_insert; first by assumption.
          iFrame.
        }
        iDestruct (big_sepM_insert with "HQ's")
          as "[HQ' HQ's]";
          first by assumption.
        iDestruct (big_sepM_insert with "Hstatuses")
          as "[Hstatus Hstatuses']";
          first by assumption.
        iFrame "∗ #".
        trivial.
      }
      iFrame.
      trivial.
    }
    iModIntro.
    iFrame.
    iApply big_sepM_insert; first by assumption.
    iFrame.
  Qed.

  Lemma na_crash_inv_status_wand_sepM {A} `{Countable K} (m: gmap K A) k Q P :
    ([∗ map] i ↦ x ∈ m, na_crash_inv k (Q i x) (P i x)) -∗
    □ (
      [∗ map] i ↦ x ∈ m,
      ▷ Q i x -∗
     |C={⊤}_Init.Nat.pred k=>
      ▷ P i x
    ).
  Proof.
    iInduction m as [|i x m] "IH" using map_ind.
    {
      iIntros "_ !>".
      iApply big_sepM_empty.
      trivial.
    }
    iIntros "Hcrash_invs".
    iDestruct (big_sepM_insert with "Hcrash_invs")
      as "[Hcrash_inv Hcrash_invs]";
      first by assumption.
    iDestruct ("IH" with "Hcrash_invs") as "#Hstatuses".
    iDestruct (na_crash_inv_status_wand with "Hcrash_inv") as "#Hstatus".
    iModIntro.
    iApply big_sepM_insert; first by assumption.
    iFrame "#".
  Qed.

  Theorem twophase_started_abort l γ γ' dinit objs_dom j K e1 e2 :
    is_twophase_started l γ γ' dinit objs_dom j K e1 e2 -∗
    |NC={⊤}=> is_twophase_releasable l γ γ' objs_dom ∗
              j ⤇ K NONEV.
  Proof.
    iIntros "Htwophase".
    iNamed "Htwophase".
    iNamed "Htwophase".
    iMod (ghost_step_jrnl_atomically_abort with "[$] [$] [$]") as "$"; auto.
    iExists _, _, _, _.
    iDestruct (is_twophase_locks_get_pures with "Hlocks")
      as "#Hlocks_pures".
    iNamed "Hlocks_pures".
    iFrame "∗ %".
    rewrite -big_sepS_list_to_set; last by assumption.
    rewrite -Hlocks_held.
    iNamed "Hbuftxn".
    iDestruct (na_crash_inv_status_wand_sepM with "Hcrash_invs") as
      "#Hstatuses".
    iDestruct (
      na_crash_inv_open_modify_ncfupd_sepM _ _ _ _
      (λ a vobj,
        twophase_pre_crash_inv_pred jrnl_mapsto_own γ a (committed vobj)
      )
      (
        [∗ map] a ↦ vobj ∈ mt_changed,
          modify_token γ a
      )%I
      with
      "Hcrash_invs [Hbuftxn_mem Hbuftxn_durable_frag]"
    ) as "> [Htoks Hcrash_invs]".
    {
      iIntros "Hpreds".
      iApply big_sepM_later_2 in "Hpreds".
      iMod "Hpreds".
      iDestruct (big_sepM_sep with "Hpreds") as "[Hjrnl_mapstos Hpreds]".
      iDestruct (big_sepM_sep with "Hpreds")
        as "[Hdurable_mapstos %Hcommitted_valids]".
      iApply big_sepM_fmap in "Hdurable_mapstos".
      iDestruct (
        is_buftxn_to_old_pred' with
        "Hbuftxn_mem Hbuftxn_durable_frag Hdurable_mapstos"
      ) as "?".
      iNamed.
      iApply (big_sepM_fmap committed) in "Hold_vals".
      iDestruct (big_sepM_sep with "Hold_vals")
        as "[Htokens Hdurable_mapstos]".
      iModIntro.
      iFrame "∗ #".
      iDestruct (big_sepM_sep with "[$Hdurable_mapstos $Hjrnl_mapstos]")
        as "Hpreds".
      iApply (big_sepM_impl with "Hpreds").
      iIntros (a vobj) "!> %Hacc [Hdurable_mapsto Hjrnl_mapsto] !>".
      iFrame.
      iPureIntro.
      apply Hcommitted_valids.
      assumption.
    }
    iDestruct (big_sepM_sep with "[$Htoks $Hcrash_invs]") as "Hcrash_invs".
    iModIntro.
    iApply big_sepS_set_map.
    {
      intros a1 a2 Hacc1 Hacc2 Heq.
      apply elem_of_dom in Hacc1.
      apply elem_of_dom in Hacc2.
      destruct Hacc1 as [vo1 Hacc1].
      destruct Hacc2 as [vo2 Hacc2].
      apply Hvalids in Hacc1.
      apply Hvalids in Hacc2.
      rewrite /mapsto_valid in Hacc1.
      rewrite /mapsto_valid in Hacc2.
      apply addr2flat_eq; intuition.
    }
    iApply big_sepM_dom.
    iApply (big_sepM_mono with "Hcrash_invs").
    iIntros (a vobj Hacc) "[Htok Hcrash_inv]".
    iExists _.
    iSplit; last by trivial.
    iExists _.
    iFrame.
    iPureIntro.
    apply Hvalids in Hacc.
    rewrite /mapsto_valid in Hacc.
    rewrite /mapsto_valid //.
  Qed.

  Theorem wp_TwoPhase__ReleaseAll' l γ γ' objs_dom :
    {{{ is_twophase_releasable l γ γ' objs_dom }}}
      TwoPhase__ReleaseAll #l
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Htwophase HΦ".
    iNamed "Htwophase".
    wp_apply (wp_TwoPhase__ReleaseAll with "[$]").
    iApply "HΦ".
    trivial.
  Qed.

  Lemma wp_SliceToListFrom data_s t q data (from: nat) :
    from ≤ length data →
    length data < 2^64 →
    {{{
      "Hslice" ∷ is_slice data_s t q data
    }}}
      SliceToListFrom t (slice_val data_s) #from
    {{{ RET (val_of_list (drop from data));
      True
    }}}.
  Proof.
    iLöb as "IH" forall (from).
    iIntros (Hbound Hwf Φ) "Hpre HΦ".
    iNamed "Hpre".
    wp_call.
    wp_apply wp_slice_len.
    iDestruct (is_slice_sz with "Hslice") as "%Hsz".
    wp_let.
    wp_if_destruct.
    2: {
      assert (from = length data)%nat as -> by (revert Heqb; word).
      rewrite drop_all /=.
      iApply "HΦ".
      trivial.
    }
    assert (from < length data)%nat as Hbound' by (revert Heqb; word).
    apply list_lookup_lt in Hbound' as Hacc.
    destruct Hacc as [x Hacc].
    iDestruct (is_slice_small_read with "Hslice") as "[Hslice Hrestore]".
    wp_apply (wp_SliceGet with "[$Hslice]").
    {
      iPureIntro.
      word_cleanup.
      rewrite Nat2Z.id.
      apply Hacc.
    }
    iIntros "[Hslice %Hty]".
    iApply "Hrestore" in "Hslice".
    wp_pures.
    replace (LitInt (word.add from 1)) with (LitInt (S from))%nat
      by (f_equal; word).
    wp_apply ("IH" with "[] [] Hslice");
      [iPureIntro; lia|trivial|].
    wp_pures.
    apply drop_S in Hacc.
    rewrite Hacc /=.
    iApply "HΦ".
    trivial.
  Qed.

  Lemma wp_SliceToList data_s t q data :
    length data < 2^64 →
    {{{
      "Hslice" ∷ is_slice data_s t q data
    }}}
      SliceToList t (slice_val data_s)
    {{{ RET (val_of_list data);
      True
    }}}.
  Proof.
    iIntros (Hwf Φ) "Hpre HΦ".
    iNamed "Hpre".
    wp_call.
    wp_apply (wp_SliceToListFrom with "Hslice");
      [lia|assumption|].
    iApply "HΦ".
    trivial.
  Qed.

  Lemma wp_ListToSliceApp data1_s t data1 data2 :
    has_zero t →
    length data1 + length data2 < 2^64 →
    Forall (λ v, val_ty v t) data2 →
    {{{
      "Hslice" ∷ is_slice data1_s t 1 data1
    }}}
      ListToSliceApp t (val_of_list data2) (slice_val data1_s)
    {{{ data_s, RET (slice_val data_s);
      "Hslice" ∷ is_slice data_s t 1 (data1 ++ data2)
    }}}.
  Proof.
    iLöb as "IH" forall (data1_s data1 data2).
    iIntros (Ht Hwf Hty Φ) "Hpre HΦ".
    iNamed "Hpre".
    wp_call.
    destruct data2 as [|x data2].
    {
      rewrite app_nil_r /ListMatch.
      wp_pures.
      iApply "HΦ".
      iFrame.
    }
    simpl in Hwf.
    rewrite /ListMatch.
    wp_pures.
    wp_apply (wp_SliceAppend with "[$Hslice]"); first by assumption.
    {
      apply Forall_cons_1 in Hty as [Hty _].
      iPureIntro.
      assumption.
    }
    iIntros (s') "Hslice".
    wp_pures.
    wp_apply ("IH" with "[] [] [] Hslice").
    1: iPureIntro; assumption.
    1: iPureIntro; rewrite app_length /=; lia.
    1: iPureIntro; apply Forall_cons_1 in Hty as [_ Hty]; assumption.
    iIntros (?) "?".
    iNamed.
    iApply "HΦ".
    rewrite -app_assoc /=.
    iFrame.
  Qed.

  Lemma wp_ListToSlice t data :
    has_zero t →
    length data < 2^64 →
    Forall (λ v, val_ty v t) data →
    {{{
      True
    }}}
      ListToSlice t (val_of_list data)
    {{{ data_s, RET (slice_val data_s);
      "Hslice" ∷ is_slice data_s t 1 data
    }}}.
  Proof.
    iIntros (Ht Hwf Hty Φ) "_ HΦ".
    wp_call.
    wp_apply wp_new_slice; first by assumption.
    iIntros (s) "Hslice".
    wp_apply (wp_ListToSliceApp with "Hslice");
      [assumption|rewrite replicate_length; word|assumption|].
    iIntros (?) "?".
    iNamed.
    iApply "HΦ".
    rewrite replicate_0 app_nil_l //.
  Qed.

  Lemma data_has_obj_not_bit data a bufObj :
    objKind bufObj ≠ KindBit →
    data_has_obj data a bufObj →
    objBytes data = bufObj_to_obj bufObj.
  Proof.
    intros Hnot_bit Hdata.
    destruct bufObj as [k [b|data'|data']].
    - contradiction.
    - rewrite /data_has_obj /= in Hdata.
      rewrite -Hdata //.
    - rewrite /data_has_obj /= in Hdata.
      rewrite -Hdata //.
  Qed.

  Lemma val_of_obj_data_not_bit data a o :
    objKind o ≠ KindBit →
    data_has_obj data a o →
    val_of_obj (bufObj_to_obj o) = val_of_list (list.untype data).
  Proof.
    intros Hnot_bit Hdata.
    erewrite <- data_has_obj_not_bit.
    2-3: eassumption.
    reflexivity.
  Qed.


  Lemma obj_to_bufObj_exists o k :
    objSz o = bufSz k →
    ∃ bufObj, o = bufObj_to_obj bufObj ∧ objKind bufObj = k.
  Proof.
    intros Hsz.
    rewrite /objSz /bufSz in Hsz.
    destruct k.
    - destruct o as [b|data]; last by lia.
      exists (existT _ (bufBit b)).
      intuition.
    - destruct o as [b|data]; first by lia.
      exists (existT _ (bufInode (list_to_inode_buf data))).
      rewrite /bufObj_to_obj /= list_to_inode_buf_to_list //.
      lia.
    - destruct o as [b|data]; first by lia.
      exists (existT _ (bufBlock (disk_lib.list_to_block data))).
      rewrite /bufObj_to_obj /= disk_lib.list_to_block_to_list //.
      rewrite /block_bytes in Hsz.
      lia.
  Qed.

  Lemma data_has_obj_exists_not_bit bufObj :
    objKind bufObj ≠ KindBit →
    ∃ data a, data_has_obj data a bufObj.
  Proof.
    intros Hnot_bit.
    destruct bufObj as [k [b|data|data]].
    - contradiction.
    - eexists data, (U64 0, U64 0).
      rewrite /data_has_obj //.
    - eexists data, (U64 0, U64 0).
      rewrite /data_has_obj //.
  Qed.

  Lemma data_has_obj_change_addr_not_bit data a a' o :
    objKind o ≠ KindBit →
    data_has_obj data a o →
    data_has_obj data a' o.
  Proof.
    intros Hnot_bit Hdata.
    destruct o as [k [b|data'|data']].
    - contradiction.
    - trivial.
    - trivial.
  Qed.

  Lemma twophase_started_ub_det' l γ γ' dinit objs_dom E j K0 K
        `{Hctx: LanguageCtx'
          (ext := @spec_ext_op_field _)
          (ffi := (spec_ffi_model_field))
          (ffi_semantics := (spec_ext_semantics_field))
          K} e0 e :
    nclose sN ⊆ E →
    is_twophase_started l γ γ' dinit objs_dom j K0 e0 (K e)
    -∗ |NC={E}=>
      ∃ σj1 σj2 mt_changed (ls: sval),
        "Hj" ∷ j ⤇ K0 (Atomically ls e0) ∗
        "Htwophase" ∷ is_twophase_raw
          l γ γ' dinit LVL jrnl_mapsto_own objs_dom mt_changed ∗
        "#Hspec_ctx" ∷ spec_ctx ∗
        "#Hspec_crash_ctx" ∷ spec_crash_ctx jrnl_crash_ctx ∗
        "#Hjrnl_open" ∷ jrnl_open ∗
        "#Hjrnl_kinds_lb" ∷ jrnl_kinds γ.(buftxn_txn_names).(txn_kinds) ∗
        "%Halways_steps" ∷ ⌜always_steps e0 σj1 (K e) σj2⌝ ∗
        "%Hjrnl_maps_kinds" ∷ ⌜jrnl_maps_kinds_valid γ σj1 σj2⌝ ∗
        "%Hjrnl_maps_mt" ∷ ⌜jrnl_maps_have_mt mt_changed σj1 σj2⌝ ∗
        "%HLCtxt"∷ ⌜ LanguageCtx K0 ⌝ ∗
        "#Hjrnl_dom" ∷ jrnl_dom objs_dom ∗
        "%Hnotstuck" ∷ ⌜ (∃ s g, jrnl_sub_state σj2 s ∧
         dom (gset _) (jrnlData (get_jrnl s.(world))) = objs_dom ∧
         ¬ stuck' (K e) s g) ⌝.
  Proof.
    iIntros (?). iNamed 1.
    iNamed "Htwophase".
    iDestruct (na_crash_inv_status_wand_sepM with "Hcrash_invs") as
      "#Hstatuses".
    iDestruct (
      na_crash_inv_open_modify_ncfupd_sepM _ _ _ _
      (λ a vobj,
        twophase_pre_crash_inv_pred jrnl_mapsto_own γ a (committed vobj)
      )
      (
        "Hj" ∷ j ⤇ K0 (Atomically ls e0) ∗
        "%Hnotstuck" ∷ ⌜∃ s g,
          jrnl_sub_state σj2 s ∧
          dom (gset addr) (jrnlData (get_jrnl s.(world))) =
            objs_dom ∧ ¬ stuck' (K e) s g
        ⌝
      )%I
      with
      "Hcrash_invs [Hj]"
    ) as "> [HR Hcrash_invs]".
    {
      iIntros "Hpreds".
      iApply big_sepM_later_2 in "Hpreds".
      iMod "Hpreds".
      iDestruct (big_sepM_sep with "Hpreds") as "(Hjrnl_mapstos&Hpreds)".
      iDestruct (big_sepM_sep with "Hpreds") as "(Hdurables&%Hvalids_c)".
      iDestruct (big_sepM_sep with "Hjrnl_mapstos")
        as "(Hjrnl_mapstos&Htoks)".
      iMod (
        ghost_step_jrnl_atomically_ub'
        with "Hspec_ctx [Hjrnl_mapstos] [] [$] Hjrnl_open Hj"
      ) as "(%Hnotstuck&Hj&Hjrnl_mapstos)".
      1-2: eassumption.
      {
        destruct Hjrnl_maps_mt as [<- _].
        rewrite !big_sepM_fmap //.
      }
      { destruct Hjrnl_maps_kinds as (->&_); eauto. }
      iModIntro.
      iFrame "∗ # %".
      destruct Hjrnl_maps_mt as [<- _].
      rewrite !big_sepM_fmap //.
      iDestruct (big_sepM_sep with "[$Htoks $Hdurables]") as "Hpreds".
      iDestruct (big_sepM_sep with "[$Hpreds $Hjrnl_mapstos]") as "Hpreds".
      iApply (big_sepM_mono with "Hpreds").
      iIntros (a vobj Hacc) "[[Htok Hdurable] Hcrash_inv] !>".
      iFrame.
      iPureIntro.
      apply Hvalids in Hacc.
      rewrite /mapsto_valid in Hacc.
      rewrite /mapsto_valid //.
    }
    iNamed "HR".

    iModIntro.
    iExists _, _, _, _.
    iFrame "Hj".
    iSplit.
    {
      iExists _.
      iFrame "∗ # %".
    }
    by iFrame "# %".
  Qed.


  Lemma twophase_started_ub_det l γ γ' dinit objs_dom E j K0 K
        `{Hctx: LanguageCtx'
          (ext := @spec_ext_op_field _)
          (ffi := (spec_ffi_model_field))
          (ffi_semantics := (spec_ext_semantics_field))
          K} e0 e :
    nclose sN ⊆ E →
    (∀ s g, stuck' e s g) →
    is_twophase_started l γ γ' dinit objs_dom j K0 e0 (K e)
    -∗ |NC={E}=> False.
  Proof.
    iIntros. iMod (twophase_started_ub_det' with "[$]") as "H".
    { eauto. }
    iNamed "H".
    iExFalso.
    iPureIntro.
    destruct Hnotstuck as (s&g&Hsub&Hdom&Hnstuck).
    eapply Hnstuck.
    eapply stuck'_fill; eauto.
  Qed.

  Theorem wp_TwoPhase__ReadBuf' l γ γ' dinit objs_dom j K0 K
          {Hctx: LanguageCtx'
            (ext := @spec_ext_op_field _)
            (ffi := (spec_ffi_model_field))
            (ffi_semantics := (spec_ext_semantics_field))
            K} e1 a (sz: u64) :
    {{{
      is_twophase_started l γ γ' dinit objs_dom j K0 e1
        (K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
          ReadBufOp (PairV (addr2val' a) #sz)))
    }}}
      TwoPhase__ReadBuf' #l (addr2val a, #sz)
    {{{ data, RET (val_of_obj (objBytes data));
        is_twophase_started l γ γ' dinit objs_dom j K0 e1
          (K (val_of_obj' (objBytes data)))
    }}}.
  Proof.
    iIntros (Φ) "Htwophase HΦ".
    iMod (twophase_started_ub_det' with "[$]") as "Htwophase".
    { auto. }
    iNamed "Htwophase".
    iDestruct (is_twophase_wf_jrnl with "Htwophase") as "%Hwf_jrnl";
      [eassumption|eassumption|].
    rewrite /TwoPhase__ReadBuf'.


    destruct Hnotstuck as (s&g&Hsub&Hdom&Hnotstuck).
    apply not_stuck'_ReadBuf_inv in Hnotstuck
      as (σj&k&Hopen&Hlookup1&Hlookup2&Hsz&Hk_not_bit);
      last done.
    assert (Ha_in_dom: a ∈ objs_dom).
    { rewrite -Hdom. apply elem_of_dom. rewrite Hopen => //=. }
    assert (Hk: γ.(buftxn_txn_names).(txn_kinds) !! a.(addrBlock) = Some k).
    { destruct Hjrnl_maps_kinds as (_&<-).
      destruct Hsub as (?&Hs_eq&?&?).
      rewrite Hs_eq in Hopen. inversion Hopen; subst. rewrite -Hlookup2. f_equal.
      eauto.
    }


    wp_apply (wp_TwoPhase__ReadBuf_raw with "Htwophase");
      [assumption|rewrite Hk -Hsz //|].
    iIntros (????) "Hpost".
    iNamed "Hpost".
    apply data_has_obj_wf in Hdata as Hwf.
    rewrite /block_bytes in Hwf.
    wp_apply (wp_SliceToList with "Hdata_s");
      first by (rewrite list_untype_length; lia).
    iDestruct (is_twophase_raw_get_valid with "Htwophase") as "%Hvalids".
    apply fmap_Some_1 in Hobj as [vobj [Hvobj ->]].
    apply Hvalids in Hvobj as Hvobj_valid.
    destruct Hvobj_valid as (Hvalid_addr&Hvalid_off&Hvalid_γ).
    rewrite Hvalid_γ in Hk.
    inversion Hk.
    subst k.
    erewrite <- val_of_obj_data_not_bit; last by eassumption.
    2: assumption.
    erewrite <- data_has_obj_not_bit.
    2-3: eassumption.

    iApply "HΦ".
    erewrite data_has_obj_not_bit; last by eassumption.
    2: trivial.
    subst mt_changed'.
    destruct (mt_changed !! a) as [vobj'|] eqn:Hacc.
    - rewrite Hvobj in Hacc.
      inversion Hacc.
      subst vobj'.
      iDestruct (is_twophase_wf_jrnl with "Htwophase") as "%Hwf_jrnl'";
        [eassumption|eassumption|].
      iExists _, _, _, _.
      iFrame "∗ #".
      iFrame (Hjrnl_maps_kinds Hjrnl_maps_mt).
      iPureIntro; split; last assumption.
      eapply always_steps_trans; first by eapply Halways_steps.
      apply always_steps_bind.
      eapply always_steps_ReadBufOp; first by intuition.
      {
        destruct Hjrnl_maps_mt as [_ <-].
        rewrite !lookup_fmap Hvobj //.
      }
      {
        destruct Hjrnl_maps_kinds as [_ ->].
        eassumption.
      }
      split; first by assumption.
      rewrite -Hsz //.
    - rewrite lookup_insert in Hvobj.
      assert (committed vobj = modified vobj) as Hvobj'.
      {
        inversion Hvobj as [Hvobj'].
        destruct vobj as [k [oc om]].
        reflexivity.
      }
      remember (
        <[a:=bufObj_to_obj (modified vobj)]>(jrnlData σj1), jrnlKinds σj1
      ) as σj1'.
      remember (
        <[a:=bufObj_to_obj (modified vobj)]>(jrnlData σj2), jrnlKinds σj2
      ) as σj2'.
      assert (jrnl_maps_kinds_valid γ σj1' σj2') as Hjrnl_maps_kinds'
        by rewrite Heqσj1' Heqσj2' //.
      assert (
        jrnl_maps_have_mt
          (<[a:=object_to_versioned (modified vobj)]> mt_changed)
          σj1' σj2'
      ) as Hjrnl_maps_mt'.
      {
        rewrite Heqσj1' Heqσj2' /jrnl_maps_have_mt !fmap_insert
          /modified /committed
          modified_to_versioned committed_to_versioned /=.
        destruct Hjrnl_maps_mt as [<- <-].
        intuition.
      }
      iDestruct (is_twophase_wf_jrnl with "Htwophase") as "%Hwf_jrnl'";
        [eassumption|eassumption|].
      iExists σj1', σj2', _, _.
      iFrame "∗ #".
      iPureIntro.
      split; last by intuition.
      subst σj1' σj2'.
      eapply always_steps_trans.
      {
        apply always_steps_extend; last by apply Halways_steps.
        - destruct Hjrnl_maps_mt as [_ <-].
          rewrite !dom_fmap.
          apply not_elem_of_dom.
          assumption.
        - eexists _.
          destruct Hjrnl_maps_kinds as [-> _].
          rewrite Hvalid_γ objSz_bufObj_to_obj.
          intuition.
      }
      apply always_steps_bind.
      eapply always_steps_ReadBufOp; first by intuition.
      {
        destruct Hjrnl_maps_mt as [_ <-].
        rewrite /= -!fmap_insert !lookup_fmap lookup_insert //.
      }
      {
        destruct Hjrnl_maps_kinds as [_ ->].
        rewrite Hvalid_γ //.
      }
      intuition.
  Qed.

  Theorem wp_TwoPhase__OverWrite' l γ γ' dinit objs_dom j K0 K
          {Hctx: LanguageCtx'
            (ext := @spec_ext_op_field _)
            (ffi := (spec_ffi_model_field))
            (ffi_semantics := (spec_ext_semantics_field))
            K}  e1 a ov :
    {{{
      is_twophase_started l γ γ' dinit objs_dom j K0
        e1
        (K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
          OverWriteOp (PairV (addr2val' a) (val_of_obj' ov))))
    }}}
      TwoPhase__OverWrite' #l (addr2val a, val_of_obj ov)
    {{{ RET #();
        is_twophase_started l γ γ' dinit objs_dom j K0
                            e1 (K #())
    }}}.
  Proof.
    iIntros (Φ) "Htwophase HΦ".
    iMod (twophase_started_ub_det' with "[$]") as "Htwophase".
    { auto. }
    iNamed "Htwophase".
    iDestruct (is_twophase_wf_jrnl with "Htwophase") as "%Hwf_jrnl";
      [eassumption|eassumption|].
    destruct Hwf_jrnl as [Hwf_jrnl1 Hwf_jrnl2].
    rewrite /TwoPhase__OverWrite'.

    destruct Hnotstuck as (s&g&Hsub&Hdom&Hnotstuck).
    apply not_stuck'_OverWrite_inv in Hnotstuck
      as (σj&k&o&Hopen&Hlookup1&Hlookup2&Hhval&Hov_len&Hnot_bit);
      last done.
    eapply val_of_obj'_inj2 in Hhval; eauto.
    assert (Ha_in_dom: a ∈ objs_dom).
    { rewrite -Hdom. apply elem_of_dom. rewrite Hopen => //=. }
    subst.
    assert (Hk: γ.(buftxn_txn_names).(txn_kinds) !! a.(addrBlock) = Some k).
    { destruct Hjrnl_maps_kinds as (_&<-).
      destruct Hsub as (?&Hs_eq&?&?).
      rewrite Hs_eq in Hopen. inversion Hopen; subst. rewrite -Hlookup2. f_equal.
      eauto.
    }

    apply obj_to_bufObj_exists in Hov_len as [bufObj [Ho <-]].
    rewrite Ho in Halways_steps.
    rewrite Ho.
    apply data_has_obj_exists_not_bit in Hnot_bit as Hdata.
    destruct Hdata as (data&a'&Hdata).
    erewrite val_of_obj_data_not_bit; [|eassumption|eassumption].
    apply data_has_obj_wf in Hdata as Hdata_wf.
    rewrite /block_bytes in Hdata_wf.
    wp_apply wp_ListToSlice.
    1: auto.
    1: rewrite list_untype_length; lia.
    {
      apply Forall_forall.
      intros x Hin.
      apply elem_of_list_fmap_2 in Hin as [b [-> Hin]].
      auto.
    }
    iIntros (data_s) "?".
    iNamed.
    wp_apply wp_slice_len.
    wp_pures.
    iDestruct (is_slice_to_small with "Hslice") as "Hslice".
    iDestruct (is_slice_small_sz with "Hslice") as "%Hsz".
    rewrite list_untype_length in Hsz.

    wp_apply (wp_TwoPhase__OverWrite_raw with "[$Htwophase $Hslice]");
      first by assumption.
    1: rewrite Hk //.
    {
      assert (
        Z.of_nat (length data) = int.Z data_s.(Slice.sz)
      ) as Hsz' by word.
      replace (int.nat (word.mul data_s.(Slice.sz) 8))
        with ((int.nat data_s.(Slice.sz)) * 8)%nat;
        last by (rewrite word.unsigned_mul; word).
      rewrite -Hsz -objSz_bufObj_to_obj.
      erewrite <- data_has_obj_not_bit.
      2-3: eassumption.
      rewrite /objSz.
      lia.
    }
    1: eapply data_has_obj_change_addr_not_bit; eassumption.
    iIntros (?) "Hpost".
    iNamed "Hpost".
    subst bufObj.

    iApply "HΦ".
    iDestruct (is_twophase_raw_get_valid with "Htwophase") as "%Hvalids".
    remember (
      <[a:=bufObj_to_obj (committed vobj)]>(jrnlData σj1), jrnlKinds σj1
    ) as σj1'.
    remember (
      <[a:=bufObj_to_obj (modified vobj)]>(jrnlData σj2), jrnlKinds σj2
    ) as σj2'.
    assert (jrnl_maps_kinds_valid γ σj1' σj2') as Hjrnl_maps_kinds'
      by rewrite Heqσj1' Heqσj2' //.
    assert (
      jrnl_maps_have_mt
        (<[a:=vobj]> mt_changed)
        σj1' σj2'
    ) as Hjrnl_maps_mt'.
    {
      rewrite Heqσj1' Heqσj2' /jrnl_maps_have_mt !fmap_insert /=.
      destruct Hjrnl_maps_mt as [<- <-].
      intuition.
    }
    iExists σj1', σj2', _, _.
    iFrame "∗ #".
    iPureIntro.
    split; last by intuition.
    subst σj1' σj2'.
    apply data_has_obj_not_bit in Hdata; last by assumption.
    destruct (mt_changed !! a) as [vobj_old|] eqn:Hacc.
    - eapply always_steps_trans.
      {
        destruct Hjrnl_maps_mt as [Hσj1_data _].
        rewrite -Hσj1_data insert_id;
          last by rewrite !lookup_fmap Hacc Hvobj_committed //.
        rewrite Hσj1_data.
        apply Halways_steps.
      }
      apply always_steps_bind.
      efeed pose proof always_steps_OverWriteOp as Halways_steps'.
      1: apply Hwf_jrnl2.
      {
        destruct Hjrnl_maps_mt as (_&<-).
        rewrite !lookup_fmap.
        erewrite Hacc.
        eauto.
      }
      {
        destruct Hjrnl_maps_kinds as (_&->).
        eauto.
      }
      {
        erewrite Hdata.
        split; last by assumption.
        apply objSz_bufObj_to_obj.
      }
      rewrite /updateData Hdata in Halways_steps'.
      apply Halways_steps'.
    - simpl in Hk.
      eapply (
        always_steps_extend _ _ _ _ _ (bufObj_to_obj (committed vobj))
      ) in Halways_steps.
      2: {
        destruct Hjrnl_maps_mt as (_&<-).
        rewrite !dom_fmap.
        eapply not_elem_of_dom.
        eassumption.
      }
      2: {
        eexists _.
        destruct Hjrnl_maps_kinds as (->&_).
        split; first by eassumption.
        split; first by apply objSz_bufObj_to_obj.
        efeed pose proof Hvalids as Hvalid;
          first by apply lookup_insert.
        simpl in Hvalid.
        destruct Hvalid as (_&Hvalid_off&_).
        assumption.
      }
      eapply always_steps_trans; first by apply Halways_steps.
      apply always_steps_bind.
      remember (
        <[a:=bufObj_to_obj (committed vobj)]> (jrnlData σj2), jrnlKinds σj2
      ) as σj'.
      efeed pose proof (always_steps_OverWriteOp a data (projT1 vobj) σj')
        as Halways_steps'.
      {
        subst σj'.
        split.
        - intros a'' Hin.
          simpl in Hin.
          simpl.
          destruct Hjrnl_maps_kinds as (_&->).
          destruct Hjrnl_maps_mt' as (_&Hσj2'_mt).
          apply dom_insert in Hin.
          apply elem_of_union in Hin as [Ha''|Hin].
          + apply elem_of_singleton_1 in Ha''.
            subst a''.
            eexists _.
            split; first by eassumption.
            apply map_Forall_insert_1_1 in Hvalids as (_&Hvalid_off&_).
            assumption.
          + destruct Hjrnl_maps_mt as (_&Hσj2_mt).
            rewrite -Hσj2_mt in Hin.
            apply dom_fmap in Hin.
            apply dom_fmap in Hin.
            apply elem_of_dom in Hin as [vobj'' Hin].
            apply map_Forall_insert_1_2 in Hvalids; last by assumption.
            apply Hvalids in Hin as (_&Hvalid_off&Hvalid_γ).
            eauto.
        - intros a'' o'' Hacc''.
          simpl in Hacc''.
          simpl.
          destruct Hjrnl_maps_kinds as (_&->).
          destruct (decide (a'' = a)) as [->|Ha''].
          + rewrite lookup_insert in Hacc''.
            inversion Hacc''.
            subst o''.
            eexists _.
            split; first by eassumption.
            apply objSz_bufObj_to_obj.
          + rewrite lookup_insert_ne in Hacc''; last by trivial.
            destruct Hjrnl_maps_mt as (_&Hσj2_mt).
            rewrite -Hσj2_mt !lookup_fmap in Hacc''.
            apply fmap_Some_1 in Hacc'' as [obj [Hobj ->]].
            apply fmap_Some_1 in Hobj as [vobj' [Hvobj' ->]].
            apply map_Forall_insert_1_2 in Hvalids; last by assumption.
            apply Hvalids in Hvobj' as (_&_&Hvalid_γ).
            rewrite Hvalid_γ.
            eexists _.
            split; first by reflexivity.
            apply objSz_bufObj_to_obj.
      }
      {
        rewrite Heqσj' /= lookup_insert.
        eauto.
      }
      {
        rewrite Heqσj' /=.
        destruct Hjrnl_maps_kinds as (_&->).
        assumption.
      }
      {
        rewrite Hdata.
        split; last by assumption.
        apply objSz_bufObj_to_obj.
      }
      rewrite /updateData Hdata in Halways_steps'.
      subst σj'.
      rewrite /= insert_insert in Halways_steps'.
      apply Halways_steps'.
  Qed.

  Lemma twophase_started_step_puredet l γ γ' dinit objs_dom j K0 K
        `{Hctx: LanguageCtx'
          (ext := @spec_ext_op_field _)
          (ffi := (spec_ffi_model_field))
          (ffi_semantics := (spec_ext_semantics_field))
          K} e0 e1 e2:
    (∀ σ g, prim_step' e1 σ g [] e2 σ g []) →
    is_twophase_started l γ γ' dinit objs_dom j K0 e0 (K e1) -∗
    is_twophase_started l γ γ' dinit objs_dom j K0 e0 (K e2).
  Proof.
    iIntros (Hstep) "Htwophase".
    iNamed "Htwophase".
    iExists _, _, _, _.
    iFrame "∗ #".
    iPureIntro.
    split; last by intuition.
    eapply always_steps_lifting_puredet; trivial.
  Qed.


End proof.
