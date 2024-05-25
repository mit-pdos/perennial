From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import map.impl list.impl list.list_slice slice.typed_slice.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang.ffi Require Import disk.
From Goose.github_com.mit_pdos.go_journal Require Import obj txn.
From Perennial.program_proof Require Import lockmap_proof.
From Perennial.program_proof Require Import txn.op_wrappers typed_translate.
From Perennial.program_proof Require Import addr.addr_proof buf.buf_proof obj.obj_proof.
From Perennial.program_proof Require Import jrnl.sep_jrnl_proof.
From Perennial.program_proof Require Import txn.txn_proof.
From Perennial.goose_lang.lib.list Require Import list.
From Perennial.goose_lang Require Import spec_assert crash_borrow.

From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.program_proof Require Import disk_prelude.

Section proof.
  Context `{!jrnlG Σ}.
  Context `{!heapGS Σ}.
  Context `{!lockmapG Σ}.
  Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp
           jrnl_spec_interp_adequacy.
  Context `{hRG: !refinement_heapG Σ}.
  Existing Instance jrnlG0.

  Notation spec_ext := jrnl_spec_ext.
  Notation sval := (@val (@spec_ffi_op_field spec_ext)).

  Implicit Types (N: namespace).

  Definition val_of_obj o :=
    match o with
    | objBit b => #b
    | objBytes o => val_of_list ((λ u, LitV (LitByte u)) <$> o)
    end.

  Definition LVL := 100%nat.

  Definition jrnl_pointsto_own a bufObj : iProp Σ :=
    "Hpointsto" ∷ jrnl_pointsto a 1 (bufObj_to_obj bufObj) ∗
    "Htok" ∷ jrnl_crash_tok a.

  Global Instance jrnl_pointsto_own_Timeless a bufObj:
    Timeless (jrnl_pointsto_own a bufObj).
  Proof. refine _. Qed.

  Global Instance jrnl_pointsto_own_Discretizable a bufObj:
    Discretizable (jrnl_pointsto_own a bufObj).
  Proof. refine _. Qed.

  Definition jrnl_maps_kinds_valid γ (σj1 σj2: jrnl_map) :=
    jrnlKinds σj1 = γ.(jrnl_txn_names).(txn_kinds) ∧
    jrnlKinds σj2 = γ.(jrnl_txn_names).(txn_kinds).

  Definition jrnl_maps_have_mt (mt_changed: gmap addr versioned_object) (σj1 σj2: jrnl_map) :=
    bufObj_to_obj <$> (committed <$> mt_changed) = jrnlData σj1 ∧
    bufObj_to_obj <$> (modified <$> mt_changed) = jrnlData σj2.

  Definition is_twophase_pre l (γ γ' : jrnl_names) dinit (objs_dom: gset addr) : iProp Σ :=
    ∃ (txnl locksl : loc) ghs,
      "#Hpre.txn" ∷ readonly (l ↦[txn.Log :: "log"] #txnl) ∗
      "#Hpre.locks" ∷ readonly (l ↦[txn.Log :: "locks"] #locksl) ∗
      "#Histxn_system" ∷ is_txn_system Njrnl γ ∗
      "#Histxn" ∷ is_txn txnl γ.(jrnl_txn_names) dinit ∗
      "#HlockMap" ∷ is_lockMap locksl ghs (set_map addr2flat objs_dom)
        (twophase_linv_flat jrnl_pointsto_own γ γ') ∗
      "#Hspec_ctx" ∷ spec_ctx ∗
      "#Hspec_crash_ctx" ∷ spec_crash_ctx jrnl_crash_ctx ∗
      "#Hjrnl_open" ∷ jrnl_open ∗
      "#Hjrnl_kinds_lb" ∷ jrnl_kinds γ.(jrnl_txn_names).(txn_kinds) ∗
      "#Hjrnl_dom" ∷ jrnl_dom objs_dom ∗
      "#Htxn_cinv" ∷ txn_cinv Njrnl γ γ' ∗
      "%Haddrs_valid" ∷ ⌜set_Forall valid_addr objs_dom⌝.

  Definition is_twophase_started l γ γ' dinit objs_dom j K e1 e2 : iProp Σ :=
    ∃ σj1 σj2 mt_changed (ls: sval),
      (* mark: do we need is_twophase_pre in here too? *)
      "Hj" ∷ j ⤇ K (Atomically ls e1) ∗
      "Htwophase" ∷ is_twophase_raw
        l γ γ' dinit jrnl_pointsto_own objs_dom mt_changed ∗
      "#Hspec_ctx" ∷ spec_ctx ∗
      "#Hspec_crash_ctx" ∷ spec_crash_ctx jrnl_crash_ctx ∗
      "#Hjrnl_open" ∷ jrnl_open ∗
      "#Hjrnl_kinds_lb" ∷ jrnl_kinds γ.(jrnl_txn_names).(txn_kinds) ∗
      "#Hjrnl_allocs" ∷ jrnl_alloc_map (jrnlAllocs σj1) ∗
      "#Hjrnl_dom" ∷ jrnl_dom objs_dom ∗
      "%Halways_steps" ∷ ⌜always_steps e1 σj1 e2 σj2⌝ ∗
      "%Hjrnl_maps_kinds" ∷ ⌜jrnl_maps_kinds_valid γ σj1 σj2⌝ ∗
      "%Hjrnl_maps_mt" ∷ ⌜jrnl_maps_have_mt mt_changed σj1 σj2⌝ ∗
      "%HLCtxt"∷ ⌜ LanguageCtx K ⌝.

  Definition is_twophase_releasable l γ γ' (objs_dom: gset addr) : iProp Σ :=
    ∃ locks_held mt_changed σj1 σj2,
      "Hlocks" ∷ is_twophase_locks
        l γ γ' jrnl_pointsto_own (set_map addr2flat objs_dom) locks_held ∗
      "Hlinvs" ∷ ([∗ set] flat_a ∈ locks_held, (
        "Hlinv" ∷ twophase_linv_flat jrnl_pointsto_own γ γ' flat_a
      )) ∗
      "%Hlocks_held" ∷ ⌜
        set_map addr2flat (dom mt_changed) = locks_held
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

  Lemma is_twophase_wf_jrnl l γ γ' dinit objs_dom mt_changed σj1 σj2 :
    jrnl_maps_kinds_valid γ σj1 σj2 →
    jrnl_maps_have_mt mt_changed σj1 σj2 →
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit jrnl_pointsto_own objs_dom mt_changed -∗
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

  Definition twophase_obj_cfupd_cancel γ' d :=
   ((|C={⊤}=> ∃ mt',
       ⌜ dom mt' = d ⌝ ∗
       "Hpointstos" ∷ ([∗ map] a ↦ obj ∈ mt',
         "Hdurable_pointsto" ∷ durable_pointsto_own γ' a obj ∗
         "Hjrnl_pointsto" ∷ jrnl_pointsto_own a obj)))%I.

  Lemma map_Forall_exists {A B} `{Countable K} (m: gmap K A) P :
    map_Forall (λ a x, ∃ y, P a x y) m →
    ∃ (m': gmap K B),
      dom m = dom m' ∧
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
    dom m2 ⊆ dom m1 →
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

  Theorem wp_Txn__Begin' N prel γ γ' dinit objs_dom j K {HCTX: LanguageCtx K} (ls: sval) e1 :
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
    wp_apply (wp_Txn__Begin_raw with "[$]"); [ assumption |..].
    iIntros (?) "?".
    iNamed.

    iApply "HΦ".
    iExists {| jrnlData := ∅; jrnlKinds := _; jrnlAllocs := ∅ |},
           {| jrnlData := ∅; jrnlKinds := _; jrnlAllocs := ∅ |}, _, _.
    iFrame "∗ #".
    iSplit.
    { rewrite /= /jrnl_alloc_map big_sepM_empty //. }
    iPureIntro.
    split.
    2: {
      split; first by rewrite /jrnl_maps_kinds_valid //.
      rewrite /jrnl_maps_have_mt !fmap_empty //.
    }
    apply always_steps_refl.
    rewrite /wf_jrnl /offsets_aligned dom_empty_L //.
  Qed.

  Theorem wp_Txn__commitNoRelease' l γ γ' dinit objs_dom j K e1 v :
    {{{ is_twophase_started l γ γ' dinit objs_dom j K e1 (SOMEV v) }}}
      Txn__commitNoRelease #l #true
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
      wp_Txn__commitNoRelease_raw
      _ _ _ _ _ _ _
      (j ⤇ K (SOMEV v))%I
      (|NC={⊤}=> j ⤇ K NONEV)%I
      with "[$Htwophase Hj]"
    )).
    1-2: refine _.
    {
      iSplit.
      - iIntros "?".
        iNamed.
        iAssert (
          [∗ map] a ↦ o ∈ jrnlData σj1,
            "Hpointsto" ∷ jrnl_pointsto a 1 o ∗
            "Htok" ∷ jrnl_crash_tok a
        )%I with "[Hcommitted]" as "Hcommitted".
        {
          destruct Hjrnl_maps_mt as [<- _].
          rewrite !big_sepM_fmap //.
        }
        iDestruct (big_sepM_sep with "Hcommitted") as "[Hpointstos Htoks]".
        destruct Hjrnl_maps_kinds as [<- _].
        iDestruct (
          ghost_step_jrnl_atomically_crash
          with "Hspec_crash_ctx Hpointstos Htoks Hjrnl_kinds_lb Hjrnl_allocs Hjrnl_open Hj"
        ) as "H"; (* "> [Hpointstos Htoks]" *) [eassumption|set_solver|].
        iMod (cfupd_weaken_mask with "H") as "[Hpointstos Htoks]".
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
            "Hpointsto" ∷ jrnl_pointsto a 1 o ∗
            "Htok" ∷ jrnl_crash_tok a
        )%I with "[Hcommitted]" as "Hcommitted".
        {
          destruct Hjrnl_maps_mt as [<- _].
          rewrite !big_sepM_fmap //.
        }
        iDestruct (big_sepM_sep with "Hcommitted") as "[Hpointstos Htoks]".
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
          with "Hspec_ctx Hpointstos Hjrnl_kinds_lb Hjrnl_allocs Hjrnl_open Hj"
        ) as "> [Hj Hpointstos]"; [eassumption|set_solver|].
        iModIntro.
        iFrame.
        destruct Hjrnl_maps_mt as [<- <-].
        rewrite !big_sepM_fmap.
        iApply big_sepM_sep.
        iFrame.
    }
    iIntros (?) "Hpost".
    iNamed "Hpost".
    iApply "HΦ".
    iSplitL "Hlocks Hlinvs".
    {
      iExists _, _, _, _.
      iDestruct (is_twophase_locks_get_pures with "Hlocks")
        as "#Hlocks_pures".
      iNamed "Hlocks_pures".
      iFrame "∗ %".
      iModIntro.
      iSplit; last by auto.
      iApply big_sepS_set_map; last by iFrame.

      intros a1 a2 Hacc1 Hacc2 Heq.
      apply elem_of_dom in Hacc1.
      apply elem_of_dom in Hacc2.
      destruct Hacc1 as [vo1 Hacc1].
      destruct Hacc2 as [vo2 Hacc2].
      apply Hvalids in Hacc1.
      apply Hvalids in Hacc2.
      rewrite /pointsto_valid in Hacc1.
      rewrite /pointsto_valid in Hacc2.
      apply addr2flat_eq; intuition.
    }
    destruct ok; first by iFrame.
    iMod "HQ"; eauto.
  Qed.


  Lemma na_crash_inv_status_wand_sepM {A} `{Countable K} (m: gmap K A) Q P :
    ([∗ map] i ↦ x ∈ m, crash_borrow (Q i x) (P i x)) -∗
    □ (
      [∗ map] i ↦ x ∈ m,
      Q i x -∗
      P i x
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
    iDestruct (crash_borrow_crash_wand with "Hcrash_inv") as "#Hstatus".
    iModIntro.
    iApply big_sepM_insert; first by assumption.
    iFrame "#".
  Qed.

  Theorem twophase_started_abort l γ γ' dinit objs_dom j K e1 e2 :
    is_twophase_started l γ γ' dinit objs_dom j K e1 e2 -∗
    wpc_nval ⊤ (is_twophase_releasable l γ γ' objs_dom ∗ j ⤇ K NONEV).
  Proof.
    iIntros "Htwophase".
    iNamed "Htwophase".
    iNamed "Htwophase".
    iApply ncfupd_wpc_nval.
    iMod (ghost_step_jrnl_atomically_abort with "[$] [$] [$]") as "Hj"; auto.
    (* iExists _, _, _, _. *)
    iDestruct (is_twophase_locks_get_pures with "Hlocks")
      as "#Hlocks_pures".
    iNamed "Hlocks_pures".
    iNamed "Hjrnl".
    iDestruct (na_crash_inv_status_wand_sepM with "Hcrash_invs") as
      "#Hstatuses".
    iDestruct (
      crash_borrow_wpc_nval_sepM ⊤ _ _
      (λ a vobj,
        twophase_pre_crash_inv_pred jrnl_pointsto_own γ a (committed vobj)
      )
      (
        [∗ map] a ↦ vobj ∈ mt_changed,
          modify_token γ a
      )%I
      with
      "Hcrash_invs [Hjrnl_mem Hjrnl_durable_frag]"
    ) as "H". (* "> [Htoks Hcrash_invs]". *)
    {
      iIntros "Hpreds".
      iDestruct (big_sepM_sep with "Hpreds") as "[Hjrnl_pointstos Hpreds]".
      iDestruct (big_sepM_sep with "Hpreds")
        as "[Hdurable_pointstos %Hcommitted_valids]".
      iApply big_sepM_fmap in "Hdurable_pointstos".
      iDestruct (
        is_jrnl_to_old_pred' with
        "Hjrnl_mem Hjrnl_durable_frag Hdurable_pointstos"
      ) as "?".
      iNamed.
      iApply (big_sepM_fmap committed) in "Hold_vals".
      iDestruct (big_sepM_sep with "Hold_vals")
        as "[Htokens Hdurable_pointstos]".
      iModIntro.
      iFrame "∗ #".
      iDestruct (big_sepM_sep with "[$Hdurable_pointstos $Hjrnl_pointstos]")
        as "Hpreds".
      iApply (big_sepM_impl with "Hpreds").
      iIntros (a vobj) "!> %Hacc [Hdurable_pointsto Hjrnl_pointsto]".
      iFrame.
      iPureIntro.
      apply Hcommitted_valids.
      assumption.
    }
    iModIntro.
    iApply (wpc_nval_strong_mono with "H").
    iNext. iIntros "[Htoks Hcrash_invs]".
    iDestruct (big_sepM_sep with "[$Htoks $Hcrash_invs]") as "Hcrash_invs".
    iModIntro.
    iFrame.
    iExists _, _, _.
    iFrame "∗ %".
    iSplit; last by auto.
    iApply big_sepS_set_map.
    {
      intros a1 a2 Hacc1 Hacc2 Heq.
      apply elem_of_dom in Hacc1.
      apply elem_of_dom in Hacc2.
      destruct Hacc1 as [vo1 Hacc1].
      destruct Hacc2 as [vo2 Hacc2].
      apply Hvalids in Hacc1.
      apply Hvalids in Hacc2.
      rewrite /pointsto_valid in Hacc1.
      rewrite /pointsto_valid in Hacc2.
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
    rewrite /pointsto_valid in Hacc.
    rewrite /pointsto_valid //.
  Qed.

  Theorem wp_Txn__ReleaseAll' l γ γ' objs_dom :
    {{{ is_twophase_releasable l γ γ' objs_dom }}}
      Txn__ReleaseAll #l
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Htwophase HΦ".
    iNamed "Htwophase".
    wp_apply (wp_Txn__ReleaseAll with "[$]").
    iApply "HΦ".
    trivial.
  Qed.

  Lemma wp_SliceToListFrom data_s t q data (from: nat) :
    from ≤ length data →
    length data < 2^64 →
    {{{
      "Hslice" ∷ own_slice data_s t q data
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
    iDestruct (own_slice_sz with "Hslice") as "%Hsz".
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
    iDestruct (own_slice_small_read with "Hslice") as "[Hslice Hrestore]".
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
      "Hslice" ∷ own_slice data_s t q data
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
      "Hslice" ∷ own_slice data1_s t (DfracOwn 1) data1
    }}}
      ListToSliceApp t (val_of_list data2) (slice_val data1_s)
    {{{ data_s, RET (slice_val data_s);
      "Hslice" ∷ own_slice data_s t (DfracOwn 1) (data1 ++ data2)
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
      by iFrame.
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
      "Hslice" ∷ own_slice data_s t (DfracOwn 1) data
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
    - eexists data, (W64 0, W64 0).
      rewrite /data_has_obj //.
    - eexists data, (W64 0, W64 0).
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

  Lemma twophase_started_ub_det_with_alloc' la u l γ γ' dinit objs_dom E j K0 K
        `{Hctx: LanguageCtx'
          (ext := @spec_ffi_op_field _)
          (ffi := (spec_ffi_model_field))
          (ffi_semantics := (spec_ext_semantics_field))
          K} e0 e :
    nclose sN ⊆ E →
    jrnl_alloc la u -∗
    is_twophase_started l γ γ' dinit objs_dom j K0 e0 (K e)
    -∗ wpc_nval E
      (∃ σj1 σj2 mt_changed (ls: sval),
        "%Hin" ∷ ⌜ (jrnlAllocs σj1 !! la = Some u) ⌝ ∗
        "Hj" ∷ j ⤇ K0 (Atomically ls e0) ∗
        "Htwophase" ∷ is_twophase_raw
          l γ γ' dinit jrnl_pointsto_own objs_dom mt_changed ∗
        "#Hspec_ctx" ∷ spec_ctx ∗
        "#Hspec_crash_ctx" ∷ spec_crash_ctx jrnl_crash_ctx ∗
        "#Hjrnl_open" ∷ jrnl_open ∗
        "#Hjrnl_kinds_lb" ∷ jrnl_kinds γ.(jrnl_txn_names).(txn_kinds) ∗
        "#Hjrnl_allocs" ∷ jrnl_alloc_map (jrnlAllocs σj1) ∗
        "%Halways_steps" ∷ ⌜always_steps e0 σj1 (K e) σj2⌝ ∗
        "%Hjrnl_maps_kinds" ∷ ⌜jrnl_maps_kinds_valid γ σj1 σj2⌝ ∗
        "%Hjrnl_maps_mt" ∷ ⌜jrnl_maps_have_mt mt_changed σj1 σj2⌝ ∗
        "%HLCtxt"∷ ⌜ LanguageCtx K0 ⌝ ∗
        "#Hjrnl_dom" ∷ jrnl_dom objs_dom ∗
        "%Hnotstuck" ∷ ⌜ (∃ s g, jrnl_sub_state σj2 s ∧
         dom (jrnlData (get_jrnl s.(world))) = objs_dom ∧
         ¬ stuck' (K e) s g) ⌝).
  Proof.
    iIntros (?) "#Hjrnl_alloc1". iNamed 1.
    iNamed "Htwophase".
    iDestruct (na_crash_inv_status_wand_sepM with "Hcrash_invs") as
      "#Hstatuses".
    iDestruct (jrnl_ctx_allocs_agree2 with "[$] [$]") as %Hlookup'.
    opose proof (always_steps_extend_allocs2 _ _ _ _ _ _ _ _); eauto.
    { destruct Hlookup'; eauto. left. apply not_elem_of_dom; eauto. }
    clear Halways_steps.
    iDestruct (jrnl_ctx_allocs_extend with "[$] [$]") as "#Hjrnl_allocs'".
    assert (jrnlData (updateAllocs σj1 la u) = jrnlData σj1) as Heq_data_update.
    { destruct σj1; eauto. }
    assert (jrnlKinds (updateAllocs σj1 la u) = jrnlKinds σj1) as Heq_kinds_update.
    { destruct σj1; eauto. }
    iDestruct (
      crash_borrow_wpc_nval_sepM E _ _
      (λ a vobj,
        twophase_pre_crash_inv_pred jrnl_pointsto_own γ a (committed vobj)
      )
      (
        "Hj" ∷ j ⤇ K0 (Atomically ls e0) ∗
        "%Hnotstuck" ∷ ⌜∃ s g,
          jrnl_sub_state (updateAllocs σj2 la u) s ∧
          dom (jrnlData (get_jrnl s.(world))) =
            objs_dom ∧ ¬ stuck' (K e) s g
        ⌝
      )%I
      with
      "Hcrash_invs [Hj]"
    ) as "H". (* "> [HR Hcrash_invs]". *)
    {
      iIntros "Hpreds".
      iDestruct (big_sepM_sep with "Hpreds") as "(Hjrnl_pointstos&Hpreds)".
      iDestruct (big_sepM_sep with "Hpreds") as "(Hdurables&%Hvalids_c)".
      iDestruct (big_sepM_sep with "Hjrnl_pointstos")
        as "(Hjrnl_pointstos&Htoks)".
      iMod (
        ghost_step_jrnl_atomically_ub'
        with "Hspec_ctx [Hjrnl_pointstos] [] Hjrnl_allocs' [$] Hjrnl_open Hj"
      ) as "(%Hnotstuck&Hj&Hjrnl_pointstos)".
      1-2: eassumption.
      {
        rewrite Heq_data_update.
        destruct Hjrnl_maps_mt as [<- _].
        rewrite !big_sepM_fmap //.
      }
      {
        rewrite Heq_kinds_update.
        destruct Hjrnl_maps_kinds as (->&_); eauto. }
      iModIntro.
      iFrame "∗ # %".
      rewrite Heq_data_update.
      destruct Hjrnl_maps_mt as [<- _].
      rewrite !big_sepM_fmap //.
      iDestruct (big_sepM_sep with "[$Htoks $Hdurables]") as "Hpreds".
      iDestruct (big_sepM_sep with "[$Hpreds $Hjrnl_pointstos]") as "Hpreds".
      iApply (big_sepM_mono with "Hpreds").
      iIntros (a vobj Hacc) "[[Htok Hdurable] Hcrash_inv]".
      iFrame.
      iPureIntro.
      apply Hvalids in Hacc.
      rewrite /pointsto_valid in Hacc.
      rewrite /pointsto_valid //.
    }
    iApply (wpc_nval_strong_mono with "H").
    iIntros "!> [HR Hcrash_invs]".
    iNamed "HR".

    iModIntro.
    iExists (updateAllocs σj1 la u), (updateAllocs σj2 la u), _, _.
    iFrame "Hj".
    iSplit.
    { iPureIntro. rewrite //= lookup_insert //=. }
    iSplit; first by iFrame "∗ # %".
    iFrame "# %".
  Qed.

  Lemma twophase_started_ub_det' l γ γ' dinit objs_dom E j K0 K
        `{Hctx: LanguageCtx'
          (ext := @spec_ffi_op_field _)
          (ffi := (spec_ffi_model_field))
          (ffi_semantics := (spec_ext_semantics_field))
          K} e0 e :
    nclose sN ⊆ E →
    is_twophase_started l γ γ' dinit objs_dom j K0 e0 (K e)
    -∗ wpc_nval E
      (∃ σj1 σj2 mt_changed (ls: sval),
        "Hj" ∷ j ⤇ K0 (Atomically ls e0) ∗
        "Htwophase" ∷ is_twophase_raw
          l γ γ' dinit jrnl_pointsto_own objs_dom mt_changed ∗
        "#Hspec_ctx" ∷ spec_ctx ∗
        "#Hspec_crash_ctx" ∷ spec_crash_ctx jrnl_crash_ctx ∗
        "#Hjrnl_open" ∷ jrnl_open ∗
        "#Hjrnl_kinds_lb" ∷ jrnl_kinds γ.(jrnl_txn_names).(txn_kinds) ∗
        "#Hjrnl_allocs" ∷ jrnl_alloc_map (jrnlAllocs σj1) ∗
        "%Halways_steps" ∷ ⌜always_steps e0 σj1 (K e) σj2⌝ ∗
        "%Hjrnl_maps_kinds" ∷ ⌜jrnl_maps_kinds_valid γ σj1 σj2⌝ ∗
        "%Hjrnl_maps_mt" ∷ ⌜jrnl_maps_have_mt mt_changed σj1 σj2⌝ ∗
        "%HLCtxt"∷ ⌜ LanguageCtx K0 ⌝ ∗
        "#Hjrnl_dom" ∷ jrnl_dom objs_dom ∗
        "%Hnotstuck" ∷ ⌜ (∃ s g, jrnl_sub_state σj2 s ∧
         dom (jrnlData (get_jrnl s.(world))) = objs_dom ∧
         ¬ stuck' (K e) s g) ⌝).
  Proof.
    iIntros (?). iNamed 1.
    iNamed "Htwophase".
    iDestruct (na_crash_inv_status_wand_sepM with "Hcrash_invs") as
      "#Hstatuses".
    iDestruct (
      crash_borrow_wpc_nval_sepM E _ _
      (λ a vobj,
        twophase_pre_crash_inv_pred jrnl_pointsto_own γ a (committed vobj)
      )
      (
        "Hj" ∷ j ⤇ K0 (Atomically ls e0) ∗
        "%Hnotstuck" ∷ ⌜∃ s g,
          jrnl_sub_state σj2 s ∧
          dom (jrnlData (get_jrnl s.(world))) =
            objs_dom ∧ ¬ stuck' (K e) s g
        ⌝
      )%I
      with
      "Hcrash_invs [Hj]"
    ) as "H". (* "> [HR Hcrash_invs]". *)
    {
      iIntros "Hpreds".
      iDestruct (big_sepM_sep with "Hpreds") as "(Hjrnl_pointstos&Hpreds)".
      iDestruct (big_sepM_sep with "Hpreds") as "(Hdurables&%Hvalids_c)".
      iDestruct (big_sepM_sep with "Hjrnl_pointstos")
        as "(Hjrnl_pointstos&Htoks)".
      iMod (
        ghost_step_jrnl_atomically_ub'
        with "Hspec_ctx [Hjrnl_pointstos] [] Hjrnl_allocs [$] Hjrnl_open Hj"
      ) as "(%Hnotstuck&Hj&Hjrnl_pointstos)".
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
      iDestruct (big_sepM_sep with "[$Hpreds $Hjrnl_pointstos]") as "Hpreds".
      iApply (big_sepM_mono with "Hpreds").
      iIntros (a vobj Hacc) "[[Htok Hdurable] Hcrash_inv]".
      iFrame.
      iPureIntro.
      apply Hvalids in Hacc.
      rewrite /pointsto_valid in Hacc.
      rewrite /pointsto_valid //.
    }
    iApply (wpc_nval_strong_mono with "H").
    iIntros "!> [HR Hcrash_invs]".
    iNamed "HR".

    iModIntro.
    iExists _, _, _, _.
    iFrame "Hj".
    iSplit; first by iFrame "∗ # %".
    by iFrame "# %".
  Qed.


  Lemma twophase_started_ub_det l γ γ' dinit objs_dom E j K0 K
        `{Hctx: LanguageCtx'
          (ext := @spec_ffi_op_field _)
          (ffi := (spec_ffi_model_field))
          (ffi_semantics := (spec_ext_semantics_field))
          K} e0 e :
    nclose sN ⊆ E →
    (∀ s g, stuck' e s g) →
    is_twophase_started l γ γ' dinit objs_dom j K0 e0 (K e)
    -∗ wpc_nval E False.
  Proof.
    iIntros. iDestruct (twophase_started_ub_det' with "[$]") as "H".
    { eauto. }
    iApply (wpc_nval_strong_mono with "H").
    iNext. iNamed 1.
    iExFalso.
    iPureIntro.
    destruct Hnotstuck as (s&g&Hsub&Hdom&Hnstuck).
    eapply Hnstuck.
    eapply stuck'_fill; eauto.
  Qed.
  Opaque crash_borrow.

  Theorem wp_Txn__ReadBuf' l γ γ' dinit objs_dom j K0 K
          {Hctx: LanguageCtx'
            (ext := @spec_ffi_op_field _)
            (ffi := (spec_ffi_model_field))
            (ffi_semantics := (spec_ext_semantics_field))
            K} e1 a (sz: u64) :
    {{{
      is_twophase_started l γ γ' dinit objs_dom j K0 e1
        (K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
          ReadBufOp (PairV (addr2val' a) #sz)))
    }}}
      Txn__ReadBuf' #l (addr2val a, #sz)
    {{{ data, RET (val_of_obj (objBytes data));
        is_twophase_started l γ γ' dinit objs_dom j K0 e1
          (K (val_of_obj' (objBytes data)))
    }}}.
  Proof.
    iIntros (Φ) "Htwophase HΦ".
    rewrite /Txn__ReadBuf'.
    iDestruct (twophase_started_ub_det' with "[$]") as "Htwophase".
    { auto. }
    wp_bind (addr2val a, #sz)%E.
    iApply (wpc_nval_elim_wp with "Htwophase"); auto.
    wp_pures. iModIntro. iNamed 1.
    iDestruct (is_twophase_wf_jrnl with "Htwophase") as "%Hwf_jrnl";
      [eassumption|eassumption|].


    destruct Hnotstuck as (s&g&Hsub&Hdom&Hnotstuck).
    apply not_stuck'_ReadBuf_inv in Hnotstuck
      as (σj&k&Hopen&Hlookup1&Hlookup2&Hsz&Hk_not_bit);
      last done.
    assert (Ha_in_dom: a ∈ objs_dom).
    { rewrite -Hdom. apply elem_of_dom. rewrite Hopen => //=. }
    assert (Hk: γ.(jrnl_txn_names).(txn_kinds) !! a.(addrBlock) = Some k).
    { destruct Hjrnl_maps_kinds as (_&<-).
      destruct Hsub as (?&Hs_eq&?&?&?).
      rewrite Hs_eq in Hopen. inversion Hopen; subst. rewrite -Hlookup2. f_equal.
      eauto.
    }

    wp_apply (wp_Txn__ReadBuf_raw with "Htwophase");
      [assumption|rewrite Hk -Hsz //|].
    iIntros (????) "Hpost".
    iNamed "Hpost".
    apply data_has_obj_wf in Hdata as Hwf.
    rewrite /block_bytes in Hwf.
    iDestruct (is_twophase_raw_get_valid with "Htwophase") as "%Hvalids".
    wp_apply (wp_SliceToList with "Hdata_s");
      first by (rewrite list_untype_length; lia).
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
      remember (updateData σj1 a (bufObj_to_obj (modified vobj))) as σj1'.
      remember (updateData σj2 a (bufObj_to_obj (modified vobj))) as σj2'.
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
      iSplit.
      { rewrite Heqσj1' /=. eauto. }
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
        rewrite /updateData.
        destruct Hjrnl_maps_mt as [_ <-].
        rewrite /= -!fmap_insert !lookup_fmap lookup_insert //.
      }
      {
        rewrite /updateData.
        destruct Hjrnl_maps_kinds as [_ ->].
        rewrite Hvalid_γ //.
      }
      intuition.
  Qed.

  Theorem wp_Txn__ReadBufBit' l γ γ' dinit objs_dom j K0 K
          {Hctx: LanguageCtx'
            (ext := @spec_ffi_op_field _)
            (ffi := (spec_ffi_model_field))
            (ffi_semantics := (spec_ext_semantics_field))
            K} e1 a :
    {{{
      is_twophase_started l γ γ' dinit objs_dom j K0 e1
        (K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
          ReadBitOp (addr2val' a)))
    }}}
      Txn__ReadBufBit' #l (addr2val a)
    {{{ data, RET (val_of_obj (objBit data));
        is_twophase_started l γ γ' dinit objs_dom j K0 e1
          (K (val_of_obj' (objBit data)))
    }}}.
  Proof.
    iIntros (Φ) "Htwophase HΦ".
    iDestruct (twophase_started_ub_det' with "[$]") as "Htwophase".
    { auto. }
    rewrite /Txn__ReadBufBit'.
    wp_pure1.
    wp_pure1.
    wp_pure1.
    wp_bind (Skip)%E.
    iApply (wpc_nval_elim_wp with "Htwophase"); auto.
    wp_pures. iModIntro. iNamed 1.
    iDestruct (is_twophase_wf_jrnl with "Htwophase") as "%Hwf_jrnl";
      [eassumption|eassumption|].

    destruct Hnotstuck as (s&g&Hsub&Hdom&Hnotstuck).
    apply not_stuck'_ReadBit_inv in Hnotstuck
      as (σj&Hopen&Hlookup1&Hlookup2);
      last eauto.
    assert (Ha_in_dom: a ∈ objs_dom).
    { rewrite -Hdom. apply elem_of_dom. rewrite Hopen => //=. }
    assert (Hk: γ.(jrnl_txn_names).(txn_kinds) !! a.(addrBlock) = Some KindBit).
    { destruct Hjrnl_maps_kinds as (_&<-).
      destruct Hsub as (?&Hs_eq&?&?&?).
      rewrite Hs_eq in Hopen. inversion Hopen; subst. rewrite -Hlookup2. f_equal.
      eauto.
    }


    wp_apply (wp_Txn__ReadBufBit with "Htwophase");
      [assumption|rewrite Hk //|].
    iIntros (??) "Hpost".
    iNamed "Hpost".
    iDestruct (is_twophase_raw_get_valid with "Htwophase") as "%Hvalids".
    apply fmap_Some_1 in Hobj as [vobj [Hvobj Heq]].
    apply Hvalids in Hvobj as Hvobj_valid.
    destruct Hvobj_valid as (Hvalid_addr&Hvalid_off&Hvalid_γ).
    rewrite Hvalid_γ in Hk.
    inversion Hk.

    iApply "HΦ".
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
      eapply always_steps_ReadBitOp; first by intuition.
      {
        destruct Hjrnl_maps_mt as [_ <-].
        rewrite !lookup_fmap Hvobj //.
        rewrite /= -Heq //.
      }
      {
        destruct Hjrnl_maps_kinds as [_ ->].
        rewrite Hvalid_γ. subst. eauto.
      }
    - rewrite lookup_insert in Hvobj.
      assert (committed vobj = modified vobj) as Hvobj'.
      {
        inversion Hvobj as [Hvobj'].
        destruct vobj as [k [oc om]].
        reflexivity.
      }
      remember (updateData σj1 a (bufObj_to_obj (modified vobj))) as σj1'.
      remember (updateData σj2 a (bufObj_to_obj (modified vobj))) as σj2'.
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
        [eassumption| |].
      { inversion Hvobj. subst. eauto. }
      iExists σj1', σj2', _, _.
      iFrame "∗ #".
      iSplit.
      { rewrite Heqσj1' /=. eauto. }
      iPureIntro.
      split; last first.
      { split_and!; intuition.
        inversion Hvobj. subst. eauto. }
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
      eapply always_steps_ReadBitOp; first by intuition.
      {
        rewrite /updateData.
        destruct Hjrnl_maps_mt as [_ <-].
        rewrite /= -!fmap_insert !lookup_fmap lookup_insert //.
        rewrite /= -Heq //.
      }
      {
        rewrite /updateData.
        destruct Hjrnl_maps_kinds as [_ ->].
        rewrite Hvalid_γ //.
      }
  Qed.

  Theorem wp_Txn__OverWrite' l γ γ' dinit objs_dom j K0 K
          {Hctx: LanguageCtx'
            (ext := @spec_ffi_op_field _)
            (ffi := (spec_ffi_model_field))
            (ffi_semantics := (spec_ext_semantics_field))
            K}  e1 a ov :
    {{{
      is_twophase_started l γ γ' dinit objs_dom j K0
        e1
        (K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
          OverWriteOp (PairV (addr2val' a) (val_of_obj' ov))))
    }}}
      Txn__OverWrite' #l (addr2val a, val_of_obj ov)
    {{{ RET #();
        is_twophase_started l γ γ' dinit objs_dom j K0
                            e1 (K #())
    }}}.
  Proof.
    iIntros (Φ) "Htwophase HΦ".
    rewrite /Txn__OverWrite'.
    iDestruct (twophase_started_ub_det' with "[$]") as "Htwophase".
    { auto. }
    wp_bind (addr2val a, val_of_obj ov)%E.
    iApply (wpc_nval_elim_wp with "Htwophase"); auto.
    wp_pures. iModIntro. iNamed 1.
    iDestruct (is_twophase_wf_jrnl with "Htwophase") as "%Hwf_jrnl";
      [eassumption|eassumption|].
    destruct Hwf_jrnl as [Hwf_jrnl1 Hwf_jrnl2].
    rewrite /Txn__OverWrite'.

    destruct Hnotstuck as (s&g&Hsub&Hdom&Hnotstuck).
    apply not_stuck'_OverWrite_inv in Hnotstuck
      as (σj&k&o&Hopen&Hlookup1&Hlookup2&Hhval&Hov_len&Hnot_bit);
      last done.
    eapply val_of_obj'_inj2 in Hhval; eauto.
    assert (Ha_in_dom: a ∈ objs_dom).
    { rewrite -Hdom. apply elem_of_dom. rewrite Hopen => //=. }
    subst.
    assert (Hk: γ.(jrnl_txn_names).(txn_kinds) !! a.(addrBlock) = Some k).
    { destruct Hjrnl_maps_kinds as (_&<-).
      destruct Hsub as (?&Hs_eq&?&?&?).
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
    iDestruct (own_slice_to_small with "Hslice") as "Hslice".
    iDestruct (own_slice_small_sz with "Hslice") as "%Hsz".
    rewrite list_untype_length in Hsz.

    wp_apply (wp_Txn__OverWrite_raw with "[$Htwophase $Hslice]");
      first by assumption.
    1: rewrite Hk //.
    {
      assert (
        Z.of_nat (length data) = uint.Z data_s.(Slice.sz)
      ) as Hsz' by word.
      replace (uint.nat (word.mul data_s.(Slice.sz) 8))
        with ((uint.nat data_s.(Slice.sz)) * 8)%nat;
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
    remember (updateData σj1 a (bufObj_to_obj (committed vobj))) as σj1'.
    remember (updateData σj2 a (bufObj_to_obj (modified vobj))) as σj2'.
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
    iSplit.
    { rewrite Heqσj1' /=; eauto. }
    iPureIntro.
    split; last by intuition.
    subst σj1' σj2'.
    apply data_has_obj_not_bit in Hdata; last by assumption.
    destruct (mt_changed !! a) as [vobj_old|] eqn:Hacc.
    - eapply always_steps_trans.
      {
        destruct Hjrnl_maps_mt as [Hσj1_data _].
        rewrite /updateData.
        rewrite -Hσj1_data insert_id;
          last by rewrite !lookup_fmap Hacc Hvobj_committed //.
        rewrite Hσj1_data.
        apply Halways_steps.
      }
      apply always_steps_bind.
      opose proof (always_steps_OverWriteOp _ _ _ _ _ _ _ _) as Halways_steps'.
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
        opose proof (Hvalids _ _ _) as Hvalid;
          first by apply lookup_insert.
        simpl in Hvalid.
        destruct Hvalid as (_&Hvalid_off&_).
        assumption.
      }
      eapply always_steps_trans; first by apply Halways_steps.
      apply always_steps_bind.
      remember (updateData σj2 a (bufObj_to_obj (committed vobj))) as σj'.
      opose proof (always_steps_OverWriteOp a data (projT1 vobj) σj' _ _ _ _)
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

  Theorem wp_Txn__OverWriteBit' l γ γ' dinit objs_dom j K0 K
          {Hctx: LanguageCtx'
            (ext := @spec_ffi_op_field _)
            (ffi := (spec_ffi_model_field))
            (ffi_semantics := (spec_ext_semantics_field))
            K}  e1 a ov :
    {{{
      is_twophase_started l γ γ' dinit objs_dom j K0
        e1
        (K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
          OverWriteBitOp (PairV (addr2val' a) (val_of_obj' ov))))
    }}}
      Txn__OverWriteBit' #l (addr2val a, val_of_obj ov)
    {{{ RET #();
        is_twophase_started l γ γ' dinit objs_dom j K0
                            e1 (K #())
    }}}.
  Proof.
    iIntros (Φ) "Htwophase HΦ".
    rewrite /Txn__OverWrite'.
    iDestruct (twophase_started_ub_det' with "[$]") as "Htwophase".
    { auto. }
    wp_bind (addr2val a, val_of_obj ov)%E.
    iApply (wpc_nval_elim_wp with "Htwophase"); auto.
    wp_pures. iModIntro. iNamed 1.
    iDestruct (is_twophase_wf_jrnl with "Htwophase") as "%Hwf_jrnl";
      [eassumption|eassumption|].
    destruct Hwf_jrnl as [Hwf_jrnl1 Hwf_jrnl2].
    rewrite /Txn__OverWrite'.

    destruct Hnotstuck as (s&g&Hsub&Hdom&Hnotstuck).
    apply not_stuck'_OverWriteBit_inv in Hnotstuck
      as (σj&o&Hopen&Hlookup1&Hlookup2&Hhval);
      last done.
    eapply val_of_obj'_inj3 in Hhval.
    assert (Ha_in_dom: a ∈ objs_dom).
    { rewrite -Hdom. apply elem_of_dom. rewrite Hopen => //=. }
    subst.
    assert (Hk: γ.(jrnl_txn_names).(txn_kinds) !! a.(addrBlock) = Some KindBit).
    { destruct Hjrnl_maps_kinds as (_&<-).
      destruct Hsub as (?&Hs_eq&?&?&?).
      rewrite Hs_eq in Hopen. inversion Hopen; subst. rewrite -Hlookup2. f_equal.
      eauto.
    }


    rewrite /Txn__OverWriteBit'.
    wp_pures.
    wp_apply (wp_Txn__OverWriteBit with "[$Htwophase]");
      first by assumption.
    1: rewrite Hk //.
    iIntros (?) "Hpost".
    iNamed "Hpost".

    iApply "HΦ".
    iDestruct (is_twophase_raw_get_valid with "Htwophase") as "%Hvalids".
    remember (updateData σj1 a (bufObj_to_obj (committed vobj))) as σj1'.
    remember (updateData σj2 a (bufObj_to_obj (modified vobj))) as σj2'.
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
    iSplit.
    { rewrite Heqσj1' /=. eauto. }
    iPureIntro.
    split; last by intuition.
    subst σj1' σj2'.
    destruct (mt_changed !! a) as [vobj_old|] eqn:Hacc.
    - eapply always_steps_trans.
      {
        destruct Hjrnl_maps_mt as [Hσj1_data _].
        rewrite /updateData.
        rewrite -Hσj1_data insert_id;
          last by rewrite !lookup_fmap Hacc Hvobj_committed //.
        rewrite Hσj1_data.
        apply Halways_steps.
      }
      apply always_steps_bind.
      opose proof (always_steps_OverWriteBitOp _ _ _ _ _ _ _ _) as Halways_steps'.
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
        rewrite //=.
      }
      rewrite /updateData in Halways_steps'.
      rewrite Hvobj_modified /= /bufObj_to_obj //=.
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
        opose proof (Hvalids _ _ _) as Hvalid;
          first by apply lookup_insert.
        simpl in Hvalid.
        destruct Hvalid as (_&Hvalid_off&_).
        rewrite objSz_bufObj_to_obj.
        inversion Hvobj_modified as [Heq]. rewrite Heq.
        rewrite Hvobj_modified /= in Hvalid_off. split; auto.
        rewrite /committed//= Heq //=.
      }
      eapply always_steps_trans; first by apply Halways_steps.
      apply always_steps_bind.
      remember (updateData σj2 a (bufObj_to_obj (committed vobj))) as σj'.
      opose proof (always_steps_OverWriteBitOp a o (projT1 vobj) σj' _ _ _ _)
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
            rewrite Hvobj_modified in Hvalid_off; assumption.
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
            rewrite objSz_bufObj_to_obj.
            inversion Hvobj_modified as [Heq]. rewrite Heq.
            rewrite /committed//= Heq //=.
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
        inversion Hvobj_modified as [Heq1]; subst. rewrite Heq1. eauto.
      }
      {
        inversion Hvobj_modified as [Heq1]; subst. rewrite Heq1. eauto.
      }
      rewrite /updateData in Halways_steps'.
      subst σj'.
      rewrite /= insert_insert in Halways_steps'.
      rewrite Hvobj_modified //=.
  Qed.

  Lemma twophase_started_step_puredet l γ γ' dinit objs_dom j K0 K
        `{Hctx: LanguageCtx'
          (ext := @spec_ffi_op_field _)
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
