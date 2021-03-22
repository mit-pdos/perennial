From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import map.impl list.impl list.list_slice.
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

  Definition is_twophase_system N γ :=
    is_txn_system N γ.

  Definition val_of_obj (o : obj) := val_of_list ((λ u, LitV (LitByte u)) <$> o).

  Definition bufObj_to_obj bufObj : obj :=
    match objData bufObj with
    | bufBit b => [U8 (if b then 1 else 0)]
    | bufInode data | bufBlock data => data
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
        (twophase_linv_flat 0 jrnl_mapsto_own γ γ') ∗
      "#Hspec_ctx" ∷ spec_ctx ∗
      "#Hspec_crash_ctx" ∷ spec_crash_ctx jrnl_crash_ctx ∗
      "#Hjrnl_open" ∷ jrnl_open ∗
      "#Hjrnl_kinds_lb" ∷ jrnl_kinds_lb γ.(buftxn_txn_names).(txn_kinds) ∗
      "#Htxn_cinv" ∷ txn_cinv Nbuftxn γ γ' ∗
      "%Haddrs_valid" ∷ ⌜set_Forall valid_addr objs_dom⌝.

  Definition is_twophase_started l γ γ' dinit objs_dom j K e1 e2 : iProp Σ :=
    ∃ σj1 σj2 mt_changed (ls: sval),
      (* mark: do we need is_twophase_pre in here too? *)
      "Hj" ∷ j ⤇ K (Atomically ls e1) ∗
      "Htwophase" ∷ is_twophase_raw
        l γ γ' dinit 0 jrnl_mapsto_own objs_dom mt_changed ∗
      "#Hspec_ctx" ∷ spec_ctx ∗
      "#Hspec_crash_ctx" ∷ spec_crash_ctx jrnl_crash_ctx ∗
      "#Hjrnl_open" ∷ jrnl_open ∗
      "#Hjrnl_kinds_lb" ∷ jrnl_kinds_lb γ.(buftxn_txn_names).(txn_kinds) ∗
      "%Halways_steps" ∷ ⌜always_steps e1 σj1 e2 σj2⌝ ∗
      "%Hjrnl_maps_kinds" ∷ ⌜jrnl_maps_kinds_valid γ σj1 σj2⌝ ∗
      "%Hjrnl_maps_mt" ∷ ⌜jrnl_maps_have_mt mt_changed σj1 σj2⌝.

  Definition is_twophase_releasable l γ γ' (objs_dom: gset addr) : iProp Σ :=
    ∃ locks_held mt_changed σj1 σj2,
      (* mark: do we need is_twophase_pre in here too? *)
      "Hlocks" ∷ is_twophase_locks
        l γ γ' 0 jrnl_mapsto_own (set_map addr2flat objs_dom) locks_held ∗
      "Hlinvs" ∷ ([∗ list] flat_a ∈ locks_held, (
        "Hlinv" ∷ twophase_linv_flat 0 jrnl_mapsto_own γ γ' flat_a
      )) ∗
      "%Hlocks_held" ∷ ⌜
        set_map addr2flat (dom (gset addr) mt_changed) =
        (list_to_set locks_held: gset u64)
      ⌝ ∗
      "%Hjrnl_maps_kinds" ∷ ⌜jrnl_maps_kinds_valid γ σj1 σj2⌝ ∗
      "%Hjrnl_maps_mt" ∷ ⌜jrnl_maps_have_mt mt_changed σj1 σj2⌝.

  Theorem wpc_Init N (d: loc) γ dinit logm mt k :
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
      "#Hjrnl_kinds_lb" ∷ jrnl_kinds_lb γ.(buftxn_txn_names).(txn_kinds)
    }}}
      Init #d @ k; ⊤
    {{{
      γ' (l: loc), RET #l;
      "Htwophase" ∷ is_twophase_pre
        l γ γ' dinit (dom (gset addr) mt)
    }}}
    {{{ ∃ γ' logm',
      is_txn_durable γ' dinit logm' ∗
      (⌜ γ' = γ ⌝ ∨ txn_cinv Nbuftxn γ γ')
    }}}.
  Proof.
    iIntros (HinvN HwalN Hvalids Φ Φc) "Hpre HΦ".
    iNamed "Hpre".
    wpc_call.
    {
      iExists _, _.
      iFrame.
      auto.
    }
    wpc_apply (wpc_MkTxn Nbuftxn with "Htxn_durable").
    1-2: solve_ndisj.
    iSplit.
    {
      iDestruct "HΦ" as "[HΦ _]".
      iFrame.
    }
    iModIntro.
    iIntros (? txnl) "
      (#Histxn&#Histxn_system&Htxn_cancel&#Htxn_cinv&%Htxn_kinds)
    ".
    iApply wpc_cfupd.
    iCache with "HΦ Htxn_cancel".
    {
      iDestruct "HΦ" as "[HΦ _]".
      iModIntro.
      iMod "Htxn_cancel"; first by lia.
      iMod "Htxn_cancel".
      iDestruct "Htxn_cancel" as (?) "Htxn_cancel".
      iModIntro.
      iApply "HΦ".
      iExists _, _.
      iFrame "∗ #".
      auto.
    }
    wpc_frame.
    iMod (twophase_init_locks with "Histxn_system Hmapstos") as "?".
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
    wp_apply (
      wp_MkLockMap _ (twophase_linv_flat 0 jrnl_mapsto_own γ γ')
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
    iFrame (Htxn_kinds) "#".
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

  Theorem wp_TwoPhase__Begin' N prel γ γ' dinit objs_dom j K (ls: sval) e1 :
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
    wp_apply (wp_TwoPhase__Begin_raw with "[$]"); first by assumption.
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

  Theorem wp_TwoPhase__CommitNoRelease' l γ γ' dinit objs_dom j K {HCTX: LanguageCtx K} e1 v :
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
        ) as "> [Hmapstos Htoks]"; [eassumption|set_solver|].
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

  Theorem twophase_started_abort l γ γ' dinit objs_dom j K {HCTX: LanguageCtx K} e1 e2 :
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
        twophase_crash_inv_pred jrnl_mapsto_own γ a (committed vobj)
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
  Proof. Admitted.

  Theorem wp_TwoPhase__ReadBuf' l γ γ' dinit objs_dom j K0 K
          {Hctx: LanguageCtx'
            (ext := @spec_ext_op_field _)
            (ffi := (spec_ffi_model_field))
            (ffi_semantics := (spec_ext_semantics_field))
            K} e1 a sz :
    {{{
      is_twophase_started l γ γ' dinit objs_dom j K0 e1
        (K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
          ReadBufOp (PairV (addr2val' a) #sz)))
    }}}
      TwoPhase__ReadBuf' #l (addr2val a, #sz)
    {{{ v, RET (val_of_obj v);
        is_twophase_started l γ γ' dinit objs_dom j K0 e1
          (K (val_of_obj' v))
    }}}.
  Proof. Admitted.

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
          OverWriteOp (PairV (addr2val' a) (val_of_obj' ov)))) }}}
      TwoPhase__OverWrite' #l (addr2val a, val_of_obj ov)
    {{{ RET #();
        is_twophase_started l γ γ' dinit objs_dom j K0
                            e1 (K #())
    }}}.
  Proof. Admitted.

  Lemma twophase_started_step_puredet l γ γ' dinit objs_dom j K0 K
        `{Hctx: LanguageCtx'
          (ext := @spec_ext_op_field _)
          (ffi := (spec_ffi_model_field))
          (ffi_semantics := (spec_ext_semantics_field))
          K} e0 e1 e2:
    (∀ σ, prim_step' e1 σ [] e2 σ []) →
    is_twophase_started l γ γ' dinit objs_dom j K0 e0 (K e1) -∗
    is_twophase_started l γ γ' dinit objs_dom j K0 e0 (K e2).
  Proof. Admitted.

  Lemma twophase_started_ub_det l γ γ' dinit objs_dom E j K0 K
        `{Hctx: LanguageCtx'
          (ext := @spec_ext_op_field _)
          (ffi := (spec_ffi_model_field))
          (ffi_semantics := (spec_ext_semantics_field))
          K} e0 e :
    nclose sN ⊆ E →
    (∀ s, stuck' e s) →
    is_twophase_started l γ γ' dinit objs_dom j K0 e0 (K e)
    -∗ |NC={E}=> False.
  Proof. Admitted.

End proof.
