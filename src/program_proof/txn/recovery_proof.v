From Perennial.Helpers Require Import Transitions NamedProps Map.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.algebra Require Import auth_map log_heap.

From Goose.github_com.mit_pdos.goose_nfsd Require Import txn.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import wal.specs wal.lib wal.heapspec addr.addr_proof buf.buf_proof disk_lib.
From Perennial.program_proof Require Import txn.invariant.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.
Section goose_lang.
Context `{!txnG Σ}.

Implicit Types (γ: @txn_names Σ).

Definition txn_init_ghost_state γ : iProp Σ :=
  let logm0 := Build_async (∅: gmap addr object) [] in
  "logheap" ∷ log_heap_ctx (hG:=γ.(txn_logheap)) logm0 ∗
  "crashstates" ∷ ghost_var γ.(txn_crashstates) 1 logm0 ∗
  "metaheap" ∷ map_ctx γ.(txn_metaheap) 1 (∅ : gmap addr gname).

Lemma alloc_txn_init_ghost_state (γtxn_walnames: wal_heap_gnames) kinds :
  ⊢ |==> ∃ γ, ⌜γ.(txn_walnames) = γtxn_walnames⌝ ∗
              ⌜γ.(txn_kinds) = kinds⌝ ∗
              txn_init_ghost_state γ.
Proof.
  set (logm:=Build_async (∅: gmap addr object) []).
  iMod (seq_heap_init logm) as (txn_logheap) "[? _]".
  iMod (ghost_var_alloc logm) as (txn_crashstates) "?".
  iMod (map_init (∅ : gmap addr gname)) as (txn_metaheap) "?".
  iModIntro.
  iExists (Build_txn_names _ _ _ _ _ _).
  rewrite /txn_init_ghost_state /=.
  by iFrame.
Qed.

(* Definitely missing the durable invariant of the heapspec layer, which should
say something more complete about [γ.(txn_walnames)]. Otherwise there probably
isn't enough to relate the state inside [is_txn_always] to that in
[is_wal_inner_durable]. *)

Definition is_txn_durable γ dinit : iProp Σ :=
  ∃ ls' logm crash_heaps,
  "%Hpostcrash" ∷ ⌜ wal_post_crash ls' ⌝ ∗
  "His_wal_inner_durable" ∷ is_wal_inner_durable γ.(txn_walnames).(wal_heap_walnames) ls' dinit ∗
  "Hwal_res" ∷ wal_resources γ.(txn_walnames).(wal_heap_walnames) ∗
  "Hwal_heap_inv" ∷ wal_heap_inv γ.(txn_walnames) ls' ∗
  "Hlocked_walheap" ∷ is_locked_walheap γ.(txn_walnames) {| locked_wh_σd := ls'.(log_state.d);
                        locked_wh_σtxns := ls'.(log_state.txns);
                    |} ∗
  "His_txn_always" ∷ is_txn_state γ logm crash_heaps ∗
  (* ⌜ lb < length ls'.(log_state.txns) ⌝%nat ∗ *)
  (* XXX this is already in is_txn_state
     "Hcrash_heaps" ∷ ghost_var γ.(txn_walnames).(wal_heap_crash_heaps) (3/4) crash_heaps ∗ *)
  "Hgh_ptsto" ∷ ([∗ map] a↦b ∈ latest crash_heaps, ∃ hb,
    ⌜hb_latest_update hb = b⌝ ∗
    mapsto (hG:=γ.(txn_walnames).(wal_heap_h)) a 1 hb).

Definition txn_resources γ logm : iProp Σ :=
  "Hlogm" ∷ ghost_var γ.(txn_crashstates) (3/4) logm ∗
  "Hmapsto_txns" ∷ ([∗ map] a ↦ v ∈ latest (logm), mapsto_txn γ a v).

Definition crash_heap_match γ logmap walheap : iProp Σ :=
  ([∗ map] blkno ↦ offmap;walblock ∈ gmap_addr_by_block logmap;walheap,
        ∃ blockK,
       "%Htxn_cb_kind" ∷ ⌜ γ.(txn_kinds) !! blkno = Some blockK ⌝ ∗
       "Htxn_in_cb" ∷ bufDataTs_in_crashblock walblock blkno blockK offmap)%I.

Definition crash_heaps_match γ logm crash_heaps : iProp Σ :=
  ([∗ list] logmap;walheap ∈ possible logm;possible crash_heaps, crash_heap_match γ logmap walheap).

Lemma crash_heaps_match_async_take γ logm crash_heaps n :
  (0 < n)%nat →
  (n ≤ length (possible logm))%nat →
  crash_heaps_match γ logm crash_heaps -∗
  crash_heaps_match γ (async_take n logm) (async_take n crash_heaps).
Proof.
  rewrite /crash_heaps_match.
  iIntros (Hlt Hle) "Hl".
  iDestruct (big_sepL2_length with "Hl") as %Hlen.
  iApply (big_sepL2_prefix with "Hl"); auto.
  - apply async_take_possible_prefix; auto.
  - apply async_take_possible_prefix; auto. lia.
  - rewrite ?possible_list_to_async ?take_length; lia.
Qed.

Lemma crash_heaps_match_transfer_gname γ1 γ2 logm crash_heaps :
  txn_kinds γ2 = txn_kinds γ1 →
  crash_heaps_match γ1 logm crash_heaps -∗
  crash_heaps_match γ2 logm crash_heaps.
Proof. iIntros (Heq) "H". rewrite /crash_heaps_match/crash_heap_match Heq. eauto. Qed.

Lemma alloc_metamap names (m: gmap addr object):
  map_ctx names 1 ∅ ==∗
  ∃ metam,
  map_ctx names 1 metam ∗
  ([∗ map] addr↦bufData;γm ∈ m;metam, ghost_var γm (1/2) true) ∗
  ([∗ map] addr↦bufData;γm ∈ m;metam, ptsto_mut names addr 1 γm ∗ ghost_var γm (1/2) true).
Proof.
  iIntros "Hctx".
  iInduction m as [|i x m] "IH" using map_ind.
  - iExists ∅. rewrite ?big_sepM2_empty //. by iFrame.
  - iMod ("IH" with "Hctx") as (metam) "(H1&H2&H3)".
    iDestruct (big_sepM2_dom with "H2") as %Hdom.
    iMod (ghost_var_alloc true) as (γm) "[Hm1 Hm2]".
    assert (metam !! i = None).
    { apply not_elem_of_dom. rewrite -Hdom.
      apply not_elem_of_dom. eauto. }
    iMod (map_alloc i γm with "[$]") as "(Hctx&Hpts)"; auto.
    iExists (<[i := γm]>metam).
    iFrame. iSplitL "H2 Hm1".
    { rewrite big_sepM2_insert //. by iFrame. }
    { rewrite big_sepM2_insert //. by iFrame. }
Qed.


Lemma crash_heap_match_to_heapmatch γ offmap crash_heap :
    "Hmetactx" ∷ map_ctx γ.(txn_metaheap) 1 ∅ ∗
    "Hcrashheapmatch" ∷ crash_heap_match γ offmap crash_heap ==∗
    ∃ metam,
    "Hmetactx" ∷ map_ctx γ.(txn_metaheap) 1 metam ∗
    "Hmeta_maptso" ∷ ([∗ map] l↦γm ∈ metam, ghost_var γm (1/2) true) ∗
    "Hheapmatch" ∷ ( [∗ map] blkno ↦ offmap;metamap ∈ gmap_addr_by_block offmap;gmap_addr_by_block metam,
      ∃ installed bs blockK,
        "%Htxn_hb_kind" ∷ ⌜ γ.(txn_kinds) !! blkno = Some blockK ⌝ ∗
        "Htxn_hb" ∷ mapsto (hG := γ.(txn_walnames).(wal_heap_h)) blkno 1 (HB installed bs) ∗
        "Htxn_in_hb" ∷ bufDataTs_in_block installed bs blkno blockK offmap metamap ) ∗
    "Hmapsto_txns" ∷ ([∗ map] addr↦bufData;γm ∈ offmap;metam, ptsto_mut γ.(txn_metaheap) addr 1 γm ∗ ghost_var γm (1/2) true).
Proof.
  iNamed 1.
  rewrite /crash_heap_match.
  iMod (alloc_metamap _ offmap with "[$]") as (metam) "(Hctx&H1&H2)".
  iDestruct (gmap_addr_by_block_big_sepM2 with "H1") as "H1".
Abort.


Lemma crash_heaps_match_heapmatch_latest γ logm crash_heaps :
    "Hmetactx" ∷ map_ctx γ.(txn_metaheap) 1 ∅ ∗
    "Hcrashheapsmatch" ∷ crash_heaps_match γ logm crash_heaps ==∗
    ∃ metam,
    map_ctx γ.(txn_metaheap) 1 metam ∗
    "Hheapmatch" ∷ ( [∗ map] blkno ↦ offmap;metamap ∈ gmap_addr_by_block (latest logm);gmap_addr_by_block metam,
      ∃ installed bs blockK,
        "%Htxn_hb_kind" ∷ ⌜ γ.(txn_kinds) !! blkno = Some blockK ⌝ ∗
        "Htxn_hb" ∷ mapsto (hG := γ.(txn_walnames).(wal_heap_h)) blkno 1 (HB installed bs) ∗
        "Htxn_in_hb" ∷ bufDataTs_in_block installed bs blkno blockK offmap metamap ) ∗
    "Hmapsto_txns" ∷ ([∗ map] addr↦bufData ∈ latest logm, ∃ γm, ptsto_mut γ.(txn_metaheap) addr 1 γm ∗ ghost_var γm (1/2) true).
Proof. Admitted.

Definition txn_pre_exchange γ γ' : iProp Σ :=
 (∃ σs : async (gmap addr object), "H◯async" ∷ ghost_var γ'.(txn_crashstates) (3/4) σs ∗
              heapspec_durable_exchanger γ.(txn_walnames) (length (possible σs) - 1)).

Definition txn_post_exchange γ γ' : iProp Σ :=
 (∃ σs : async (gmap addr object), "H◯async" ∷ ghost_var γ.(txn_crashstates) (3/4) σs).

Definition txn_exchanger (γ γ' : @txn_names Σ) : iProp Σ :=
  ∃ ls ls', heapspec_exchanger ls ls' γ.(txn_walnames) γ'.(txn_walnames) ∗
  (txn_pre_exchange γ γ' ∨ txn_post_exchange γ γ').

Global Instance is_txn_always_discretizable γ :
  Discretizable (is_txn_always γ).
Proof. apply _. Qed.

Global Instance is_txn_durable_discretizable γ dinit :
  Discretizable (is_txn_durable γ dinit).
Proof. apply _. Qed.

Lemma log_crash_txns_length ls1 ls2 :
  relation.denote log_crash ls1 ls2 () →
  (length ls2.(log_state.txns) ≤ length ls1.(log_state.txns))%nat.
Proof.
  rewrite log_crash_unfold. intros (?&?&?).
  subst. rewrite /=.
  rewrite -{2}(take_drop (S x) (ls1.(log_state.txns))).
  rewrite app_length. lia.
Qed.

Lemma wal_heap_inv_wf names ls:
  wal_heap_inv names ls -∗
  ⌜ wal_wf ls ⌝.
Proof. iNamed 1. eauto. Qed.

Theorem wpc_MkTxn (d:loc) dinit (γ:txn_names) logm k :
  {{{ is_txn_durable γ dinit ∗ txn_resources γ logm }}}
    MkTxn #d @ k; ⊤
  {{{ (l: loc), RET #l; is_txn l γ dinit ∗ ([∗ map] a ↦ v ∈ latest (logm), mapsto_txn γ a v)
      (* cfupd stuff *) }}}
  {{{ ∃ γ' logm', ⌜ txn_kinds γ' = txn_kinds γ ⌝ ∗ is_txn_durable γ' dinit ∗ txn_resources γ' logm' }}}.
Proof.
  iIntros (Φ Φc) "(Hdur&Hres) HΦ".
  rewrite /MkTxn. wpc_pures.
  { crash_case. iExists _, _. iFrame. eauto. }

  iCache with "Hdur HΦ Hres".
  { crash_case. iExists _, _. iFrame. eauto. }
  wpc_bind (lock.new _).
  wpc_frame; wp_apply (wp_new_free_lock).
  iIntros (lk) "Hlock". iNamed 1.
  wpc_bind (MkLog #d).
  iNamed "Hdur".
  iMod (alloc_heapspec_init_ghost_state (γ.(txn_walnames).(wal_heap_walnames)))
         as (γ'_txn_walnames ?) "Hheapspec_init".
  iMod (alloc_txn_init_ghost_state γ'_txn_walnames γ.(txn_kinds)) as
      (γ' Hwalnames_eq Hkinds_eq) "Htxn_init".
  set (P := λ ls, (wal_heap_inv γ.(txn_walnames) ls ∗ heapspec_init_ghost_state γ'_txn_walnames)%I).
  set (Prec (ls ls': log_state.t) :=
         (wal_heap_inv γ'.(txn_walnames) ls' ∗
          heapspec_resources γ.(txn_walnames) γ'.(txn_walnames) ls ls')%I).
  set (Pcrash (ls ls' : log_state.t) := (True)%I : iProp Σ).
  iApply wpc_cfupd.
  wpc_apply (wpc_MkLog_recover dinit P _ _ _ _ Prec Pcrash
            with "[] [$His_wal_inner_durable Hwal_res Hwal_heap_inv Hheapspec_init]").
  - auto.
  - iIntros "!>" (???) ">HP".
    iDestruct "HP" as "[Hinv Hinit]".
    iMod (wal_heap_inv_crash_transform with "Hinv Hinit") as "[Hinv Hres]"; eauto.
    rewrite /Prec /Pcrash.
    rewrite Hwalnames_eq.
    iModIntro.
    by iFrame.
  - iFrame.
  - iSplit.
    { iLeft in "HΦ".
      iModIntro.
      iIntros "Hcrash".
      iDestruct "Hcrash" as (ls1) "HP".
      iDestruct "HP" as (ls2 γ'walnames Hcrashls12) "(Hdur' & Hres' & HP)".
      iNamed "His_txn_always".
      iNamed "Hres".

      iAssert (C -∗ |0={⊤}=>
                     ∃ γ'0 logm',
                      ⌜γ'0.(txn_kinds) = γ.(txn_kinds)⌝ ∗ is_txn_durable γ'0 dinit ∗
                      txn_resources γ'0 logm' )%I
      with "[-HΦ]" as "Hgoal".
      {

      rewrite /Prec. iDestruct "HP" as "(>Hheap_inv&Hheap_res)".
      rewrite /is_txn_durable.
      iIntros "C".
      iExists (γ'<|txn_walnames;wal_heap_walnames := γ'walnames|>).

      iClear "Hlocked_walheap".
      rewrite /heapspec_resources.
      iDestruct "Hheap_res" as "(>Hheap_exchanger&>Hlocked_walheap)".
      iDestruct (heapspec_exchange_crash_heaps with "[$] [$]") as "(Hheap_exchange&Hnew)".
      iDestruct "Hnew" as "(Hheap_lb_exchange&Hcrash_heaps0)".
      iNamed "Hcrash_heaps0".

      iDestruct (wal_heap_inv_wf with "Hheap_inv") as %Hls2wf.
      iNamed "Htxn_init".
      iDestruct (ghost_var_agree with "Hcrashstates Hlogm") as %->.
      iDestruct (big_sepL2_length with "Hcrashheapsmatch") as %Hlen_logm.
      assert (length ls2.(log_state.txns) ≤ length (possible logm))%nat.
      { rewrite Hlen_logm -Hlenold //=.
        apply log_crash_txns_length. auto. }
      assert (0 < length ls2.(log_state.txns))%nat.
      { destruct Hls2wf. lia. }

      iMod (ghost_var_update (async_take (length ls2.(log_state.txns)) logm) with "crashstates")
           as "crashstates".
      iDestruct (crash_heaps_match_async_take γ _ _ (length ls2.(log_state.txns)) with "Hcrashheapsmatch")
           as "#Hcrashheapsmatch'"; auto.
      iDestruct (crash_heaps_match_transfer_gname _ γ' with "Hcrashheapsmatch'") as "#Hcrashheapsmatch_new".
      { auto. }

      iMod (map_alloc_many (async_take (length ls2.(log_state.txns)) logm).(latest) with "logheap")
        as "[logheap Hlatest]".
      { intros. apply lookup_empty. }

      iMod (crash_heaps_match_heapmatch_latest γ' with "[$Hcrashheapsmatch_new $metaheap]") as
         (metam_new) "(metaheap&Heapmatch_new&Hpts)".

      iExists (async_take (length ls2.(log_state.txns)) logm).
      iSplitL ""; first eauto.


      iEval (rewrite -Qp_quarter_three_quarter) in "crashstates".
      iDestruct (fractional.fractional_split_1 with "crashstates") as
          "[crashstates1 crashstates2]".
      iDestruct (heapspec_durable_exchanger_dup with "[$]")
                as "(Hheap_lb_exchange1&Hheap_lb_exchange2)".
      iSplitR "crashstates2 Hheap_lb_exchange2 Hheap_exchange Hpts Hlatest"; last first.
      { iModIntro. rewrite /txn_exchanger. iFrame.
        iCombine "Hpts Hlatest" as "Hpts".
        rewrite -big_sepM_sep.
        iApply (big_sepM_mono with "Hpts").
        iIntros (???) "(H1&H2)".
        iDestruct "H1" as (γm) "(H1a&H1b)".
        iExists γm. iFrame.
      }
      iExists ls2, _, _. simpl. iFrame "Hheap_inv Hres' Hdur'".

      iFrame "Hcrash_heaps".
      iSplitL "".
      { iModIntro. iPureIntro. eapply log_crash_to_post_crash; eauto. }
      iFrame.
      iExists metam_new.
      iFrame "# ∗".
      rewrite /log_heap_ctx /=. iEval (rewrite right_id) in "logheap". iFrame "logheap".
      eauto.
      (* TODO: a bunch of resources are getting dropped on the floor *)
      }
      iIntros "HC".
      iSpecialize ("Hgoal" with "[$]").
      iMod (fupd_level_le with "Hgoal"); first lia.
      iApply "HΦ". eauto.
    }
    iNext. iIntros (γ'' l) "(#Hwal & Hwal_cfupd & #Hwal_cinv)".
    wpc_frame_compl "Hlock Hlocked_walheap His_txn_always".
    { admit. }
    rewrite -wp_fupd.
    wp_apply wp_allocStruct; first by val_ty.
    iIntros (txn_l) "Htxn".
    iApply struct_fields_split in "Htxn". iNamed "Htxn".
    wp_pures.
    iMod (readonly_alloc_1 with "mu") as "#mu".
    iMod (readonly_alloc_1 with "log") as "#log".
    iMod (alloc_lock lockN _ _ (is_txn_locked txn_l γ.(txn_walnames))
            with "Hlock [pos Hlocked_walheap]") as "#Htxn_lock".
    { iNext. rewrite /is_txn_locked.
      iExists _, _, _; iFrame. }
    iMod (inv_alloc invN _ (is_txn_always γ) with "[His_txn_always]") as "#Htxn_inv".
    { iNext. iExists _, _; iFrame. }
    iModIntro.
    iNamed 1.
    iRight in "HΦ".
    iApply "HΦ".
    iNamed "Hres".
    iFrame "Hmapsto_txns".
    rewrite /is_txn.
    iExists _, _; iFrame "#".
    iApply (is_wal_alter with "Hwal").
    iModIntro. iClear "#".
    rewrite /P.
    iIntros (?) "[$ $]".
    iIntros (?) "$".
    Unshelve.
    (* XXX: track this down. *)
    exact (U64 0).
    all: fail "goals remaining".
Admitted.

End goose_lang.
