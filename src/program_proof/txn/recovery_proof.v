From Perennial.Helpers Require Import Transitions NamedProps Map range_set gset.
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
  "His_txn_always" ∷ is_txn_state γ logm crash_heaps.

Lemma dom_blocks_to_map_u64 {A} (f: Block → A) (bs: list Block) :
  dom (gset u64) (list_to_map (imap (λ i x, (U64 (513 + i), f x)) bs) : gmap u64 _) =
  rangeSet 513 (length bs).
Proof.
  rewrite dom_list_to_map_L.
  rewrite fmap_imap /=.
  change (λ n, fst ∘ _) with (λ (n:nat) (_:Block), U64 (513 + n)).
  rewrite /rangeSet.
  f_equal.
  remember 513 as start. clear Heqstart.
  generalize dependent start.
  induction bs; simpl; intros.
  - reflexivity.
  - rewrite -> seqZ_cons by lia.
    replace (Z.succ start) with (start + 1) by lia.
    replace (Z.pred (S (length bs))) with (Z.of_nat $ length bs) by lia.
    rewrite fmap_cons.
    replace (start + 0%nat) with start by lia.
    f_equal.
    rewrite -IHbs.
    apply imap_ext; intros; simpl.
    f_equal.
    lia.
Qed.

Lemma dom_blocks_to_map_Z {A} (f: Block → A) (bs: list Block) :
  dom (gset Z) (list_to_map (imap (λ i x, (513 + i, f x)) bs) : gmap Z _) =
  list_to_set (seqZ 513 (length bs)).
Proof.
  rewrite dom_list_to_map_L.
  rewrite fmap_imap /=.
  change (λ n, fst ∘ _) with (λ (n:nat) (_:Block), (513 + n)).
  f_equal.
  remember 513 as start. clear Heqstart.
  generalize dependent start.
  induction bs; simpl; intros.
  - reflexivity.
  - rewrite -> seqZ_cons by lia.
    replace (Z.succ start) with (start + 1) by lia.
    replace (Z.pred (S (length bs))) with (Z.of_nat $ length bs) by lia.
    replace (start + 0%nat) with start by lia.
    f_equal.
    rewrite -IHbs.
    apply imap_ext; intros; simpl.
    lia.
Qed.

Lemma lookup_list_to_map K `{Countable K} A (l: list (K * A)) k v :
  list_to_map (M:=gmap K A) l !! k = Some v → (k, v) ∈ l.
Proof.
  induction l; simpl.
  - inversion 1.
  - destruct (decide (k = a.1)); subst.
    + rewrite lookup_insert.
      inversion 1; subst.
      destruct a; simpl.
      constructor.
    + rewrite lookup_insert_ne //.
      intros Hin%IHl.
      apply elem_of_list_further; auto.
Qed.

Lemma wal_heap_inv_init (γwalnames: wal_names) bs :
  513 + Z.of_nat (length bs) < 2^64 →
  ⊢ |==> ∃ γheapnames, wal_heap_inv γheapnames (log_state0 bs).
Proof.
  intros Hbound.
  rewrite /wal_heap_inv.

  set (gh:=list_to_map (imap (λ (i:nat) b, (U64 (513 + i), HB b [])) bs) : gmap u64 _).
  set (crash_heap0:=list_to_map (imap (λ (i:nat) b, (U64 (513 + i), b)) bs) : gmap u64 _).
  set (crash_heaps:=Build_async crash_heap0 []).

  iMod (alloc_heapspec_init_ghost_state γwalnames) as (γheapnames Heq1) "?"; iNamed.
  iNamed "Hinit".

  iMod (gen_heap_alloc_gen _ gh with "wal_heap_h") as "(wal_heap_h & wal_heap_mapsto)".
  { apply map_disjoint_empty_r. }
  rewrite right_id_L.
  iMod (ghost_var_update (list_to_map (imap (λ (i : nat) (x : Block), (513 + i, x)) bs), [(U64 0, [])])
       with "wal_heap_txns") as "[wal_heap_txns1 wal_heap_txns2]".
  iMod (ghost_var_update crash_heaps with "wal_heap_crash_heaps")
       as "H".
  iEval (rewrite -Qp_three_quarter_quarter) in "H".
  iDestruct (fractional.fractional_split with "H") as "[wal_heap_crash_heaps1 wal_heap_crash_heaps2]".

  iModIntro.

  simpl.
  iExists γheapnames, gh, (Build_async crash_heap0 []).
  iSplit.
  { iPureIntro.
    rewrite dom_blocks_to_map_u64.
    rewrite dom_blocks_to_map_Z.
    apply gset_eq; intros.
    rewrite elem_of_map.
    rewrite elem_of_list_to_set.
    rewrite elem_of_seqZ.
    split; intros.
    - destruct H as [i [-> Hlookup]].
      apply rangeSet_lookup in Hlookup; word.
    - exists (U64 x).
      rewrite -> rangeSet_lookup by word.
      word.
  }

  iFrame.
  iSplit.
  { iPureIntro.
    simpl.
    apply map_Forall_lookup; intros.
    apply lookup_list_to_map in H.
    apply elem_of_lookup_imap in H as (idx & b & [=] & Hlookup); subst.
    admit. }
  iSplit.
  { iPureIntro.
    apply log_state0_wf. }
  rewrite /wal_heap_inv_crashes /=.
  iSplit; first by auto.
  rewrite /wal_heap_inv_crash.

  rewrite right_id.
  iPureIntro. (* TODO(tej): all resources are leftover, should be in postcondition *)
  intros.
  simpl.
  rewrite /crash_heap0.
  admit. (* annoying Z vs u64 difference *)
Admitted.

Lemma is_txn_durable_init dinit (kinds: gmap u64 bufDataKind) bs :
  513 + Z.of_nat (length bs) < 2^64 →
  0 d↦∗ repeat block0 513 ∗ 513 d↦∗ bs -∗
 |={⊤}=> ∃ γ, is_txn_durable γ dinit ∗
         (* TODO: for each block, we need a bunch of mapsto_txns for all of the
         objects in that block (easy for blocks, harder for inodes and bits) *)
         ([∗ map] a ↦ K ∈ kinds,
          match K with
          | KindBit => emp
          | KindInode => emp
          | KindBlock => mapsto_txn γ (a, U64 0) (existT KindBlock (bufBlock block0))
          end).
Proof.
  iIntros (Hbound) "H".
  iMod (is_wal_inner_durable_init dinit with "H") as (γwalnames) "[Hwal Hwal_res]".

  iMod (wal_heap_inv_init γwalnames bs) as (γheapnames Heq1) "Hheap"; first done.

  iMod (alloc_txn_init_ghost_state γheapnames kinds) as (γ Heq2 Heq3)  "Htxn".

  (* TODO: set ghost state *)

  iModIntro. iExists γ.
Abort.

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

Theorem mapsto_txn_alloc {T} (γ : gname) (logm : gmap addr T) :
  map_ctx γ 1 ∅
  ==∗
  ∃ m,
    ⌜dom (gset addr) m = dom (gset addr) logm⌝ ∗
    map_ctx γ 1 m ∗
    ([∗ map] a↦_ ∈ logm, ∃ (γm : gname), a [[γ]]↦ γm ∗ ghost_var γm (1/2) true) ∗
    ([∗ map] _↦γm ∈ m, ghost_var γm (1/2) true).
Proof.
  iIntros "H".
  iInduction logm as [|a v m] "IH" using map_ind.
  { iModIntro. iExists _. iFrame. rewrite !big_sepM_empty. rewrite !dom_empty_L. done. }
  iMod ("IH" with "H") as (m0) "(%Hdom & H & H0 & H1)".
  assert (m0 !! a = None).
  { apply not_elem_of_dom in H. apply not_elem_of_dom. rewrite Hdom. eauto. }
  iMod (ghost_var_alloc true) as (γm) "[Hγ0 Hγ1]".
  iMod (map_alloc a γm with "H") as "[H Ha]"; eauto.
  iModIntro. iExists _. iFrame "H". iSplit.
  { iPureIntro. rewrite !dom_insert_L Hdom. done. }
  iSplitL "H0 Hγ0 Ha".
  { iApply big_sepM_insert; eauto. iFrame. iExists _. iFrame. }
  iApply big_sepM_insert; eauto. iFrame.
Qed.

Lemma crash_heaps_match_heapmatch_latest γ logm crash_heaps :
    "Hmetactx" ∷ map_ctx γ.(txn_metaheap) 1 ∅ ∗
    "Hcrash_heaps0" ∷ ([∗ map] a↦b ∈ latest crash_heaps, ∃ hb,
     ⌜hb_latest_update hb = b⌝ ∗
     mapsto (hG:=γ.(txn_walnames).(wal_heap_h)) a 1 hb) ∗
    "Hcrashheapsmatch" ∷ crash_heaps_match γ logm crash_heaps ==∗
    ∃ metam,
    map_ctx γ.(txn_metaheap) 1 metam ∗
    "Hheapmatch" ∷ ( [∗ map] blkno ↦ offmap;metamap ∈ gmap_addr_by_block (latest logm);gmap_addr_by_block metam,
      ∃ installed bs blockK,
        "%Htxn_hb_kind" ∷ ⌜ γ.(txn_kinds) !! blkno = Some blockK ⌝ ∗
        "Htxn_hb" ∷ mapsto (hG := γ.(txn_walnames).(wal_heap_h)) blkno 1 (HB installed bs) ∗
        "Htxn_in_hb" ∷ bufDataTs_in_block installed bs blkno blockK offmap metamap ) ∗
    "Hmapsto_txns" ∷ ([∗ map] addr↦bufData ∈ latest logm, ∃ γm, ptsto_mut γ.(txn_metaheap) addr 1 γm ∗ ghost_var γm (1/2) true).
Proof.
  iNamed 1.
  iMod (mapsto_txn_alloc _ logm.(latest) with "Hmetactx") as (metam) "(%Hdom & Hmetactx' & H0 & H1)".

  rewrite /crash_heaps_match /possible.
  rewrite big_sepL2_snoc.
  iDestruct "Hcrashheapsmatch" as "[_ Hlatestmatch]".
  rewrite /crash_heap_match.

  iModIntro. iExists _. iFrame "Hmetactx'".
  iFrame "H0".

  iDestruct (big_sepM2_flip with "Hlatestmatch") as "Hlatestmatch".
  iDestruct (big_sepM2_sepM_merge with "[$Hlatestmatch $Hcrash_heaps0]") as "Hlatestmatch".
  iDestruct (big_sepM2_flip with "Hlatestmatch") as "Hlatestmatch".

  iDestruct (big_sepM2_sepM_1 with "Hlatestmatch") as "Hlatestmatch".
  iDestruct (gmap_addr_by_block_big_sepM with "H1") as "H1".
  iDestruct (big_sepM_sepM2_merge with "[$Hlatestmatch $H1]") as "H".
  { eapply gmap_addr_by_block_dom_eq; eauto. }

  iApply (big_sepM2_mono with "H").
  iIntros (k y1 y2 Hky1 Hky2) "[H0 H1]".
  iDestruct "H0" as (y0) "(%Hcl & H0 & H2)".
  iDestruct "H0" as (block) "[%Hk H0]". iNamed "H0".
  iDestruct "H2" as (hb) "[%Hb Hmapsto]".
  destruct hb.
  iExists _, _, _. iFrame. iFrame "%".

  rewrite /bufDataTs_in_block /bufDataTs_in_crashblock.
  iDestruct (big_sepM_sepM2_merge with "[$Htxn_in_cb $H1]") as "H1".
  { eapply gmap_addr_by_block_dom_eq2; eauto. }

  iApply (big_sepM2_mono with "H1").
  iIntros (k0 y3 y4 Hky3 Hky4) "[%Hblk H]".
  iExists _. iFrame. iPureIntro.
  rewrite -Hb in Hblk. eauto.
Qed.

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

Lemma latest_wal_heap_h_mapsto_split (γ: gen_heapG u64 heap_block Σ) gh :
  ([∗ map] a ↦ b ∈ gh, ∃ hb, ⌜hb_latest_update hb = b⌝ ∗ mapsto (hG:=γ) a 1 hb) ⊣⊢
  ([∗ map] a ↦ b ∈ gh, ∃ hb, ⌜hb_latest_update hb = b⌝ ∗ mapsto (hG:=γ) a (1/2) hb) ∗
  ([∗ map] a ↦ b ∈ gh, ∃ hb, ⌜hb_latest_update hb = b⌝ ∗ mapsto (hG:=γ) a (1/2) hb).
Proof.
  rewrite -big_sepM_sep.
  repeat f_equiv.
  iSplit.
  - iDestruct 1 as (hb <-) "[H1 H2]".
    iSplitL "H1"; eauto with iFrame.
  - iDestruct 1 as "[H1 H2]".
    iDestruct "H1" as (hb <-) "H1".
    iDestruct "H2" as (hb' <-) "H2".
    iDestruct (mapsto_agree with "H1 H2") as %<-.
    iCombine "H1 H2" as "H".
    eauto.
Qed.

(*
Definition txn_pre_exchange γ γ' : iProp Σ :=
 (∃ σs : async (gmap addr object), "H◯async" ∷ ghost_var γ'.(txn_crashstates) (3/4) σs ∗
              heapspec_durable_exchanger γ.(txn_walnames) (length (possible σs) - 1)).

Definition txn_post_exchange γ γ' : iProp Σ :=
 (∃ σs : async (gmap addr object), "H◯async" ∷ ghost_var γ.(txn_crashstates) (3/4) σs).

Definition txn_exchanger (γ γ' : @txn_names Σ) : iProp Σ :=
  ∃ ls ls', heapspec_exchanger ls ls' γ.(txn_walnames) γ'.(txn_walnames) ∗
  (txn_pre_exchange γ γ' ∨ txn_post_exchange γ γ').
*)

Definition txn_resources γ γ' logm : iProp Σ :=
  (∃ logm0 (txn_id : nat),
  "%Hasync_pre" ∷ ⌜ async_prefix logm logm0 ⌝ ∗
  "%Hlen_crash_txn" ∷ ⌜ (length (possible logm) = txn_id + 1)%nat ⌝ ∗
  "%Hlen_compare" ∷ ⌜ (length (possible logm) ≤ length (possible logm0))%nat ⌝ ∗
  "Hlogm" ∷ ghost_var γ'.(txn_crashstates) (3/4) logm ∗
  "Holdlogm" ∷ ghost_var γ.(txn_crashstates) (1/4) logm0 ∗
  "Hmapsto_txns" ∷ ([∗ map] a ↦ v ∈ latest (logm), mapsto_txn γ' a v) ∗
  "Hdurable" ∷ mnat.mnat_own_lb γ'.(txn_walnames).(heapspec.wal_heap_durable_lb) txn_id ∗
  "Hdurable_exchanger" ∷ heapspec_durable_exchanger γ.(txn_walnames) txn_id)%I.


Lemma txn_crash_transform dinit (γ γ': txn_names) logm1 crash_heaps
 (* (Hwalnames_eq : γ'.(txn_walnames) = γ'_txn_walnames) *)
  (Hkinds_eq : γ'.(txn_kinds) = γ.(txn_kinds)) :
  ("His_txn_always" ∷ is_txn_state γ logm1 crash_heaps ∗
  "Htxn_init" ∷ txn_init_ghost_state γ' ∗
  "Hcrash" ∷ ∃ (σ0 σ' : log_state.t) (γ'0 : wal_names),
             ⌜relation.denote log_crash σ0 σ' tt⌝ ∗
             is_wal_inner_durable γ'0 σ' dinit ∗ wal_resources γ'0 ∗
             ▷ (wal_heap_inv γ'.(txn_walnames) σ' ∗
                heapspec_resources γ.(txn_walnames) γ'.(txn_walnames) σ0 σ')) -∗
  (|0={∅}=> ∃ walnames (logm' : async (gmap addr object)),
         let γ' := (γ'<|txn_walnames;wal_heap_walnames := walnames|>) in
         ⌜γ'.(txn_kinds) = γ.(txn_kinds)⌝ ∗ is_txn_durable γ' dinit ∗ txn_resources γ γ' logm').
Proof.
  iNamed 1.
  iDestruct "Hcrash" as (ls1) "HP".
  iDestruct "HP" as (ls2 γ'walnames Hcrashls12) "(Hdur' & Hres' & HP)".
  iNamed "His_txn_always".
  rewrite /txn_resources.

  rewrite /Prec. iDestruct "HP" as "(>Hheap_inv&Hheap_res)".
  rewrite /is_txn_durable.

  rewrite /heapspec_resources.
  iDestruct "Hheap_res" as "(>Hheap_exchanger&>Hlocked_walheap)".
  iDestruct (heapspec_exchange_crash_heaps with "[$] [$]") as "(Hheap_exchange&Hnew)".
  iDestruct "Hnew" as "(Hheap_lb_exchange&Hcrash_heaps0)".
  iNamed "Hcrash_heaps0".

  iDestruct (wal_heap_inv_wf with "Hheap_inv") as %Hls2wf.
  iNamed "Htxn_init".
  iDestruct (big_sepL2_length with "Hcrashheapsmatch") as %Hlen_logm.
  assert (length ls2.(log_state.txns) ≤ length (possible logm1))%nat.
  { rewrite Hlen_logm -Hlenold //=.
    apply log_crash_txns_length. auto. }
  assert (0 < length ls2.(log_state.txns))%nat.
  { destruct Hls2wf. lia. }

  iMod (ghost_var_update (async_take (length ls2.(log_state.txns)) logm1) with "crashstates")
       as "crashstates".
  iDestruct (crash_heaps_match_async_take γ _ _ (length ls2.(log_state.txns)) with "Hcrashheapsmatch")
       as "#Hcrashheapsmatch'"; auto.
  iDestruct (crash_heaps_match_transfer_gname _ γ' with "Hcrashheapsmatch'") as "#Hcrashheapsmatch_new".
  { auto. }

  iMod (map_alloc_many (async_take (length ls2.(log_state.txns)) logm1).(latest) with "logheap")
    as "[logheap Hlatest]".
  { intros. apply lookup_empty. }

  iMod (crash_heaps_match_heapmatch_latest γ' with "[$Hcrashheapsmatch_new $metaheap $Hcrash_heaps0]") as
     (metam_new) "(metaheap&Heapmatch_new&Hpts)".

  iExists _.
  iExists (async_take (length ls2.(log_state.txns)) logm1).
  iSplitL ""; first eauto.


  iEval (rewrite -Qp_quarter_three_quarter) in "crashstates".
  iDestruct (fractional.fractional_split_1 with "crashstates") as
      "[crashstates1 crashstates2]".
  iDestruct (heapspec_durable_exchanger_dup with "[$]")
            as "(Hheap_lb_exchange1&Hheap_lb_exchange2)".
  iSplitR "Hcrashstates crashstates2 Hheap_lb_exchange2 Hheap_exchange Hpts Hlatest"; last first.
  { iModIntro. iExists _, ((length ls2.(log_state.txns)) - 1)%nat. iFrame.
    iSplitL "".
    {
      iPureIntro. apply async_take_async_prefix; lia.
    }
    iSplitL "".
    { iPureIntro. rewrite /async_take.
      rewrite possible_list_to_async; last first.
      { rewrite take_length. lia. }
      { rewrite take_length. lia. }
    }
    iSplitL "".
    { iPureIntro. rewrite /async_take.
      rewrite possible_list_to_async; last first.
      { rewrite take_length. lia. }
      { rewrite take_length. lia. }
    }
    iCombine "Hpts Hlatest" as "Hpts".
    rewrite -big_sepM_sep.
    iSplitL "Hpts".
    {
      iApply (big_sepM_mono with "Hpts").
      iIntros (???) "(H1&H2)".
      iDestruct "H1" as (γm) "(H1a&H1b)".
      iExists γm. iFrame.
    }
    iNamed "Hheap_exchange". simpl.
    rewrite (wal_post_crash_durable_lb_length_txns ls2); first iFrame "#".
    eapply log_crash_to_post_crash; eauto.
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
Qed.

  Definition txn_cfupd_cancel E dinit k γ' : iProp Σ :=
    (<bdisc> (|C={E}_k=>
              ▷ ∃ walnames,
               let γ' := (γ' <| txn_walnames; wal_heap_walnames := walnames |>) in
               is_txn_durable γ' dinit)).

Definition txn_cfupd_res E γ γ' : iProp Σ :=
  (<bdisc> (|C={E}_0=> ▷ ∃ walnames logm,
               let γ' := (γ' <| txn_walnames; wal_heap_walnames := walnames |>) in
               txn_resources γ γ' logm)).

Theorem wpc_MkTxn E (d:loc) dinit (γ:txn_names) k :
  ↑walN ⊆ E →
  ↑invN ⊆ E →
  {{{ is_txn_durable γ dinit }}}
    MkTxn #d @ k; ⊤
  {{{ γ' (l: loc), RET #l;
      is_txn l γ dinit ∗
      txn_cfupd_cancel E dinit 0 γ' ∗
      txn_cfupd_res E γ γ' }}}
  {{{ ∃ γ' logm', ⌜ txn_kinds γ' = txn_kinds γ ⌝ ∗ is_txn_durable γ' dinit
      ∗ (⌜ γ' = γ ⌝ ∨ txn_resources γ γ' logm') }}}.
Proof.
  iIntros (?? Φ Φc) "Hdur HΦ".
  rewrite /MkTxn. wpc_pures.
  { crash_case. iExists _, _. iFrame. eauto. }

  iCache with "Hdur HΦ".
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
  wpc_apply (wpc_MkLog_recover dinit P (↑walN) _ _ _ _ Prec Pcrash
            with "[] [$His_wal_inner_durable Hwal_res Hwal_heap_inv Hheapspec_init]").
  - auto.
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
      iIntros "Hcrash HC".
      iPoseProof (txn_crash_transform with "[$]") as "Htransform".
      { auto. }
      iDestruct (fupd_level_le _ _ _ k with "Htransform") as "Htransform".
      { lia. }
      iMod (fupd_level_mask_mono with "Htransform") as "Htransform"; auto.
      iModIntro. iApply "HΦ".
      iDestruct "Htransform" as (??) "(?&?&?)".
      iExists _, _. iFrame.
    }
    iNext. iIntros (γ'' l) "(#Hwal & Hwal_cfupd & #Hwal_cinv)".
    iApply wpc_fupd.
    iApply wpc_cfupd.
    wpc_frame_compl "Hlock Hlocked_walheap".
    {
      iLeft in "HΦ".
      iModIntro.
      iIntros "HC".
      iSpecialize ("Hwal_cfupd" with "[$]").
      iPoseProof (fupd_level_le _ _ _ k with "Hwal_cfupd") as "Hwal_cfupd"; first lia.
      iMod (fupd_level_mask_mono with "Hwal_cfupd") as "Hwal_cfupd"; auto.
      iPoseProof (txn_crash_transform with "[$His_txn_always $Htxn_init Hwal_cfupd]") as "Htransform".
      { auto. }
      { iDestruct "Hwal_cfupd" as (??) "H".
        iExists _, _, _. iFrame.
      }
      iDestruct (fupd_level_le _ _ _ k with "Htransform") as "Htransform".
      { lia. }
      iMod (fupd_level_mask_mono with "Htransform") as "Htransform"; auto.
      iModIntro. iApply "HΦ".
      iDestruct "Htransform" as (??) "(?&?&?)".
      iExists _, _. iFrame.
    }
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
    iModIntro.
    iNamed 1.
    rewrite /wal_cfupd_cancel.
    iDestruct (own_discrete_laterable with "Hwal_cfupd") as (Pwal_tok) "(HPwal_tok&#HPwal_tok_wand)".
    iMod (ncinv_cinv_alloc' invN _ E
            (is_txn_always γ ∗ Pwal_tok ∗ txn_init_ghost_state γ')
            (∃ walnames logm',
                let γ' := (γ'<|txn_walnames;wal_heap_walnames := walnames|>) in
                txn_resources γ γ' logm')%I
            (∃ walnames,
                let γ' := (γ'<|txn_walnames;wal_heap_walnames := walnames|>) in
                is_txn_durable γ' dinit)%I
      with "[] [His_txn_always HPwal_tok Htxn_init]") as "(#Htxn_inv&Hcfupd)".
    { set_solver. }
    { iIntros "!> (>H&?&>Hinit) #HC".
      iSpecialize ("Hwal_cinv" with "[$]").
      iMod ("HPwal_tok_wand" with "[$]") as "Hwal_cfupd".
      iSpecialize ("Hwal_cfupd" with "HC").
      iDestruct "H" as (??) "H".
      iMod (fupd_level_mask_mono with "Hwal_cfupd") as "Hwal_cfupd".
      { solve_ndisj. }
      iPoseProof (txn_crash_transform _ γ γ' with "[H Hwal_cfupd Hinit]") as "Htransform".
      { auto. }
      { iFrame "H Hinit".
        iDestruct "Hwal_cfupd" as (??) "(?&?&?&?)".
        iExists _, _, _. iFrame.
      }
      iMod (fupd_level_mask_mono with "Htransform") as "Htransform"; auto.
      { set_solver+. }
      iModIntro.
      iDestruct "Htransform" as (???) "(Hdur&Hres)".
      iSplitR "Hdur".
      { iNext. iExists _, _. iFrame. }
      { iNext. iExists _. iFrame. }
    }
    { iNext. iFrame. iExists _, _; iFrame. }
    iDestruct "Hcfupd" as "(Hcfupd_cancel&Hcfupd)".
    iRight in "HΦ".
    iApply "HΦ".
    iSplitL "".
    {
      iExists _, _; iFrame "#".
      iSplitL.
      - iApply (is_wal_alter with "Hwal").
        do 2 iModIntro. iClear "#".
        rewrite /P.
        iIntros (?) "[$ $]".
        iIntros (?) "$".
      -  iApply (ncinv_alter with "Htxn_inv").
         iIntros "!> !> !> (H&?)".
         iFrame. eauto.
    }
    iModIntro. iFrame "Hcfupd_cancel".
    rewrite /txn_cfupd_res.
    rewrite /txn_cfupd_cancel.
    iFrame.
    Unshelve.
    (* XXX: track this down. *)
    { exact (Build_async (∅: gmap addr object) []). }
    { exact (Build_async (∅: gmap addr object) []). }
    { exact (U64 0). }
Qed.

End goose_lang.
