From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From iris.algebra Require Import numbers.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.algebra Require Import deletable_heap log_heap.

From Goose.github_com.mit_pdos.goose_nfsd Require Import txn.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import wal.specs wal.lib wal.heapspec addr.addr_proof buf.buf_proof disk_lib.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.Helpers Require Import NamedProps Map.

Remove Hints fractional.into_sep_fractional : typeclass_instances.

Class txnG (Σ: gFunctors) :=
  {
    txn_boolG :> ghost_varG Σ bool;
    txn_walheapG :> walheapG Σ;
    txn_logheapG :> log_heapPreG addr {K & bufDataT K} Σ;
    txn_metaheapG :> gen_heapPreG addr gname Σ;
    txn_crashstatesG :> ghost_varG Σ (async (gmap addr {K & bufDataT K}));
  }.

Section heap.
Context `{!txnG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition lockN : namespace := nroot .@ "txnlock".
Definition invN : namespace := nroot .@ "txninv".

Record txn_names := {
  txn_logheap : log_heapG addr {K & bufDataT K} Σ;
  txn_metaheap : gen_heapG addr gname Σ;
  txn_walnames : @wal_heap_gnames Σ;
  txn_crashstates : gname;
  txn_kinds : gmap u64 bufDataKind;
}.


Definition mapsto_txn (γ : txn_names) (l : addr) (v : {K & bufDataT K}) : iProp Σ :=
  ∃ γm,
    "Hmapsto_log" ∷ mapsto_cur (hG := γ.(txn_logheap)) l v ∗
    "Hmapsto_meta" ∷ mapsto (hG := γ.(txn_metaheap)) l 1 γm ∗
    "Hmod_frag" ∷ ghost_var γm (1/2) true.

Theorem mapsto_txn_2 {K1 K2} a v0 v1 :
  @mapsto_txn K1 a v0 -∗
  @mapsto_txn K2 a v1 -∗
  False.
Proof.
  rewrite /mapsto_txn.
  iIntros "H0 H1".
  iDestruct "H0" as (g0) "(H0log & H0m & H0own)".
  iDestruct "H1" as (g1) "(H1log & H1m & H1own)".
(*
  rewrite H0 in H2; inversion H2.
  subst.
  apply eq_sigT_eq_dep in H5.
  apply Eqdep_dec.eq_dep_eq_dec in H5; subst.
  2: apply bufDataKind_eq_dec.
  iDestruct (mapsto_valid_2 with "H0m H1m") as %x.
  exfalso; eauto.
*)
Admitted.

Definition bufDataT_in_block (walblock : Block) blockK (blkno off : u64) (bufData : {K & bufDataT K}) : Prop :=
  is_bufData_at_off walblock off (projT2 bufData) ∧
  valid_addr (Build_addr blkno off) ∧
  valid_off (projT1 bufData) off ∧
  blockK = projT1 bufData.

Definition bufDataTs_in_block (installed : Block) (bs : list Block) (blkno : u64) blockK
                              (offmap : gmap u64 {K & bufDataT K})
                              (metamap : gmap u64 gname) : iProp Σ :=
  ( [∗ map] off ↦ bufData;γm ∈ offmap;metamap,
      ∃ (modifiedSinceInstall : bool),
      "%Hoff_in_block" ∷ ⌜ bufDataT_in_block (latest_update installed bs) blockK blkno off bufData ⌝ ∗
      "Hoff_own" ∷ ghost_var γm (1/2) modifiedSinceInstall ∗
      "%Hoff_prefix_in_block" ∷ ⌜ if modifiedSinceInstall then True else
        ∀ prefix,
          bufDataT_in_block (latest_update installed (take prefix bs)) blockK blkno off bufData ⌝
  )%I.

Global Instance bufDataTs_in_block_timeless installed bs blkno blockK offmap metamap :
  Timeless (bufDataTs_in_block installed bs blkno blockK offmap metamap) := _.

Definition bufDataTs_in_crashblock (walblock : Block) (blkno : u64) blockK
                                   (offmap : gmap u64 {K & bufDataT K}) : iProp Σ :=
  (* Very similar to txn_bufDataT_in_block *)
  ( [∗ map] off ↦ bufData ∈ offmap,
      ⌜ bufDataT_in_block walblock blockK blkno off bufData ⌝
  )%I.

Definition is_txn_always (γ : txn_names) : iProp Σ :=
  (
    ∃ (logm : async (gmap addr {K & bufDataT K}))
      (metam : gmap addr gname)
      (crash_heaps : async (gmap u64 Block)),
      "Hlogheapctx" ∷ log_heap_ctx (hG := γ.(txn_logheap)) logm ∗
      "Hcrashstates" ∷ ghost_var γ.(txn_crashstates) (1/2) logm ∗
      "Hmetactx" ∷ gen_heap_ctx (hG := γ.(txn_metaheap)) metam ∗
      "Hheapmatch" ∷ ( [∗ map] blkno ↦ offmap;metamap ∈ gmap_addr_by_block (latest logm);gmap_addr_by_block metam,
        ∃ installed bs blockK,
          "%Htxn_hb_kind" ∷ ⌜ γ.(txn_kinds) !! blkno = Some blockK ⌝ ∗
          "Htxn_hb" ∷ mapsto (hG := γ.(txn_walnames).(wal_heap_h)) blkno 1 (HB installed bs) ∗
          "Htxn_in_hb" ∷ bufDataTs_in_block installed bs blkno blockK offmap metamap ) ∗
      "Hcrashheaps" ∷ ghost_var γ.(txn_walnames).(wal_heap_crash_heaps) (1/2) crash_heaps ∗
      "Hcrashheapsmatch" ∷ ( [∗ list] logmap;walheap ∈ possible logm;possible crash_heaps,
        [∗ map] blkno ↦ offmap;walblock ∈ gmap_addr_by_block logmap;walheap,
          ∃ blockK,
            "%Htxn_cb_kind" ∷ ⌜ γ.(txn_kinds) !! blkno = Some blockK ⌝ ∗
            "Htxn_in_cb" ∷ bufDataTs_in_crashblock walblock blkno blockK offmap )
  )%I.

Global Instance is_txn_always_timeless γ :
  Timeless (is_txn_always γ) := _.

Definition is_txn_locked l γ : iProp Σ :=
  (
    ∃ (nextId : u64) (pos : u64) lwh,
      "Hwal_latest" ∷ is_locked_walheap γ lwh ∗
      "Histxn_pos" ∷ l ↦[Txn.S :: "pos"] #pos
 )%I.

Definition is_txn (l : loc) (γ : txn_names) : iProp Σ :=
  (
    ∃ (mu : loc) (walptr : loc),
      "Histxn_mu" ∷ readonly (l ↦[Txn.S :: "mu"] #mu) ∗
      "Histxn_wal" ∷ readonly (l ↦[Txn.S :: "log"] #walptr) ∗
      "Hiswal" ∷ is_wal (wal_heap_inv (txn_walnames γ)) walptr (wal_heap_walnames (txn_walnames γ)) ∗
      "Histxna" ∷ inv invN (is_txn_always γ) ∗
      "Histxn_lock" ∷ is_lock lockN #mu (is_txn_locked l (txn_walnames γ))
  )%I.

Global Instance is_txn_persistent l γ : Persistent (is_txn l γ) := _.

Theorem mapsto_txn_valid γ a v E :
  ↑invN ⊆ E ->
  inv invN (is_txn_always γ) -∗
  mapsto_txn γ a v ={E}=∗
    mapsto_txn γ a v ∗ ⌜ valid_addr a ∧ valid_off (projT1 v) a.(addrOff) ∧ γ.(txn_kinds) !! a.(addrBlock) = Some (projT1 v) ⌝.
Proof.
  iIntros (HN) "#Hinv H".
  iNamed "H".
  iInv invN as ">Halways".
  iNamed "Halways".

  iDestruct (log_heap_valid_cur with "Hlogheapctx Hmapsto_log") as "%Hlogvalid".
  iDestruct (gen_heap_valid with "Hmetactx Hmapsto_meta") as "%Hmetavalid".

  eapply gmap_addr_by_block_lookup in Hlogvalid; destruct Hlogvalid.
  eapply gmap_addr_by_block_lookup in Hmetavalid; destruct Hmetavalid.
  intuition idtac.

  iDestruct (big_sepM2_lookup_acc with "Hheapmatch") as "[Hblockmatch Hheapmatch]"; eauto.
  iNamed "Hblockmatch".
  iNamed "Htxn_in_hb".
  iDestruct (big_sepM2_lookup_acc with "Htxn_in_hb") as "[Hoff Htxn_in_hb]"; eauto.
  iNamed "Hoff".
  iDestruct ("Htxn_in_hb" with "[Hoff_own]") as "Htxn_in_hb"; eauto.
  iDestruct ("Hheapmatch" with "[Htxn_hb Htxn_in_hb]") as "Hheapmatch".
  { iExists _, _, _; iFrame. done. }

  iModIntro.
  iSplitR "Hmapsto_log Hmapsto_meta Hmod_frag".
  { iModIntro. iExists _, _, _. iFrame. }
  iModIntro.
  iSplitL.
  { iExists _. iFrame. }
  iPureIntro.
  unfold bufDataT_in_block in *.
  intuition eauto; congruence.
Qed.

Theorem is_txn_dup l γ :
  is_txn l γ -∗
  is_txn l γ ∗
  is_txn l γ.
Proof.
  iIntros "#$".
Qed.

Theorem wp_txn_Load l γ a v :
  {{{ is_txn l γ ∗
      mapsto_txn γ a v
  }}}
    Txn__Load #l (addr2val a) #(bufSz (projT1 v))
  {{{ (bufptr : loc) b, RET #bufptr;
      is_buf bufptr a b ∗
      ⌜ b.(bufDirty) = false ⌝ ∗
      ⌜ existT b.(bufKind) b.(bufData) = v ⌝ ∗
      mapsto_txn γ a v
  }}}.
Proof using txnG0 Σ.
  iIntros (Φ) "(#Htxn & Hstable) HΦ".
  iNamed "Htxn".
  iNamed "Hstable".

  wp_call.
  wp_loadField.

  wp_call.

  wp_apply (wp_Walog__ReadMem _ (λ mb,
    "Hmapsto_log" ∷ mapsto_cur a v ∗
    "Hmapsto_meta" ∷ mapsto a 1 γm ∗
    match mb with
    | Some b =>
      "Hmod_frag" ∷ ghost_var γm (1/2) true ∗
      "%Hv" ∷ ⌜ is_bufData_at_off b a.(addrOff) (projT2 v) ∧ valid_addr a ⌝
    | None =>
      "Hmod_frag" ∷ ghost_var γm (1/2) false
    end)%I with "[$Hiswal Hmapsto_log Hmapsto_meta Hmod_frag]").
  {
    iApply (wal_heap_readmem (⊤ ∖ ↑walN ∖ ↑invN) with "[Hmapsto_log Hmapsto_meta Hmod_frag]").

    iInv invN as ">Hinv_inner" "Hinv_closer".
    iNamed "Hinv_inner".
    iModIntro.

    iDestruct (log_heap_valid_cur with "Hlogheapctx Hmapsto_log") as "%Hlogvalid".
    iDestruct (gen_heap_valid with "Hmetactx Hmapsto_meta") as "%Hmetavalid".

    eapply gmap_addr_by_block_lookup in Hlogvalid; destruct Hlogvalid.
    eapply gmap_addr_by_block_lookup in Hmetavalid; destruct Hmetavalid.
    intuition idtac.

    iDestruct (big_sepM2_lookup_acc with "Hheapmatch") as "[Hblockmatch Hheapmatch]"; eauto.
    iNamed "Hblockmatch".
    iExists _, _; iFrame "Htxn_hb".

    iNamed "Htxn_in_hb".
    iIntros (mb) "Hrmq".
    destruct mb; rewrite /=.

    {
      iDestruct "Hrmq" as "[Hrmq %]".
      iDestruct (big_sepM2_lookup_acc with "Htxn_in_hb") as "[Hoff Htxn_in_hb]"; eauto.
      iNamed "Hoff".
      iDestruct ("Htxn_in_hb" with "[Hoff_own]") as "Htxn_in_hb"; eauto.
      iDestruct ("Hheapmatch" with "[Hrmq Htxn_in_hb]") as "Hheapmatch".
      { iExists _, _, _. iFrame. done. }
      iDestruct ("Hinv_closer" with "[-Hmapsto_log Hmapsto_meta Hmod_frag]") as "Hinv_closer".
      {
        iModIntro.
        iExists _, _, _. iFrame.
      }

      iMod "Hinv_closer".
      iModIntro. iFrame.
      iPureIntro.
      rewrite /bufDataT_in_block in Hoff_in_block. subst. intuition eauto.
    }

    {
      iDestruct (big_sepM2_delete with "Htxn_in_hb") as "[Hoff Htxn_in_hb]"; eauto.
      iNamed "Hoff".
      iMod (ghost_var_update_halves false with "Hoff_own Hmod_frag") as "[Hoff_own Hmod_frag]".

      iDestruct ("Hinv_closer" with "[-Hmapsto_log Hmapsto_meta Hmod_frag]") as "Hinv_closer".
      {
        iModIntro.
        iExists _, _, _. iFrame.
        iApply "Hheapmatch".
        iExists _, _, _.
        iFrame.
        iSplitR; first by done.
        iDestruct (big_sepM2_mono with "Htxn_in_hb") as "Htxn_in_hb".
        2: {
          iDestruct (big_sepM2_insert_delete with "[$Htxn_in_hb Hoff_own]") as "Htxn_in_hb".
          2: rewrite -> (insert_id x) by eauto.
          2: rewrite -> (insert_id x0) by eauto.
          2: iApply "Htxn_in_hb".
          iExists _. iFrame.
          iSplit; first by done.
          iPureIntro. intros.
          rewrite take_nil /=. eauto.
        }

        iIntros (k y1 y2 Hky1 Hky2) "H".
        iNamed "H". iExists _. iFrame.
        iSplit; first by done.
        iPureIntro. intros.
        destruct modifiedSinceInstall0; eauto.
        intros. rewrite take_nil /=. eauto.
      }

      iMod "Hinv_closer".
      iModIntro.
      iFrame.
    }
  }

  iIntros (ok bl) "Hres".
  destruct ok.
  {
    (* Case 1: hit in the cache *)

    iDestruct "Hres" as (b) "[Hisblock Hres]".
    iNamed "Hres".
    wp_pures.
    rewrite /is_block.
    wp_apply (wp_MkBufLoad with "[$Hisblock]"); eauto.
    iIntros (bufptr) "Hbuf".
    wp_pures.
    iApply "HΦ". iFrame.
    rewrite /=.
    iSplitR; first done.
    destruct v. iSplitR; first done.
    iExists _. iFrame.
  }

  (* Case 2: missed in cache *)
  iNamed "Hres".
  wp_pures.

  wp_apply (wp_Walog__ReadInstalled _
    (λ b,
      "Hmapsto_log" ∷ mapsto_cur a v ∗
      "Hmapsto_meta" ∷ mapsto a 1 γm ∗
      "%Hv" ∷ ⌜ is_bufData_at_off b a.(addrOff) (projT2 v) ∧ valid_addr a ⌝ ∗
      "Hmod_frag" ∷ ghost_var γm (1/2) true
    )%I
    with "[$Hiswal Hmapsto_log Hmapsto_meta Hmod_frag]").
  {
    iSplitR.
    { admit. }

    iApply (wal_heap_readinstalled (⊤ ∖ ↑walN ∖ ↑invN) with "[Hmapsto_log Hmapsto_meta Hmod_frag]").

    iInv invN as ">Hinv_inner" "Hinv_closer".
    iNamed "Hinv_inner".
    iModIntro.

    iDestruct (log_heap_valid_cur with "Hlogheapctx Hmapsto_log") as "%Hlogvalid".
    iDestruct (gen_heap_valid with "Hmetactx Hmapsto_meta") as "%Hmetavalid".

    eapply gmap_addr_by_block_lookup in Hlogvalid; destruct Hlogvalid.
    eapply gmap_addr_by_block_lookup in Hmetavalid; destruct Hmetavalid.
    intuition idtac.

    iDestruct (big_sepM2_lookup_acc with "Hheapmatch") as "[Hblockmatch Hheapmatch]"; eauto.
    iNamed "Hblockmatch".
    iExists _, _; iFrame "Htxn_hb".
    iNamed "Htxn_in_hb".

    iIntros (b) "Hriq".
    iDestruct "Hriq" as "[Hriq %]".

    iDestruct (big_sepM2_lookup_acc with "Htxn_in_hb") as "[Hoff Htxn_in_hb]"; eauto.
    iNamed "Hoff".
    iDestruct (ghost_var_agree with "Hoff_own Hmod_frag") as %->.
    iMod (ghost_var_update_halves true with "Hoff_own Hmod_frag") as "[Hoff_own Hmod_frag]".
    iDestruct ("Htxn_in_hb" with "[Hoff_own]") as "Htxn_in_hb"; eauto.
    iDestruct ("Hheapmatch" with "[Hriq Htxn_in_hb]") as "Hheapmatch".
    { iExists _, _, _. iFrame. done. }

    iFrame.
    iDestruct ("Hinv_closer" with "[-]") as "Hinv_closer".
    {
      iModIntro.
      iExists _, _, _.
      iFrame.
    }

    iMod "Hinv_closer".
    iModIntro.
    iPureIntro.

    apply elem_of_list_lookup_1 in H0.
    destruct H0 as [prefix H0].
    specialize (Hoff_prefix_in_block prefix).
    erewrite latest_update_take_some in Hoff_prefix_in_block by eauto.
    rewrite /bufDataT_in_block in Hoff_prefix_in_block.
    intuition eauto.
  }

  iIntros (bslice) "Hres".
  iDestruct "Hres" as (b) "[Hb Hres]".
  iNamed "Hres".
  wp_pures.
  rewrite /is_block.
  wp_apply (wp_MkBufLoad with "[$Hb]"); eauto.
  iIntros (bufptr) "Hbuf".
  wp_pures.
  iApply "HΦ".
  iFrame.
  iSplitR; first done.
  destruct v.
  iSplitR; first done.
  iExists _. iFrame.
Admitted.

Definition is_txn_buf_pre γ (bufptr:loc) (a : addr) (buf : buf) : iProp Σ :=
  "Hisbuf" ∷ is_buf bufptr a buf ∗
  "Hmapto" ∷ ∃ data, mapsto_txn γ a (existT buf.(bufKind) data).

Definition is_txn_buf_blkno (bufptr : loc) (a : addr) (buf : buf) blkno :=
  ( "Hisbuf" ∷ is_buf bufptr a buf ∗
    "%HaddrBlock" ∷ ⌜a.(addrBlock) = blkno⌝ )%I.

Definition updOffsetsOK blknum diskLatest walBlock K (offmap : gmap u64 buf) : Prop :=
  ∀ off (oldBufData : @bufDataT K),
    valid_addr (Build_addr blknum off) ->
    valid_off K off ->
    is_bufData_at_off diskLatest off oldBufData ->
    match offmap !! off with
    | None => is_bufData_at_off walBlock off oldBufData
    | Some buf => is_bufData_at_off walBlock off buf.(bufData) ∧
      buf.(bufKind) = K
    end.

Definition updBlockOK blknum walBlock K (locked_wh_disk : disk) (offmap : gmap u64 buf) : Prop :=
  ∀ diskLatest,
    locked_wh_disk !! int.val blknum = Some diskLatest ->
    updOffsetsOK blknum diskLatest walBlock K offmap.

Definition updBlockKindOK blknum walBlock γ (locked_wh_disk : disk) (offmap : gmap u64 buf) : Prop :=
  ∃ K,
    γ.(txn_kinds) !! blknum = Some K ∧
    updBlockOK blknum walBlock K locked_wh_disk offmap.

Lemma valid_off_block blknum off :
  valid_addr (Build_addr blknum off) ->
  valid_off KindBlock off ->
  off = 0.
Proof.
  rewrite /valid_addr /valid_off /bufSz /addr2flat_z; intuition idtac.
  simpl addrOff in *.
  simpl addrBlock in *.
  eapply int_val_inj; first by apply u64_instance.u64_word_ok.
  epose proof (Z_div_exact_2 _ _ _ H0).
  rewrite H3. rewrite H3 in H1.
  assert (0 ≤ int.val off `div` Z.of_nat (block_bytes * 8)).
  { epose proof (Z_div_ge0 (int.val off) (Z.of_nat (block_bytes * 8)) _ _). lia. }
  assert (int.val off `div` Z.of_nat (block_bytes * 8) = 0).
  { revert H5. revert H1. generalize (int.val off `div` Z.of_nat (block_bytes * 8)). rewrite /block_bytes. lia. }
  word.
Unshelve.
  all: rewrite /block_bytes; try lia; word.
Qed.

Theorem mapsto_txn_locked (γ : txn_names) l lwh a data E :
  ↑invN ⊆ E ->
  ↑walN ⊆ E ∖ ↑invN ->
  is_wal (wal_heap_inv γ.(txn_walnames)) l (wal_heap_walnames γ.(txn_walnames)) ∗
  inv invN (is_txn_always γ) ∗
  is_locked_walheap γ.(txn_walnames) lwh ∗
  mapsto_txn γ a data
  ={E}=∗
    is_locked_walheap γ.(txn_walnames) lwh ∗
    mapsto_txn γ a data ∗
    ⌜ ∃ v, locked_wh_disk lwh !! int.val a.(addrBlock) = Some v ⌝.
Proof.
  iIntros (H0 H1) "(#Hiswal & #Hinv & Hlockedheap & Hmapsto)".
  iInv "Hinv" as ">Htxnalways".
  iNamed "Htxnalways".
  iNamed "Hmapsto".
  iDestruct (gen_heap_valid with "Hmetactx Hmapsto_meta") as %Hvalid.
  eapply gmap_addr_by_block_lookup in Hvalid.
  destruct Hvalid as [offmap [Hmetam Hoffmap]].
  iDestruct (big_sepM2_lookup_2_some with "Hheapmatch") as (x) "%Hlm"; eauto.
  iDestruct (big_sepM2_lookup_acc with "Hheapmatch") as "[Hx Hheapmatch]"; eauto.
  iNamed "Hx".
  iMod (wal_heap_mapsto_latest with "[$Hiswal $Hlockedheap $Htxn_hb]") as "(Hlockedheap & Htxn_hb & %)"; eauto.
  iModIntro.
  iSplitR "Hlockedheap Hmapsto_log Hmapsto_meta Hmod_frag".
  { iNext. iExists _, _, _. iFrame.
    iApply "Hheapmatch". iExists _, _, _. iFrame. iFrame "%". }
  iModIntro.
  iFrame.
  iSplitL.
  { iExists _. iFrame. }
  iExists _. done.
Qed.


Theorem wp_txn__installBufsMap l q walptr γ lwh bufs buflist (bufamap : gmap addr buf) :
  {{{ inv invN (is_txn_always γ) ∗
      is_wal (wal_heap_inv γ.(txn_walnames)) walptr (wal_heap_walnames γ.(txn_walnames)) ∗
      readonly (l ↦[Txn.S :: "log"] #walptr) ∗
      is_locked_walheap γ.(txn_walnames) lwh ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist,
        is_txn_buf_pre γ bufptrval a buf
  }}}
    Txn__installBufsMap #l (slice_val bufs)
  {{{ (blkmapref : loc) (blkmap : Map.t Slice.t), RET #blkmapref;
      is_locked_walheap γ.(txn_walnames) lwh ∗
      is_map blkmapref blkmap ∗
      ( [∗ map] a ↦ buf ∈ bufamap,
        ∃ data, mapsto_txn γ a (existT buf.(bufKind) data) ) ∗
      [∗ map] blkno ↦ blkslice; offmap ∈ blkmap; gmap_addr_by_block bufamap,
        ∃ b,
          is_block blkslice 1 b ∗
          ⌜ updBlockKindOK blkno b γ (locked_wh_disk lwh) offmap ⌝
  }}}.
Proof using txnG0 txnG0 Σ.
  iIntros (Φ) "(#Hinv & #Hiswal & #log & Hlockedheap & Hbufs & Hbufpre) HΦ".

Opaque struct.t.
  wp_call.
  wp_apply wp_NewMap.
  iIntros (blks) "Hblks".

  iDestruct (is_slice_to_small with "Hbufs") as "Hbufs".
  wp_apply (wp_forSlicePrefix
      (fun done todo =>
        ∃ bufamap_todo bufamap_done blkmap,
        "<-" ∷ ⌜ done ++ todo = buflist ⌝ ∗
        "->" ∷ ⌜ bufamap_done = bufamap ∖ bufamap_todo ⌝ ∗
        "%" ∷ ⌜ bufamap_todo ⊆ bufamap ⌝ ∗
        "Hblks" ∷ is_map blks blkmap ∗
        "Hbufamap_todo" ∷ ( [∗ maplist] a↦buf;bufptrval ∈ bufamap_todo;todo, is_txn_buf_pre γ bufptrval a buf ) ∗
        "Hbufamap_done" ∷ ( [∗ map] blkno ↦ blkslice; offmap ∈ blkmap; gmap_addr_by_block bufamap_done,
          ∃ b,
            is_block blkslice 1 b ∗
            ⌜ updBlockKindOK blkno b γ (locked_wh_disk lwh) offmap ⌝ ) ∗
        "Hbufamap_done_mapsto" ∷ ( [∗ map] a↦buf ∈ bufamap_done, ∃ data, mapsto_txn γ a (existT buf.(bufKind) data) ) ∗
        "Hlockedheap" ∷ is_locked_walheap γ.(txn_walnames) lwh
      )%I
      with "[] [$Hbufs Hbufpre Hblks Hlockedheap]").
  2: {
    iExists bufamap, ∅, ∅.
    iSplitR; try done.
    iSplitR.
    { iPureIntro. rewrite map_difference_diag. done. }
    iFrame "Hblks". iFrame "Hbufpre". iFrame "Hlockedheap".
    iSplitR.
    { iPureIntro. set_solver. }
    iSplit.
    { rewrite gmap_addr_by_block_empty. iApply big_sepM2_empty. done. }
    iApply big_sepM_empty. done.
  }
  {
    iIntros (i b ? ? Hdonetodo).
    iIntros (Φ') "!> HP HΦ'".
    iNamed "HP".

    iDestruct (big_sepML_delete_cons with "Hbufamap_todo") as (a buf) "(%Hb & Htxnbuf & Hbufamap_todo)".
    iNamed "Htxnbuf".
    iDestruct "Hmapto" as (data) "Hmapto".

    iMod (mapsto_txn_locked with "[$Hiswal $Hinv $Hmapto $Hlockedheap]") as "(Hlockedheap & Hmapto & %Hlockedsome)".
    1: solve_ndisj.
    1: solve_ndisj.
    destruct Hlockedsome as [lockedv Hlockedsome].

    wp_pures.
    wp_apply (wp_buf_loadField_sz with "Hisbuf"). iIntros "Hisbuf".
    destruct (decide (buf.(bufKind) = KindBlock)).

    - replace (bufSz buf.(bufKind)) with (bufSz KindBlock) by congruence.
      Opaque BlockSize. Opaque bufSz.
      wp_pures.

      iMod (mapsto_txn_valid with "Hinv Hmapto") as "[Hmapto %Hvalid]".
      { solve_ndisj. }

      generalize dependent data.
      rewrite e.
      intros.

      wp_apply (wp_buf_loadField_data with "Hisbuf"). iIntros (bufdata) "[Hbufdata Hisbuf_wd]".
      wp_apply (wp_buf_wd_loadField_addr with "Hisbuf_wd"). iIntros "Hisbuf_wd".

      wp_apply (wp_MapInsert with "Hblks").
      { reflexivity. }
      iIntros "Hblks".

      iApply "HΦ'".
      iExists (delete a bufamap_todo), (<[a := buf]> (bufamap ∖ bufamap_todo)), _.
      iSplitR.
      { rewrite -app_assoc. simpl. done. }
      iSplitR.
      { iPureIntro. erewrite map_difference_delete; eauto.
        eapply lookup_weaken; eauto. }
      iFrame "Hblks".
      iFrame "Hbufamap_todo".

      iFrame "Hlockedheap".
      iSplitR.
      { iPureIntro. etransitivity; first by apply delete_subseteq. eauto. }
      iSplitR "Hbufamap_done_mapsto Hmapto".
      2: {
        iApply (big_sepM_insert_2 with "[Hmapto] Hbufamap_done_mapsto").
        intuition.
        rewrite e.
        iExists _.
        iFrame.
      }
      rewrite /map_insert.
      rewrite gmap_addr_by_block_insert.
      2: { eapply lookup_difference_None; eauto. }
      iApply (big_sepM2_insert_2 with "[Hbufdata] Hbufamap_done").
      simpl.
      rewrite /is_buf_data /is_block.

      destruct buf; simpl in *.
      destruct bufData; try congruence.

      iExists _. iFrame. iPureIntro.
      eexists _. intuition eauto.
      intro diskLatest; intros.
      intro off; intros.

      destruct a.
      eapply valid_off_block in H2; eauto.
      eapply valid_off_block in H5; eauto.
      rewrite H2. rewrite H5.
      rewrite lookup_insert.
      simpl. done.

    - wp_pures.
      wp_if_destruct.
      {
        exfalso.
        destruct buf; simpl in *.
        destruct bufKind; cbn in *; try congruence.
        { inversion H1. }
        { inversion H1. }
      }

      wp_apply wp_ref_of_zero; first by eauto.
      iIntros (blkvar) "Hblkvar".

      wp_apply (wp_buf_loadField_addr with "Hisbuf"). iIntros "Hisbuf".
      wp_apply (wp_MapGet with "Hblks"). iIntros (v ok) "[% Hblks]".
      wp_pures.

      iMod (mapsto_txn_valid with "Hinv Hmapto") as "[Hmapto %Hvalid]".
      { solve_ndisj. }

      wp_apply (wp_If_join
        ( ∃ blkslice blk blkmap',
            "Hblkvar" ∷ blkvar ↦[slice.T byteT] (slice_val blkslice) ∗
            "Hisblock" ∷ is_block blkslice 1 blk ∗
            "Hbufamap_done" ∷ ( [∗ map] blkno↦blkslice;offmap ∈ delete a.(addrBlock) blkmap';
                  delete a.(addrBlock) (gmap_addr_by_block (bufamap ∖ bufamap_todo)),
                  ∃ b0 : Block,
                    is_block blkslice 1 b0
                    ∗ ⌜updBlockKindOK blkno b0 γ
                         (locked_wh_disk lwh) offmap⌝ ) ∗
            "Hisbuf" ∷ is_buf b a buf ∗
            "Hlockedheap" ∷ is_locked_walheap γ.(txn_walnames) lwh ∗
            "Hblks" ∷ is_map blks blkmap' ∗
            "%" ∷ ⌜ blkmap' !! a.(addrBlock) = Some blkslice ⌝ ∗
            "%" ∷ ⌜ updBlockOK a.(addrBlock) blk buf.(bufKind) (locked_wh_disk lwh) (default ∅ ((gmap_addr_by_block (bufamap ∖ bufamap_todo)) !! a.(addrBlock))) ⌝
        )%I
        with "[Hbufamap_done Hisbuf Hblkvar Hlockedheap Hblks]"); first iSplit.
      {
        iIntros "(-> & HΦ)".
        wp_store.
        apply map_get_true in H0.
        iDestruct (big_sepM2_lookup_1_some with "Hbufamap_done") as (xx) "%Hx"; eauto.
        iDestruct (big_sepM2_delete with "Hbufamap_done") as "[Ha Hbufamap_done]"; eauto.
        iDestruct "Ha" as (b0) "[Hisblock %]".
        iApply "HΦ".
        iExists _, _, _. iFrame.
        iSplit; first by done.
        iPureIntro.
        rewrite Hx.
        destruct H1. destruct H1. intuition idtac.
        rewrite H1 in H6. inversion H6; clear H6; subst. eauto.
      }
      {
        iIntros "(-> & HΦ)".
        wp_apply (wp_buf_loadField_addr with "Hisbuf"). iIntros "Hisbuf".
        wp_loadField.
        wp_apply (wp_Walog__Read with "[$Hiswal $Hlockedheap]"); eauto.
        iIntros (s) "[Hlockedheap Hisblock]".
        wp_store.
        wp_load.
        wp_apply (wp_buf_loadField_addr with "Hisbuf"). iIntros "Hisbuf".
        wp_apply (wp_MapInsert with "[$Hblks]").
        { reflexivity. }
        iIntros "Hblks".
        iApply "HΦ".
        iExists _, _, _. iFrame.

        apply map_get_false in H0; destruct H0; subst.
        iDestruct (big_sepM2_lookup_1_none with "Hbufamap_done") as %Hnone; eauto.

        rewrite delete_insert_delete.
        rewrite delete_notin; eauto.
        rewrite /map_insert lookup_insert delete_notin; eauto.
        iFrame "Hbufamap_done".
        iSplit; first by done.
        iPureIntro.

        rewrite Hnone.
        intro diskLatest; intros.
        intro off; intros.
        rewrite lookup_empty; intros.
        congruence.
      }

      iIntros "H". iNamed "H".

      wp_pures.
      wp_load.
      wp_apply (wp_Buf__Install with "[$Hisbuf $Hisblock]").
      iIntros (blk') "(Hisbuf & His_block & %Hinstall_ok)".

      iApply "HΦ'".
      iExists (delete a bufamap_todo), (<[a := buf]> (bufamap ∖ bufamap_todo)), _.
      iFrame "Hblks Hlockedheap Hbufamap_todo".
      iSplitR.
      { rewrite -app_assoc. done. }
      iSplitR.
      { iPureIntro. erewrite map_difference_delete; eauto.
        erewrite lookup_weaken; eauto. }
      iSplitR.
      { iPureIntro. etransitivity; first by apply delete_subseteq. eauto. }
      iSplitR "Hbufamap_done_mapsto Hmapto".
      2: {
        iApply (big_sepM_insert_2 with "[Hmapto] [$Hbufamap_done_mapsto]").
        iExists _. iFrame. }
      rewrite gmap_addr_by_block_insert.
      2: { eapply lookup_difference_None; eauto. }
      replace (blkmap') with (<[a.(addrBlock) := blkslice]> blkmap') at 2.
      2: { rewrite insert_id; eauto. }
      iApply big_sepM2_insert_delete.
      iFrame "Hbufamap_done".
      iExists _. iFrame. iPureIntro.

      eexists _. intuition eauto.
      intro diskLatest; intros.
      intro off; intros.
      specialize (H2 diskLatest H4 off oldBufData H7 H8 H9).
      destruct (decide (a.(addrOff) = off)).
      + subst.
        rewrite lookup_insert.
        specialize (Hinstall_ok a.(addrOff)).
        destruct (decide (a.(addrOff) = a.(addrOff))); try congruence.
        destruct (default ∅ ((gmap_addr_by_block (bufamap ∖ bufamap_todo)) !!
                    a.(addrBlock)) !! a.(addrOff)); eauto.
        intuition eauto.
        destruct b0; simpl in *.
        subst. eauto.

      + rewrite lookup_insert_ne; eauto.
        specialize (Hinstall_ok off).
        destruct (decide (off = a.(addrOff))); try congruence.
        destruct (default ∅ ((gmap_addr_by_block (bufamap ∖ bufamap_todo)) !!
                    a.(addrBlock)) !! off); eauto.
        destruct b0; simpl in *. intuition subst.
        eauto.
  }

  iIntros "[Hbufs H]". iNamed "H".
  wp_pures.

  iDestruct (big_sepML_empty_m with "Hbufamap_todo") as "%Hbufamap_todo_empty"; subst.
  rewrite map_difference_empty.
  iApply "HΦ". iFrame.
Qed.

Theorem wp_MkBlockData blkno dataslice :
  {{{
    emp
  }}}
    MkBlockData #blkno (slice_val dataslice)
  {{{
    RET (update_val (blkno, dataslice)%core);
    emp
  }}}.
Proof.
  iIntros (Φ) "Hisblock HΦ".
  wp_call.
  rewrite /update_val.
  iApply "HΦ".
  done.
Qed.

Theorem wp_txn__installBufs l q walptr γ lwh bufs buflist (bufamap : gmap addr buf) :
  {{{ inv invN (is_txn_always γ) ∗
      is_wal (wal_heap_inv γ.(txn_walnames)) walptr (wal_heap_walnames γ.(txn_walnames)) ∗
      readonly (l ↦[Txn.S :: "log"] #walptr) ∗
      is_locked_walheap γ.(txn_walnames) lwh ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist,
        is_txn_buf_pre γ bufptrval a buf
  }}}
    Txn__installBufs #l (slice_val bufs)
  {{{ (blkslice : Slice.t) upds, RET (slice_val blkslice);
      is_locked_walheap γ.(txn_walnames) lwh ∗
      updates_slice blkslice upds ∗
      ( [∗ map] a ↦ buf ∈ bufamap,
        ∃ data, mapsto_txn γ a (existT buf.(bufKind) data) ) ∗
      [∗ maplist] blkno ↦ offmap; upd ∈ gmap_addr_by_block bufamap; upds,
        ⌜ upd.(update.addr) = blkno ⌝ ∗
        ⌜ updBlockKindOK blkno upd.(update.b) γ (locked_wh_disk lwh) offmap ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hinv & #Hiswal & #Hlog & Hlockedheap & Hbufs & Hbufpre) HΦ".

  wp_call.
  wp_apply wp_ref_of_zero; first by eauto.
  iIntros (blks_var) "Hblks_var".

  wp_apply (wp_txn__installBufsMap with "[$Hinv $Hiswal $Hlog $Hlockedheap $Hbufs $Hbufpre]").
  iIntros (blkmapref blkmap) "(Hlockedheap & Hblkmapref & Hbufamap_mapsto & Hblkmap)".

  wp_apply (wp_MapIter_2 _ _ _ _
    (λ mtodo mdone,
      ∃ (blks : Slice.t) upds offmaps_todo offmaps_done,
        "Hblks_var" ∷ blks_var ↦[slice.T (struct.t Update.S)] (slice_val blks) ∗
        "Hblks" ∷ updates_slice blks upds ∗
        "%" ∷ ⌜ gmap_addr_by_block bufamap = offmaps_todo ∪ offmaps_done ⌝ ∗
        "%" ∷ ⌜ dom (gset u64) offmaps_todo ## dom (gset u64) offmaps_done ⌝ ∗
        "Hmtodo" ∷ ( [∗ map] blkno↦blkslice;offmap ∈ mtodo;offmaps_todo, ∃ b : Block,
                                          is_block blkslice 1 b ∗
                                          ⌜ updBlockKindOK blkno b γ (locked_wh_disk lwh) offmap ⌝ ) ∗
        "Hmdone" ∷ ( [∗ maplist] blkno↦offmap;upd ∈ offmaps_done;upds,
                                          ⌜ upd.(update.addr) = blkno ⌝ ∗
                                          ⌜ updBlockKindOK blkno upd.(update.b) γ (locked_wh_disk lwh) offmap ⌝ )
    )%I with "Hblkmapref [Hblks_var Hblkmap]").
  {
    rewrite zero_slice_val.
    iExists _, nil, _, ∅.
    iFrame "Hblks_var".
    iFrame "Hblkmap".
    iSplitL.
    { rewrite /updates_slice. iExists nil. simpl.
      iSplitL; last by done.
      iApply is_slice_zero.
    }
    iSplitL.
    { iPureIntro. rewrite right_id. done. }
    iSplitL.
    { iPureIntro. rewrite dom_empty. set_solver. }
    iApply big_sepML_empty.
  }
  {
    iIntros (k v mtodo mdone).
    iIntros (Φ') "!> [HI %] HΦ'".
    iNamed "HI".

    iDestruct (big_sepM2_lookup_1_some with "Hmtodo") as (x) "%Hx"; eauto.
    iDestruct (big_sepM2_delete with "Hmtodo") as "[Htodo Hmtodo]"; eauto.
    iDestruct "Htodo" as (b) "[Hisblock %]".

    wp_apply (wp_MkBlockData with "[$]"). iIntros "_".
    wp_load.
    wp_apply (wp_SliceAppend_updates with "[Hblks Hisblock]").
    { iFrame. }
    iIntros (blks') "Hblks'".
    wp_store.
    iApply "HΦ'".

    iExists _, _, (delete k offmaps_todo), (<[k := x]> offmaps_done).
    iFrame "Hblks_var Hblks' Hmtodo".
    iSplitR.
    { iPureIntro. rewrite H0. rewrite delete_insert_union; eauto. }
    iSplitR.
    { iPureIntro. set_solver. }
    iApply big_sepML_insert_app.
    { eapply (not_elem_of_dom (D:=gset u64)).
      assert (k ∈ dom (gset u64) offmaps_todo).
      { eapply elem_of_dom; eauto. }
      set_solver. }
    iFrame "Hmdone".
    simpl. done.
  }

  iIntros "[Hblkmapref H]".
  iNamed "H".
  wp_load.
  iDestruct (big_sepM2_empty_r with "Hmtodo") as "->".
  rewrite left_id in H. subst.
  iApply "HΦ".
  iFrame.
Qed.

(*
Theorem memappend_mapsto_update E mData gData bufamap mx updlist_olds lwh walHeap :
  ( [∗ map] k↦y ∈ (mData ∖ mx), ∃ (installed : Block) (bs : list Block),
    "Hmdata_hb" ∷ mapsto (hG := walHeap.(wal_heap_h)) k 1 (HB installed bs) ∗
    "Hmdata_in_block" ∷ bufDataTs_in_block installed bs (projT2 y) ) ∗
  ( [∗ maplist] k↦v;lv ∈ mx;updlist_olds, ∃ offmap : gmap u64 buf,
    ⌜mData !! k = Some v⌝ ∗
    ⌜(lv.1).(update.addr) = k⌝ ∗
    bufDataTs_in_block lv.2.1 lv.2.2 (projT2 v) ∗
    mapsto (hG := walHeap.(wal_heap_h)) (lv.1).(update.addr) 1 (HB lv.2.1 (lv.2.2 ++ [(lv.1).(update.b)])) ∗
    ⌜gmap_addr_by_block bufamap !! (lv.1).(update.addr) = Some offmap⌝ ∗
    ⌜ updBlockKindOK (lv.1).(update.addr) (lv.1).(update.b) gData (locked_wh_disk lwh) offmap⌝ ) ∗
  ( [∗ map] k↦x ∈ bufamap, ∃ data : bufDataT x.(bufKind), mapsto_txn gData k data )
  ={E}=∗
    ∃ mData',
      ( [∗ map] k↦x ∈ bufamap, mapsto_txn gData k x.(bufData) ) ∗
      ( [∗ map] k↦y ∈ mData', ∃ (installed : Block) (bs : list Block),
        "Hmdata_hb" ∷ mapsto (hG := walHeap.(wal_heap_h)) k 1 (HB installed bs) ∗
        "Hmdata_in_block" ∷ txn_bufDataT_in_block installed bs (projT2 y) ).
Proof.
(*
  iIntros "(Hgmdata & Hmapstos)".

  iMod (big_sepM_mono_fupd
    _
    (λ k x, mapsto_txn gData k x.(bufData))
    _
    (∃ mData',
      "Hgmdata" ∷ [∗ map] y1;y2 ∈ mData';gData, gmDataP y1 y2)%I
    with "[] [$Hmapstos Hgmdata]") as "[HI Hmapstos]".
  2: {
    iExists _; iFrame.
  }
  {
    iIntros (k x Hkx) "[H HΦ]".
    iNamed "H".
    iDestruct "HΦ" as (data) "Hmapsto".

    iDestruct "Hmapsto" as (hG γown) "(% & % & Hmapsto & Hown)".
    iDestruct (big_sepM2_lookup_2_some with "Hgmdata") as (mk) "%"; eauto.
    iDestruct (big_sepM2_insert_acc with "Hgmdata") as "[Hk Hgmdata]"; eauto.
    iDestruct (gmDataP_eq with "Hk") as "%Hproj".
    destruct mk; simpl in *; subst.
    iDestruct (gmDataP_ctx with "Hk") as "Hk".
    iMod (gen_heap_update with "Hk Hmapsto") as "[Hk Hmapsto]".
    iModIntro.
    iSplitR "Hmapsto Hown".
    2: { iExists _, _. iFrame. done. }

    iDestruct ("Hgmdata" with "[Hk]") as "Hgmdata".
    { iApply (gmDataP_ctx' (existT x.(bufKind) (<[k.(addrOff) := UB x.(bufData) γown]> g))).
      iFrame. }
    rewrite (insert_id gData); eauto.
  }

  iModIntro.
  iDestruct "HI" as (mData') "HI".
  iExists _. iFrame.
Qed.
*)
Admitted.
*)

Theorem bi_iff_1 {PROP:bi} (P Q: PROP) :
  P ≡ Q ->
  ⊢ P -∗ Q.
Proof.
  intros ->; auto.
Qed.

Theorem bi_iff_2 {PROP:bi} (P Q: PROP) :
  P ≡ Q ->
  ⊢ Q -∗ P.
Proof.
  intros ->; auto.
Qed.

(*
Lemma txn_crash_heap_alloc γcrash txn_crash_heaps wal_crash_new
                           (crash_blocks : gmap u64 Block)
                           (crash_bufs : gmap addr {K & @bufDataT K})
                           npos :
  ⊢ own γcrash (●E txn_crash_heaps) ∗
    own γcrash (◯E txn_crash_heaps) ∗
    ( [∗ map] a↦b ∈ crash_bufs, ⌜valid_addr a ∧ valid_off (projT1 b) a.(addrOff)⌝ ) ∗
    ( [∗ map] a↦b;offmap ∈ crash_blocks;gmap_addr_by_block crash_bufs,
        mapsto (hG := GenHeapG_Pre _ _ _ crashPreG wal_crash_new) a 1 b ∗
        txn_crash_heap_off_match b offmap )
    ==∗
      ∃ txn_crash_new,
        own γcrash (●E (async_put (npos, txn_crash_new) txn_crash_heaps)) ∗
        own γcrash (◯E (async_put (npos, txn_crash_new) txn_crash_heaps)) ∗
        txn_crash_heap_match wal_crash_new txn_crash_new ∗
        ( [∗ map] a↦b ∈ crash_bufs, mapsto_txn_crash txn_crash_new a b ).
Proof.
  iIntros "(Hown & Hfrag & Hvalids & Hblocks)".
  iMod (gen_heap_init_gname ∅) as (txn_crash_new) "Htxn_crash_new".
  iMod (ghost_var_update with "Hown Hfrag") as "[Hown Hfrag]".
  iMod (gen_heap_alloc_gen ∅ crash_bufs with "Htxn_crash_new") as "[Htxn_crash_new Hnewbufs]".
  { apply map_disjoint_empty_r. }
  rewrite right_id.
  iModIntro.
  iExists _.
  iFrame.

  iSplitL "Htxn_crash_new Hblocks".
  { iExists _. iFrame.
    iDestruct (big_sepM2_sepM_2 with "Hblocks") as "Hbufs".
    iApply (big_sepM_mono with "Hbufs").
    iIntros (k x Hkx) "H".
    iDestruct "H" as (b) "(% & H0 & H1)".
    iExists _. iFrame. }

  iDestruct (bi_iff_2 with "[Hvalids Hnewbufs]") as "Hnewbufs".
  { apply (big_sepM_sep (K := addr) (A := {K & bufDataT K})). }
  { iFrame. }

  iApply (big_sepM_mono with "Hnewbufs").
  iIntros (k x Hkx) "[Hmapsto Hvalid]". iFrame.
Qed.
*)

(*
Lemma crash_txn_bufs_to_wal_blocks (unmodifiedBufs : gmap addr {K & @bufDataT K})
                                   (wal_crash_heap txn_crash_heap : gname)
                                   (updlist : list update.t) :
  ( [∗ map] a↦b ∈ unmodifiedBufs, mapsto_txn_crash txn_crash_heap a b ) -∗
  txn_crash_heap_match wal_crash_heap txn_crash_heap -∗
  ∃ wal_blocks,
    ( [∗ map] a↦b ∈ unmodifiedBufs, mapsto_txn_crash txn_crash_heap a b ) ∗
    ⌜∀ u : update.t, u ∈ updlist → wal_blocks !! u.(update.addr) = None⌝ ∗
    let P := [∗ map] a↦b ∈ wal_blocks,
                 mapsto (hG := GenHeapG_Pre _ _ _ crashPreG wal_crash_heap) a 1 b in
    P ∗
    ( P -∗ txn_crash_heap_match wal_crash_heap txn_crash_heap ).
Proof.
  iIntros "Hbufs Hmatch".
  iDestruct "Hmatch" as (wal_crash_map) "[Hctx Hmatch]".
  iAssert (⌜ unmodifiedBufs ⊆ wal_crash_map ⌝)%I as "%Hsubset".
  { rewrite map_subseteq_spec.
    iIntros (i b Hib).
    iDestruct (big_sepM_lookup with "Hbufs") as "[% Hbuf]"; eauto.
    iDestruct (gen_heap_valid with "Hctx Hbuf") as "%Hvalid".
    done. }

  rewrite -(map_union_filter
              (λ x, Forall (λ u, u.(update.addr) ≠ (fst x)) updlist ∧
                    is_Some (gmap_addr_by_block unmodifiedBufs !! fst x))
              (gmap_addr_by_block wal_crash_map)).
  iDestruct (big_sepM_union with "Hmatch") as "[Hmatch0 Hmatch1]".
  { eapply map_disjoint_filter. }

  iDestruct (big_sepM_sepM2 with "Hmatch0") as (wal_blocks) "Hmatch0".

  iExists wal_blocks.
  iFrame "Hbufs".

  iAssert (⌜∀ u : update.t, u ∈ updlist → wal_blocks !! u.(update.addr) = None⌝)%I as "%Hdisjoint".
  { iIntros (u Hu).
    destruct (wal_blocks !! u.(update.addr)) eqn:He; eauto.
    iDestruct (big_sepM2_lookup_2_some with "Hmatch0") as (z) "%Hfiltered"; eauto.
    eapply map_filter_lookup_Some in Hfiltered; intuition idtac.
    eapply Forall_forall in H1; eauto. }

  iSplitR; first by done.
  iDestruct (big_sepM2_sep with "Hmatch0") as "[Hmatch00 Hmatch01]".
  iDestruct (big_sepM2_sepM_2 with "Hmatch00") as "Hmatch00".

  iSplitL "Hmatch00".
  { iApply (big_sepM_mono with "Hmatch00").
    iIntros (???) "H".
    iDestruct "H" as (?) "[% H]". iFrame. }

  iIntros "Hmatch00".
  iDestruct (big_sepM2_flip with "Hmatch01") as "Hmatch01".
  iDestruct (big_sepM2_sepM_merge with "[$Hmatch01 $Hmatch00]") as "Hmatch0".
  iDestruct (big_sepM2_sepM_2 with "Hmatch0") as "Hmatch0".
  iDestruct (big_sepM_mono with "Hmatch0") as "Hmatch0".
  2: {
    iDestruct (big_sepM_union with "[$Hmatch0 $Hmatch1]") as "Hmatch".
    { eapply map_disjoint_filter. }
    rewrite map_union_filter.
    iExists _. iFrame. }

  iIntros (???) "H".
  iDestruct "H" as (b) "[% [H0 H1]]". iExists b. iFrame.
Qed.
*)

Theorem wp_txn__doCommit l q γ bufs buflist bufamap E (Q : nat -> iProp Σ) :
  {{{ is_txn l γ ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      ( [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist, is_txn_buf_pre γ bufptrval a buf ) ∗
      ( |={⊤ ∖ ↑walN ∖ ↑invN, E}=> ∃ (σl : async (gmap addr {K & bufDataT K})),
          "Hcrashstates_frag" ∷ ghost_var γ.(txn_crashstates) (1/2) σl ∗
          "Hcrashstates_fupd" ∷ (
            let σ := ((λ b, existT _ b.(bufData)) <$> bufamap) ∪ latest σl in
            ghost_var γ.(txn_crashstates) (1/2) (async_put σ σl)
            ={E, ⊤ ∖ ↑walN ∖ ↑invN}=∗ Q (length (possible σl)) ) )
  }}}
    Txn__doCommit #l (slice_val bufs)
  {{{ (commitpos : u64) (ok : bool), RET (#commitpos, #ok);
      if ok then
        ∃ txn_id,
        txn_pos (wal_heap_walnames (txn_walnames γ)) txn_id commitpos ∗ Q txn_id ∗
        [∗ map] a ↦ buf ∈ bufamap,
          mapsto_txn γ a (existT _ buf.(bufData))
      else
        [∗ map] a ↦ buf ∈ bufamap,
          ∃ data, mapsto_txn γ a (existT buf.(bufKind) data)
  }}}.
Proof using txnG0 Σ.
  iIntros (Φ) "(#Htxn & Hbufs & Hbufpre & Hfupd) HΦ".
  iPoseProof "Htxn" as "Htxn0".
  iNamed "Htxn".

  wp_call.
  wp_loadField.
  wp_apply acquire_spec; eauto.
  iIntros "[Hlocked Htxnlocked]".

  wp_pures.
  iNamed "Htxnlocked".

  wp_apply (wp_txn__installBufs with "[$Histxna $Hiswal $Histxn_wal $Hbufs $Hbufpre $Hwal_latest]").
  iIntros (blks updlist) "(Hwal_latest & Hblks & Hmapstos & #Hupdmap)".
  wp_pures.
  wp_apply util_proof.wp_DPrintf.
  wp_loadField.

  wp_apply (wp_Walog__MemAppend _
    ("Hlockedheap" ∷ is_locked_walheap γ.(txn_walnames) lwh)
    (λ npos,
      ∃ lwh' txn_id,
        "Hlockedheap" ∷ is_locked_walheap γ.(txn_walnames) lwh' ∗
        "Hmapstos" ∷ ( [∗ map] k↦x ∈ bufamap, mapsto_txn γ k (existT _ x.(bufData)) ) ∗
        "Hpos" ∷ txn_pos (wal_heap_walnames (txn_walnames γ)) txn_id npos
    )%I
    with "[$Hiswal $Hblks Hmapstos Hwal_latest Hfupd]").
  { iApply (wal_heap_memappend E with "[Hmapstos Hfupd] Hwal_latest").
    iInv invN as ">Hinner" "Hinner_close".
    iMod "Hfupd".
    iModIntro.
    iNamed "Hinner".
    iNamed "Hfupd".

    rewrite /memappend_pre.
    rewrite /memappend_crash_pre.

    iDestruct (ghost_var_agree with "Hcrashstates Hcrashstates_frag") as %->.

    iDestruct (gmap_addr_by_block_big_sepM with "Hmapstos") as "Hmapstos".
    iDestruct (big_sepM2_filter _ (λ k, is_Some (gmap_addr_by_block bufamap !! k)) with "Hheapmatch") as "[Hheapmatch_in Hheapmatch_out]".
    iDestruct (big_sepM2_sepM_1 with "Hheapmatch_in") as "Hheapmatch_in".

(*

action items:

- big_sepM2 from two big_sepM's that agree on keys
- big_sepML factored into L-to-M existential correspondence
- big_sepMmany

*)

(*

updlist ->
[Hupdmap]
bufamap ->
[Hmapstos]
logm.(latest) ->
[Hheapmatch]
olds

*)


(*



    iDestruct (big_sepML_sepM2_shift with "[Hupdmap] []") as "Hupdmap2".

    iDestruct (big_sepM_mono_wand _
      (λ blkno offmap, (
        [∗ map] off↦v ∈ offmap,
             ∃ (data : bufDataT v.(bufKind)) (first : nat),
               mapsto_txn γ first {| addrBlock := blkno; addrOff := off |}
                 (existT v.(bufKind) data)) ∗
        ⌜ is_Some (gmap_addr_by_block logm.(latest) !! blkno) ⌝)%I _ (log_heap_ctx logm)
      with "[] [$Hmapstos $Hlogheapctx]") as "[Hlogheapctx Hmapstos]".
    {
      iIntros (k x Hkx) "[Hlogheapctx Hx]".
      eapply gmap_addr_by_block_off_not_empty in Hkx as Hx.
      assert (x = (list_to_map (map_to_list x) : gmap u64 buf)) as Hlm. { rewrite list_to_map_to_list; eauto. }
      rewrite -> Hlm in *.
      destruct (map_to_list x) eqn:Hxl.
      { simpl in Hx. congruence. }
      simpl.
      iDestruct (big_sepM_lookup_acc with "Hx") as "[H Hx]".
      { apply lookup_insert. }
      iNamed "H".
      iDestruct (log_heap_valid_cur with "Hlogheapctx Hmapsto_log") as %Hvalid.
      eapply gmap_addr_by_block_lookup in Hvalid as Hvalidblock; destruct Hvalidblock; intuition idtac.
      iDestruct ("Hx" with "[Hmapsto_log Hmapsto_meta Hmod_frag]") as "Hx".
      { iExists _, _, _. iFrame. }
      iFrame "Hlogheapctx". iFrame. eauto.
    }
    iDestruct (big_sepM_sep with "Hmapstos") as "[Hmapstos #Hmapsto_latest]".


Search _ gmap insert.
Search _ gmap ∅.

    iDestruct (big_sepML_sepM with "[$Hupdmap $Hmapstos]") as "Hmapstos".

    rewrite -(map_union_filter
                (λ x, is_Some (gmap_addr_by_block bufamap !! fst x))
                (gmap_addr_by_block logm.(latest))).

    iDestruct (big_sepM_union with "Hmatch") as "[Hmatch0 Hmatch1]".
    { eapply map_disjoint_filter. }



Check big_sepML_map_val_exists.

*)

(*
    iDestruct (big_sepM_mono _
       (λ a buf,
         ∃ first, mapsto_txn γ first a (existT buf.(bufKind) buf.(bufData))
      )%I with "Hmapstos") as "Hmapstos".
    {
      iIntros (k x Hkx) "H".
      iDestruct "H" as (data first) "Hmapsto".
      iExists _. done.
    }

    (* XXX up to here *)

    iDestruct (big_sepM_sep with "Hmapstos") as "[Hmapstos #Hbufamap_gdata]".

    iDestruct (big_sepM2_mono _ (λ k gm gh, gmDataP gm gh ∗ emp)%I with "Hgmdata") as "Hgmdata".
    { iIntros; iFrame. }
    iDestruct (big_sepM2_sep with "Hgmdata") as "[Hgmdata #Hmdata_gmdata]".

    iDestruct (big_sepML_map_val_exists with "Hupdmap []") as (mx) "Hx".
    {
      iIntros (k v lv Hkv Hp).
      destruct Hp as [Hk Hp].
      destruct Hp as [K [GH [Hgdata Hp]]].

      iDestruct (big_sepM2_lookup_2_some with "Hmdata_gmdata") as (mv) "%Hmdata"; eauto.

      iExists mv.
      iPureIntro.
      apply Hmdata.
    }

    iAssert (⌜ ∀ k v, mx !! k = Some v -> mData !! k = Some v ⌝)%I as "%Hsubset".
    { iIntros (k v Hkv).
      iDestruct (big_sepML_lookup_m_acc with "Hx") as (i lv) "(% & Hx2 & _)"; eauto.
      iDestruct "Hx2" as (v0) "(% & % & %)". done.
    }

    rewrite <- (map_difference_union mx mData) at 2.
    2: { apply map_subseteq_spec. eauto. }

    iDestruct (big_sepM_union with "Hmdata_m") as "[Hmx Hmdata_m]".
    { apply map_disjoint_difference_r. apply map_subseteq_spec; eauto. }

    iDestruct (big_sepML_sepM with "[$Hx $Hmx]") as "Hx_mx".
    iDestruct (big_sepML_mono _
      (λ k (v : {K : bufDataKind & gmap u64 (updatable_buf (bufDataT K))}) lv,
        (∃ (installed_bs : Block * list Block),
          ( ( ⌜mData !! k = Some v⌝ ∗
              ⌜lv.(update.addr) = k⌝ ∗
              txn_bufDataT_in_block (fst installed_bs) (snd installed_bs) (projT2 v)) ) ∗
            mapsto lv.(update.addr) 1 (HB (fst installed_bs) (snd installed_bs)) )
      )%I with "Hx_mx []") as "Hx_mx".
    {
      iIntros (k v lv). iPureIntro.
      iIntros "[H0 H1]".
      iDestruct "H0" as (v0) "(% & <- & %)".
      iDestruct "H1" as (installed bs) "[H10 H11]".
      iExists (installed, bs). iFrame. done. }

    iDestruct (big_sepML_exists with "Hx_mx") as (updlist_olds) "[-> Hx_mx]".
    iExists (snd <$> updlist_olds).

    iDestruct (big_sepL2_length with "Hcrashheapsmatch") as "%Hcrashlen".
    rewrite /possible ?app_length /= in Hcrashlen.
    iDestruct (big_sepL2_app_inv with "Hcrashheapsmatch") as "[Hcrashheapsmatch [[% Hcrashheapmatch_latest] _]]".
    { lia. }

    iDestruct (crash_txn_bufs_to_wal_blocks with "Htxn_unmod Hcrashheapmatch_latest")
      as (wal_unmodified_blocks) "(Hwal_blocks_old & %Hwal_unmod_disjoint & Hwal_unmod & Hcrashheapmatch_latest)".
    iExists wal_unmodified_blocks.
    iExists _.

    iFrame "Hwal_unmod Hcrashheaps".
    iDestruct (big_sepML_sepL_split with "Hx_mx") as "[Hx_mx Hupdlist_olds]".

    iSplitL "Hupdlist_olds".
    {
      iApply big_sepL2_alt.
      iSplitR.
      { repeat rewrite fmap_length. eauto. }
      rewrite zip_fst_snd. iFrame.
    }

    iSplitR; first by eauto.

    iIntros (txn_id lwh' new_crash_heap) "(Hcrash & Hq)".
    rewrite /memappend_crash /memappend_q.
    iDestruct "Hcrash" as "(Hlockedheap & Hcrashheaps & Hunmod & Hunmod_new & Hmod_new & Hpos)".
    rewrite (big_sepL2_alt _ updlist_olds.*1).

    iDestruct "Hq" as "[_ Hq]".
    rewrite zip_fst_snd.

    iDestruct (big_sepML_sepL_combine with "[$Hx_mx $Hq]") as "Hmx".
    iDestruct (big_sepML_sepL_exists with "Hupdmap") as "Hupdmap_list".
    iDestruct (big_sepML_sepL_combine with "[$Hmx Hupdmap_list]") as "Hmx".
    2: {
      iDestruct (bi_iff_1 with "Hupdmap_list") as "Hupdmap_list2".
      { iApply big_sepL_fmap. }
      iApply "Hupdmap_list2".
    }
    { refine _. }

    iDestruct (big_sepML_mono _
      (λ k (v : {K : bufDataKind & gmap u64 (updatable_buf (bufDataT K))}) lv,
        ∃ offmap,
          ⌜mData !! k = Some v⌝ ∗
          ⌜(fst lv).(update.addr) = k⌝ ∗
          txn_bufDataT_in_block (fst (snd lv)) (snd (snd lv)) (projT2 v) ∗
          mapsto (fst lv).(update.addr) 1 (HB (fst (snd lv)) ((snd (snd lv)) ++ [(fst lv).(update.b)])) ∗
          ⌜gmap_addr_by_block bufamap !! (fst lv).(update.addr) = Some offmap⌝ ∗
          ⌜updBlockKindOK (fst lv).(update.addr) (fst lv).(update.b) gData (locked_wh_disk lwh) offmap⌝
      )%I with "Hmx []") as "Hmx".
    {
      iIntros (k v lv). iPureIntro.
      iIntros "[H0 H1]".
      iDestruct "H0" as "[(% & % & Hinblock) Hmapsto]".
      iDestruct "H1" as (k0 v0) "(% & <- & %)".
      iExists _.
      iFrame. done.
    }

    iDestruct ("Hcrashheapmatch_latest" with "Hunmod") as "Hcrashheapmatch_latest".

    iMod (memappend_mapsto_update with "[$Hgmdata $Hmapstos $Hmx $Hmdata_m]") as (mData') "(Hgmdata & Hmapstos & Hmdata)".
    iMod (txn_crash_heap_alloc _ _ _ (wal_unmodified_blocks ∪ (list_to_map ((λ u, (u.(update.addr), u.(update.b))) <$> updlist_olds.*1))) (unmodifiedBufs ∪ ((λ b, existT _ b.(bufData)) <$> bufamap)) with "[$Htxncrashheaps $Htxn_crash_heaps_frag]")
      as (txn_crash_new) "(Htxncrashheaps & Htxn_crash_heaps_frag & Htxn_crash_heap_ok & Htxn_crash_mapstos)".
    { admit. }

    iExists _. iFrame.

    iMod ("Htxn_crash_close" with "[$Htxn_crash_heaps_frag $Hwal_blocks_old Htxn_crash_mapstos]") as "Htxn_crash_close".
    { iDestruct (big_sepM_union with "Htxn_crash_mapstos") as "[H0 H1]".
      { rewrite /map_disjoint /map_relation /option_relation. intro a. rewrite lookup_fmap.
        specialize (Htxn_unmod_disjoint a). destruct (unmodifiedBufs !! a).
        { destruct (bufamap !! a); simpl; eauto.
          assert (is_Some (Some b)); intuition eauto. congruence. }
        { destruct (bufamap !! a); simpl; eauto. }
      }
      iFrame.
      iApply big_sepM_fmap. iFrame.
    }

    iMod ("Hinner_close" with "[-Hpos]") as "Hinner_close".
    { iNext.
      iExists _, _, _. iFrame.
      iSplitL "Hcrashheapmatch_latest".
      { iSplitL; last by done.
        iFrame. done. }
      iSplitL; last by done.
      iSplitR; first by eauto.
      rewrite /=. iFrame.
    }

    iModIntro. iExists _. iFrame.
  }

  iIntros (npos ok) "Hnpos".
  wp_pures.
  wp_storeField.
  wp_loadField.
  destruct ok.
  {
    iDestruct "Hnpos" as "[Hnpos Htxn_pos]".
    iNamed "Hnpos".
    iDestruct "Htxn_pos" as (txn_num) "#Htxn_pos".
    wp_apply (release_spec with "[$Histxn_lock $Hlocked Histxn_nextid Hlockedheap Histxn_pos]").
    { iExists _, _, _. iFrame. }

    wp_pures.
    iApply "HΦ".
    iFrame.
    iExists _, _; iFrame "#".
  }
  {
    wp_apply (release_spec with "[$Histxn_lock $Hlocked Histxn_nextid Hnpos Histxn_pos]").
    { iExists _, _, _. iFrame. }

    wp_pures.
    iApply "HΦ".
    admit.
  }
*)
Admitted.

Theorem wp_txn_CommitWait l q γ bufs buflist bufamap (wait : bool) E (Q : nat -> iProp Σ) :
  {{{ is_txn l γ ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      ( [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist, is_txn_buf_pre γ bufptrval a buf ) ∗
      ( |={⊤ ∖ ↑walN ∖ ↑invN, E}=> ∃ (σl : async (gmap addr {K & bufDataT K})),
          "Hcrashstates_frag" ∷ ghost_var γ.(txn_crashstates) (1/2) σl ∗
          "Hcrashstates_fupd" ∷ (
            let σ := ((λ b, existT _ b.(bufData)) <$> bufamap) ∪ latest σl in
            ⌜bufamap ≠ ∅⌝ ∗
            ghost_var γ.(txn_crashstates) (1/2) (async_put σ σl)
            ={E, ⊤ ∖ ↑walN ∖ ↑invN}=∗ Q (length (possible σl))  ))
  }}}
    Txn__CommitWait #l (slice_val bufs) #wait
  {{{ (ok : bool), RET #ok;
      if ok then
        ( ⌜bufamap ≠ ∅⌝ -∗ ∃ (txn_id : nat),
          Q txn_id ∗
          ( ⌜wait=true⌝ -∗ own γ.(txn_walnames).(wal_heap_durable_lb) (◯ (MaxNat txn_id)) ) ) ∗
        [∗ map] a ↦ buf ∈ bufamap,
          mapsto_txn γ a (existT _ buf.(bufData))
      else
        [∗ map] a ↦ buf ∈ bufamap,
          ∃ data, mapsto_txn γ a (existT buf.(bufKind) data)
  }}}.
Proof.
  iIntros (Φ) "(#Htxn & Hbufs & Hbufpre & Hfupd) HΦ".

  wp_call.
  wp_apply wp_ref_to; [val_ty|].
  iIntros (commit) "Hcommit".
  wp_pures.
  wp_apply wp_slice_len.
  wp_pures.
  rewrite bool_decide_decide.
  destruct (decide (int.val 0 < int.val bufs.(Slice.sz))).
  - wp_pures.

    iAssert (⌜ bufamap ≠ ∅ ⌝)%I as "%Hnotempty".
    { admit. }

    wp_apply (wp_txn__doCommit with "[$Htxn $Hbufs $Hbufpre Hfupd]").
    {
      iMod "Hfupd".
      iModIntro.
      iNamed "Hfupd".
      iExists σl. iFrame "Hcrashstates_frag".

      iIntros "H".
      iMod ("Hcrashstates_fupd" with "[H]").
      { iFrame. done. }

      iModIntro. done.
    }

    iIntros (commitpos ok) "Hbufpost".

    wp_pures.
    destruct ok; wp_pures.
    + iDestruct "Hbufpost" as (txn_id) "(#Hpos & Hq & Hbufamap)".
      destruct wait; wp_pures.
      * iNamed "Htxn".
        wp_loadField.
        wp_apply (wp_Walog__Flush_heap with "[$Hiswal $Hpos]").
        iIntros "HQ".
        wp_load.
        iApply "HΦ". iFrame.
        iIntros (?). iExists txn_id. iFrame.
        done.

      * wp_pures.
        wp_load.
        iApply "HΦ". iFrame.
        iIntros (?). iExists txn_id. iFrame.
        iIntros (?). intuition congruence.

    + wp_apply util_proof.wp_DPrintf.
      wp_store.
      wp_load.
      iApply "HΦ".
      iFrame.

  - wp_apply util_proof.wp_DPrintf.

    iAssert (⌜ bufamap = ∅ ⌝)%I as "%Hempty".
    { admit. }

    wp_load.
    iApply "HΦ".

    iDestruct (is_slice_sz with "Hbufs") as %Hbuflistlen.
    assert (int.val bufs.(Slice.sz) = 0) by (revert n; word).
    assert (length (list.untype buflist) = 0%nat) by len.
    rewrite fmap_length in H0.
    apply length_zero_iff_nil in H0; subst.

    iSplit; last by iApply big_sepM_empty.
    iIntros. congruence.
    Fail idtac.
Admitted.


End heap.
