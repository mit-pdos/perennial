From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.algebra Require Import deletable_heap.

From Goose.github_com.mit_pdos.goose_nfsd Require Import txn.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import wal.specs wal.lib wal.heapspec addr.specs buf.defs buf.specs disk_lib.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.Helpers Require Import NamedProps Map.

Inductive updatable_buf (T : Type) :=
| UB : forall (v : T) (modifiedSinceInstallG : gname), updatable_buf T
.

Arguments UB {T} v modifiedSinceInstallG.

Class txnG (Σ: gFunctors) :=
  { txn_bool :> inG Σ (ghostR $ boolO);
    txn_gmap_u64_block :> inG Σ (ghostR $ gmapO u64 blockO);
    txn_disk_txns :> inG Σ (ghostR $ prodO (gmapO Z blockO) (listO (prodO u64O (listO updateO))));
    txn_mnat :> inG Σ (authR mnatUR);
  }.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!gen_heapPreG u64 heap_block Σ}.
Context `{!{K & gen_heapPreG u64 (updatable_buf (@bufDataT K)) Σ}}.
Context `{!gen_heapPreG addr {K & @bufDataT K} Σ}.
Context `{!txnG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition lockN : namespace := nroot .@ "txnlock".
Definition invN : namespace := nroot .@ "txninv".
Definition walN : namespace := nroot .@ "txnwal".

Definition mapsto_txn {K} (gData : gmap u64 {K & gen_heapG u64 (updatable_buf (@bufDataT K)) Σ})  (a : addr) (v : @bufDataT K) : iProp Σ :=
  ∃ hG γm,
    ⌜ valid_addr a ∧ valid_off K a.(addrOff) ⌝ ∗
    ⌜ gData !! a.(addrBlock) = Some (existT K hG) ⌝ ∗
    mapsto (hG := hG) a.(addrOff) 1 (UB v γm) ∗
    own γm (◯ (Excl' true)).

Theorem mapsto_txn_2 {K1 K2} gData a v0 v1 :
  @mapsto_txn K1 gData a v0 -∗
  @mapsto_txn K2 gData a v1 -∗
  False.
Proof.
  rewrite /mapsto_txn.
  iIntros "H0 H1".
  iDestruct "H0" as (g0 m0) "(% & % & H0m & H0own)".
  iDestruct "H1" as (g1 m1) "(% & % & H1m & H1own)".
  rewrite H1 in H3; inversion H3.
  subst.
  apply eq_sigT_eq_dep in H6.
  apply Eqdep_dec.eq_dep_eq_dec in H6; subst.
  2: apply bufDataKind_eq_dec.
  iDestruct (mapsto_valid_2 with "H0m H1m") as %x.
  exfalso; eauto.
Qed.

Theorem mapsto_txn_valid {K} gData a v :
  @mapsto_txn K gData a v -∗
  ⌜ valid_addr a ⌝.
Proof.
  rewrite /mapsto_txn.
  iIntros "H".
  iDestruct "H" as (h g) "[% _]"; intuition; done.
Qed.

Theorem mapsto_txn_valid_off {K} gData a v :
  @mapsto_txn K gData a v -∗
  ⌜ valid_off K a.(addrOff) ⌝.
Proof.
  rewrite /mapsto_txn.
  iIntros "H".
  iDestruct "H" as (h g) "[% _]"; intuition; done.
Qed.

Definition txn_bufDataT_in_block {K} (installed : Block) (bs : list Block)
                                 (gm : gmap u64 (updatable_buf (@bufDataT K))) : iProp Σ :=
  (
    [∗ map] off ↦ ub ∈ gm,
      match ub with
      | UB bufData γm =>
        ⌜ is_bufData_at_off (latest_update installed bs) off bufData ⌝ ∗
        ∃ (modifiedSinceInstall : bool),
          own γm (● (Excl' modifiedSinceInstall)) ∗
          if modifiedSinceInstall then emp
          else
            ⌜ ∀ prefix,
              is_bufData_at_off (latest_update installed (take prefix bs)) off bufData ⌝
      end
  )%I.

Global Instance txn_bufDataT_in_block_timeless K installed bs gm : Timeless (@txn_bufDataT_in_block K installed bs gm).
Proof.
  apply big_sepM_timeless; intros.
  destruct x.
  apply sep_timeless; refine _.
  apply exist_timeless.
  destruct x; refine _.
Qed.

Definition gmDataP (gm : {K & gmap u64 (updatable_buf (@bufDataT K))})
                   (gh : {K & gen_heapG u64 (updatable_buf (@bufDataT K)) Σ}) : iProp Σ.
  refine (if decide (projT1 gm = projT1 gh) then _ else False)%I.
  refine (gen_heap_ctx (hG := projT2 gh) _)%I.
  rewrite <- e.
  refine (projT2 gm).
Defined.

Definition is_txn_always
    (walHeap : gen_heapG u64 heap_block Σ)
    (gData   : gmap u64 {K & gen_heapG u64 (updatable_buf (@bufDataT K)) Σ})
    : iProp Σ :=
  (
    ∃ (mData : gmap u64 {K & gmap u64 (updatable_buf (@bufDataT K))}),
      "Hgmdata" ∷ ( [∗ map] _ ↦ gm;gh ∈ mData;gData, gmDataP gm gh ) ∗
      "Hmdata_m" ∷ ( [∗ map] blkno ↦ datamap ∈ mData,
          ∃ installed bs,
            "Hmdata_hb" ∷ mapsto (hG := walHeap) blkno 1 (HB installed bs) ∗
            "Hmdata_in_block" ∷ txn_bufDataT_in_block installed bs (projT2 datamap) )
  )%I.

Global Instance is_txn_always_timeless walHeap gData :
  Timeless (is_txn_always walHeap gData).
Proof.
  apply exist_timeless; intros.
  apply sep_timeless; refine _.
  apply big_sepM2_timeless; intros.
  rewrite /gmDataP.
  destruct (decide (projT1 x1 = projT1 x2)); refine _.
Qed.

Definition is_txn_locked l γ : iProp Σ :=
  (
    ∃ (nextId : u64) (pos : u64) lwh,
      "Hwal_latest" ∷ is_locked_walheap γ lwh ∗
      "Histxn_nextid" ∷ l ↦[Txn.S :: "nextId"] #nextId ∗
      "Histxn_pos" ∷ l ↦[Txn.S :: "pos"] #pos
 )%I.

Definition is_txn (l : loc)
    (gData   : gmap u64 {K & gen_heapG u64 (updatable_buf (@bufDataT K)) Σ})
    : iProp Σ :=
  (
    ∃ γLock (walHeap : wal_heap_gnames) (mu : loc) (walptr : loc),
      "Histxn_mu" ∷ readonly (l ↦[Txn.S :: "mu"] #mu) ∗
      "Histxn_wal" ∷ readonly (l ↦[Txn.S :: "log"] #walptr) ∗
      "Hiswal" ∷ is_wal walN (wal_heap_inv walHeap) walptr ∗
      "Histxna" ∷ inv invN (is_txn_always walHeap.(wal_heap_h) gData) ∗
      "Histxn_lock" ∷ is_lock lockN γLock #mu (is_txn_locked l walHeap)
  )%I.

Global Instance is_txn_persistent l gData : Persistent (is_txn l gData) := _.

Theorem is_txn_dup l gData :
  is_txn l gData -∗
  is_txn l gData ∗
  is_txn l gData.
Proof.
  iIntros "#$".
Qed.

Lemma gmDataP_eq gm gh :
  gmDataP gm gh -∗ ⌜ projT1 gm = projT1 gh ⌝.
Proof.
  iIntros "H".
  rewrite /gmDataP.
  destruct (decide (projT1 gm = projT1 gh)); eauto.
Qed.

Lemma gmDataP_ctx gm (gh : gen_heapG u64 (updatable_buf (@bufDataT (projT1 gm))) Σ) :
  gmDataP gm (existT (projT1 gm) gh) -∗
  gen_heap_ctx (hG := gh) (projT2 gm).
Proof.
  iIntros "H".
  rewrite /gmDataP /=.
  destruct (decide (projT1 gm = projT1 gm)); eauto.
  rewrite <- Eqdep.Eq_rect_eq.eq_rect_eq. iFrame.
Qed.

Lemma gmDataP_ctx' gm (gh : gen_heapG u64 (updatable_buf (@bufDataT (projT1 gm))) Σ) :
  gen_heap_ctx (hG := gh) (projT2 gm) -∗
  gmDataP gm (existT (projT1 gm) gh).
Proof.
  iIntros "H".
  rewrite /gmDataP /=.
  destruct (decide (projT1 gm = projT1 gm)); eauto.
  rewrite <- Eqdep.Eq_rect_eq.eq_rect_eq. iFrame.
Qed.

Theorem wp_txn_Load K l gData a v :
  {{{ is_txn l gData ∗
      mapsto_txn gData a v
  }}}
    Txn__Load #l (addr2val a) #(bufSz K)
  {{{ (bufptr : loc) b, RET #bufptr;
      is_buf bufptr a b ∗
      ⌜ b.(bufDirty) = false ⌝ ∗
      ⌜ existT b.(bufKind) b.(bufData) = existT K v ⌝ ∗
      mapsto_txn gData a v
  }}}.
Proof using gen_heapPreG0 heapG0 lockG0 Σ.
  iIntros (Φ) "(Htxn & Hstable) HΦ".
  iDestruct "Htxn" as (γMaps γLock walHeap mu walptr) "(#Hl & #Hwalptr & #Hwal & #Hinv & #Hlock)".
  iDestruct "Hstable" as (hG γm) "(% & % & Hstable & Hmod)".

  wp_call.
  wp_loadField.

  wp_call.

  wp_apply (wp_Walog__ReadMem _ _ (λ mb,
    mapsto a.(addrOff) 1 (UB v γm) ∗
    match mb with
    | Some b => own γm (◯ Excl' true) ∗
      ⌜ is_bufData_at_off b a.(addrOff) v ⌝
    | None => own γm (◯ Excl' false)
    end)%I with "[$Hwal Hstable Hmod]").
  {
    iApply (wal_heap_readmem walN (⊤ ∖ ↑walN ∖ ↑invN) with "[Hstable Hmod]").

    iInv invN as ">Hinv_inner" "Hinv_closer".
    iDestruct "Hinv_inner" as (mData) "(Hctxdata & Hdata)".

    iDestruct (big_sepM2_lookup_2_some with "Hctxdata") as %Hblk; eauto.
    destruct Hblk.

    iDestruct (big_sepM2_lookup_acc with "Hctxdata") as "[Hctxdatablk Hctxdata]"; eauto.
    iDestruct (gmDataP_eq with "Hctxdatablk") as "%".
    simpl in *; subst.
    iDestruct (gmDataP_ctx with "Hctxdatablk") as "Hctxdatablk".
    iDestruct (gen_heap_valid with "Hctxdatablk Hstable") as %Hblockoff.
    iDestruct ("Hctxdata" with "[Hctxdatablk]") as "Hctxdata".
    { iApply gmDataP_ctx'. iFrame. }

    iDestruct (big_sepM_lookup_acc with "Hdata") as "[Hdatablk Hdata]"; eauto.
    iDestruct "Hdatablk" as (blk_installed blk_bs) "(Hblk & Hinblk)".

    iExists _, _. iFrame.

    iModIntro.
    iIntros (mb) "Hrmq".
    destruct mb; rewrite /=.

    {
      iDestruct "Hrmq" as "[Hrmq %]".

      iDestruct (big_sepM_lookup_acc with "Hinblk") as "[Hinblk Hinblkother]"; eauto.
      iDestruct "Hinblk" as "(% & Hinblk)".
      iDestruct ("Hinblkother" with "[Hinblk]") as "Hinblk".
      { iFrame. done. }

      iDestruct ("Hinv_closer" with "[-Hmod]") as "Hinv_closer".
      {
        iModIntro.
        iExists _.
        iFrame.
        iApply "Hdata".
        iExists _, _. iFrame.
      }

      iMod "Hinv_closer".
      iModIntro.
      intuition; subst.
      iFrame. done.
    }

    {
      iDestruct (big_sepM_delete with "Hinblk") as "[Hinblk Hinblkother]"; eauto.
      rewrite /=.
      iDestruct "Hinblk" as "[% Hinblk]".
      iDestruct "Hinblk" as (modSince) "[Hγm Hinblk]".
      iDestruct (ghost_var_agree with "Hγm Hmod") as %->.
      iMod (ghost_var_update _ false with "Hγm Hmod") as "[Hγm Hmod]".

      iDestruct ("Hinv_closer" with "[-Hmod]") as "Hinv_closer".
      {
        iModIntro.
        iExists _.
        iFrame.
        iApply "Hdata".
        iExists _, _.
        iFrame.
        iDestruct (big_sepM_mono with "Hinblkother") as "Hinblkother".
        2: {
          replace (projT2 x) with (<[a.(addrOff) := UB v γm]> (delete a.(addrOff) (projT2 x))) at 2.
          2: {
            rewrite insert_delete.
            rewrite insert_id; eauto.
          }
          iApply big_sepM_insert; first apply lookup_delete.
          iFrame.
          iSplitR.
          { simpl. done. }
          iExists _; iFrame.
          iPureIntro; intros.
          rewrite take_nil /=. eauto.
        }

        intros.
        iIntros "H". destruct x0. rewrite /=.
        iDestruct "H" as "[% H]".
        iDestruct "H" as (modSince) "[H Hif]".
        iSplitR; eauto.
        iExists _. iFrame.
        destruct modSince; iFrame.
        iDestruct "Hif" as %Hif.
        iPureIntro. intros. rewrite take_nil. eauto.
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

    iDestruct ("Hres") as (b) "(Hisblock & Hlatest & Hown & %)".
    wp_pures.
    rewrite /is_block.
    wp_apply (wp_MkBufLoad with "[$Hisblock]").
    { intuition. }
    iIntros (bufptr) "Hbuf".
    wp_pures.
    iApply "HΦ". iFrame.
    rewrite /=.
    iSplitR; first done.
    iSplitR; first done.
    iExists _, _. iFrame. done.
  }

  (* Case 2: missed in cache *)
  iDestruct ("Hres") as "(Hlatest & Hown)".
  wp_pures.

  wp_apply (wp_Walog__ReadInstalled _ _
    (λ b, ⌜ is_bufData_at_off b a.(addrOff) v ⌝ ∗
      mapsto (hG := hG) a.(addrOff) 1 (UB v γm) ∗
      own γm (◯ (Excl' true)))%I
    with "[$Hwal Hlatest Hown]").
  {
    iApply (wal_heap_readinstalled walN (⊤ ∖ ↑walN ∖ ↑invN) with "[Hlatest Hown]").

    iInv invN as ">Hinv_inner" "Hinv_closer".
    iDestruct "Hinv_inner" as (mData) "(Hctxdata & Hdata)".

    iDestruct (big_sepM2_lookup_2_some with "Hctxdata") as %Hblk; eauto.
    destruct Hblk.

    iDestruct (big_sepM2_lookup_acc with "Hctxdata") as "[Hctxblock Hctxdata]"; eauto.
    iDestruct (gmDataP_eq with "Hctxblock") as "%".
    simpl in *; subst.
    iDestruct (gmDataP_ctx with "Hctxblock") as "Hctxblock".
    iDestruct (gen_heap_valid with "Hctxblock Hlatest") as %Hblockoff.
    iDestruct ("Hctxdata" with "[Hctxblock]") as "Hctxdata".
    { iApply gmDataP_ctx'. iFrame. }

    iDestruct (big_sepM_lookup_acc with "Hdata") as "[Hblock Hdata]"; eauto.
    iDestruct "Hblock" as (blk_installed blk_bs) "(Hblk & Hinblk)".

    iExists _, _. iFrame "Hblk".

    iModIntro.
    iIntros (b) "Hriq".
    iDestruct "Hriq" as "[Hriq %]".

    iDestruct (big_sepM_lookup_acc with "Hinblk") as "[Hinblk Hinblkother]"; eauto.
    rewrite /=.
    iDestruct "Hinblk" as "[% Hinblk]".
    iDestruct "Hinblk" as (modSince) "[Hγm Hinblk]".
    iDestruct (ghost_var_agree with "Hγm Hown") as %->.
    iMod (ghost_var_update _ true with "Hγm Hown") as "[Hγm Hown]".
    iDestruct "Hinblk" as %Hinblk.
    iFrame.

    iDestruct ("Hinv_closer" with "[-]") as "Hinv_closer".
    {
      iModIntro.
      iExists _.
      iFrame.
      iApply "Hdata".
      iExists _, _. iFrame.
      iApply "Hinblkother".
      iSplitR; first done.
      iExists _; iFrame.
    }

    iMod "Hinv_closer".
    iModIntro.
    iPureIntro.

    apply elem_of_list_lookup_1 in H3.
    destruct H3 as [prefix H3].
    specialize (Hinblk prefix).
    erewrite latest_update_take_some in Hinblk; eauto.
  }

  iIntros (bslice) "Hres".
  iDestruct "Hres" as (b) "(Hb & % & Hlatest & Hmod)".
  wp_pures.
  rewrite /is_block.
  wp_apply (wp_MkBufLoad with "[$Hb]").
  { intuition. }
  iIntros (bufptr) "Hbuf".
  wp_pures.
  iApply "HΦ".
  iFrame. rewrite /=.
  iSplitR; first done.
  iSplitR; first done.
  iExists _, _. iFrame. done.
Qed.

Definition is_txn_buf_pre (bufptr:loc) (a : addr) (buf : buf) gData : iProp Σ :=
  "Hisbuf" ∷ is_buf bufptr a buf ∗
  "Hmapto" ∷ ∃ data, @mapsto_txn buf.(bufKind) gData a data.

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

Definition updBlockKindOK blknum walBlock
              (gData : gmap u64 {K : bufDataKind & gen_heapG u64 (updatable_buf (bufDataT K)) Σ})
              (locked_wh_disk : disk) (offmap : gmap u64 buf) : Prop :=
  ∃ K gDataGH,
    gData !! blknum = Some (existT K gDataGH) ∧
    updBlockOK blknum walBlock K locked_wh_disk offmap.

Lemma valid_off_block blknum off :
  valid_addr (Build_addr blknum off) ->
  valid_off KindBlock off ->
  off = 0.
Proof.
  rewrite /valid_addr /valid_off /bufSz; intuition idtac.
  admit.
Admitted.

Lemma mapsto_txn_gGata_kind gData K a data :
  @mapsto_txn K gData a data -∗
  ∃ gDataGH,
    ⌜ gData !! a.(addrBlock) = Some (existT K gDataGH) ⌝.
Proof.
  iIntros "Hmapsto".
  iDestruct "Hmapsto" as (x y) "(% & % & H0 & H1)".
  iExists _. done.
Qed.

Theorem mapsto_txn_locked N γ l lwh a K data gData E :
  ↑invN ⊆ E ->
  ↑N ⊆ E ∖ ↑invN ->
  is_wal N (wal_heap_inv γ) l ∗
  inv invN (is_txn_always γ.(wal_heap_h) gData) ∗
  is_locked_walheap γ lwh ∗
  @mapsto_txn K gData a data
  ={E}=∗
    is_locked_walheap γ lwh ∗
    @mapsto_txn K gData a data ∗
    ⌜ ∃ v, locked_wh_disk lwh !! int.val a.(addrBlock) = Some v ⌝.
Proof.
  iIntros (H0 H1) "(#Hiswal & #Hinv & Hlockedheap & Hmapsto)".
  iInv "Hinv" as ">Htxnalways".
  iNamed "Htxnalways".
  iDestruct "Hmapsto" as (??) "(% & % & Hmapsto & Hown)".
  iDestruct (big_sepM2_lookup_2_some with "Hgmdata") as (x1) "%Hmdata"; eauto.
  iDestruct (big_sepM_lookup_acc with "Hmdata_m") as "[Ha Hmdata_m]"; eauto.
  iDestruct "Ha" as (installed bs) "[Ha Hb]".
  iMod (wal_heap_mapsto_latest with "[$Hiswal $Hlockedheap $Ha]") as "(Hlockedheap & Ha & %)"; eauto.
  iModIntro.
  iSplitL "Hgmdata Hmdata_m Ha Hb".
  { iNext. iExists _. iFrame.
    iApply "Hmdata_m". iExists _, _. iFrame. }
  iModIntro.
  iFrame.
  iSplitL.
  { iExists _, _. iFrame. done. }
  iExists _. done.
Qed.


Theorem wp_txn__installBufsMap l q gData walptr γ lwh bufs buflist (bufamap : gmap addr buf) :
  {{{ inv invN (is_txn_always γ.(wal_heap_h) gData) ∗
      is_wal walN (wal_heap_inv γ) walptr ∗
      readonly (l ↦[Txn.S :: "log"] #walptr) ∗
      is_locked_walheap γ lwh ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist,
        is_txn_buf_pre bufptrval a buf gData
  }}}
    Txn__installBufsMap #l (slice_val bufs)
  {{{ (blkmapref : loc) (blkmap : Map.t Slice.t), RET #blkmapref;
      is_locked_walheap γ lwh ∗
      is_map blkmapref blkmap ∗
      ( [∗ map] a ↦ buf ∈ bufamap,
        ∃ data, @mapsto_txn buf.(bufKind) gData a data ) ∗
      [∗ map] blkno ↦ blkslice; offmap ∈ blkmap; gmap_addr_by_block bufamap,
        ∃ b,
          is_block blkslice 1 b ∗
          ⌜ updBlockKindOK blkno b gData (locked_wh_disk lwh) offmap ⌝
  }}}.
Proof.
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
        "Hblks" ∷ is_map blks blkmap ∗
        "Hbufamap_todo" ∷ ( [∗ maplist] a↦buf;bufptrval ∈ bufamap_todo;todo, is_txn_buf_pre bufptrval a buf gData ) ∗
        "Hbufamap_done" ∷ ( [∗ map] blkno ↦ blkslice; offmap ∈ blkmap; gmap_addr_by_block bufamap_done,
          ∃ b,
            is_block blkslice 1 b ∗
            ⌜ updBlockKindOK blkno b gData (locked_wh_disk lwh) offmap ⌝ ) ∗
        "Hbufamap_done_mapsto" ∷ ( [∗ map] a↦buf ∈ bufamap_done, ∃ data, @mapsto_txn buf.(bufKind) gData a data ) ∗
        "Hlockedheap" ∷ is_locked_walheap γ lwh
      )%I
      with "[] [$Hbufs Hbufpre Hblks Hlockedheap]").
  2: {
    iExists bufamap, ∅, ∅.
    iSplitR; try done.
    iSplitR.
    { iPureIntro. rewrite map_difference_diag. done. }
    iFrame "Hblks". iFrame "Hbufpre". iFrame "Hlockedheap".
    iSplit.
    { rewrite gmap_addr_by_block_empty. iApply big_sepM2_empty. done. }
    iApply big_sepM_empty. done.
  }
  {
    iIntros (i b done todo).
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
      wp_pures.

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
      { admit. }
      iFrame "Hblks".
      iFrame "Hbufamap_todo".

      iDestruct (mapsto_txn_gGata_kind with "Hmapto") as (K) "%Hgdata_kind".
      iDestruct (mapsto_txn_valid with "Hmapto") as "%Haddr_valid".
      iDestruct (mapsto_txn_valid_off with "Hmapto") as "%Hoff_valid".

      iFrame "Hlockedheap".
      iSplitR "Hbufamap_done_mapsto Hmapto".
      2: {
        iApply (big_sepM_insert_2 with "[Hmapto] Hbufamap_done_mapsto").
        simpl. iExists _. iFrame.
      }
      rewrite /map_insert.
      rewrite gmap_addr_by_block_insert.
      iApply (big_sepM2_insert_2 with "[Hbufdata] Hbufamap_done").
      simpl.
      rewrite /is_buf_data /is_block.

      destruct buf; simpl in *.
      destruct bufData; try congruence.

      iExists _. iFrame. iPureIntro.
      eexists _, _. intuition eauto.
      intro diskLatest; intros.
      intro off; intros.

      eapply valid_off_block in Hoff_valid; eauto.
      eapply valid_off_block in H2; eauto.
      rewrite Hoff_valid. rewrite H2.
      rewrite lookup_insert.
      simpl. done.

    - wp_pures.
      wp_if_destruct.
      {
        exfalso.
        destruct buf; simpl in *.
        destruct bufKind; cbn in *; try congruence.
        all: admit.
      }

      wp_apply wp_ref_of_zero; first by eauto.
      iIntros (blkvar) "Hblkvar".

      wp_apply (wp_buf_loadField_addr with "Hisbuf"). iIntros "Hisbuf".
      wp_apply (wp_MapGet with "Hblks"). iIntros (v ok) "[% Hblks]".
      wp_pures.

      iDestruct (mapsto_txn_gGata_kind with "Hmapto") as (x) "%Hgdata".

      wp_apply (wp_If_join
        ( ∃ blkslice blk blkmap',
            "Hblkvar" ∷ blkvar ↦[slice.T byteT] (slice_val blkslice) ∗
            "Hisblock" ∷ is_block blkslice 1 blk ∗
            "Hbufamap_done" ∷ ( [∗ map] blkno↦blkslice;offmap ∈ delete a.(addrBlock) blkmap';
                  delete a.(addrBlock) (gmap_addr_by_block (bufamap ∖ bufamap_todo)),
                  ∃ b0 : Block,
                    is_block blkslice 1 b0
                    ∗ ⌜updBlockKindOK blkno b0 gData
                         (locked_wh_disk lwh) offmap⌝ ) ∗
            "Hisbuf" ∷ is_buf b a buf ∗
            "Hlockedheap" ∷ is_locked_walheap γ lwh ∗
            "Hblks" ∷ is_map blks blkmap' ∗
            "%" ∷ ⌜ blkmap' !! a.(addrBlock) = Some blkslice ⌝ ∗
            "%" ∷ ⌜ updBlockOK a.(addrBlock) blk buf.(bufKind) (locked_wh_disk lwh) (lookup_block (gmap_addr_by_block (bufamap ∖ bufamap_todo)) a.(addrBlock)) ⌝
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
        rewrite /lookup_block Hx.
        destruct H1. destruct H1. intuition eauto.
        rewrite Hgdata in H2. inversion H2. subst. eauto.
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

        rewrite /lookup_block Hnone.
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
      { admit. }
      iSplitR "Hbufamap_done_mapsto Hmapto".
      2: {
        iApply (big_sepM_insert_2 with "[Hmapto] [$Hbufamap_done_mapsto]").
        iExists _. iFrame. }
      rewrite gmap_addr_by_block_insert.
      replace (blkmap') with (<[a.(addrBlock) := blkslice]> blkmap') at 2.
      2: { rewrite insert_id; eauto. }
      iApply big_sepM2_insert_delete.
      iFrame "Hbufamap_done".
      iExists _. iFrame. iPureIntro.

      eexists _, _. intuition eauto.
      intro diskLatest; intros.
      intro off; intros.
      specialize (H2 diskLatest H3 off oldBufData H4 H5 H6).
      destruct (decide (a.(addrOff) = off)).
      + subst.
        rewrite lookup_insert.
        specialize (Hinstall_ok a.(addrOff)).
        destruct (decide (a.(addrOff) = a.(addrOff))); try congruence.
        destruct (lookup_block (gmap_addr_by_block (bufamap ∖ bufamap_todo))
                    a.(addrBlock) !! a.(addrOff)); eauto.
        intuition eauto.
        destruct b0; simpl in *.
        subst.
        eapply Hinstall_ok. eauto.

      + rewrite lookup_insert_ne; eauto.
        specialize (Hinstall_ok off).
        destruct (decide (off = a.(addrOff))); try congruence.
        destruct (lookup_block (gmap_addr_by_block (bufamap ∖ bufamap_todo))
                    a.(addrBlock) !! off); eauto.
        destruct b0; simpl in *. intuition subst.
        specialize (Hinstall_ok _ H7). eauto.
  }

  iIntros "[Hbufs H]". iNamed "H".
  wp_pures.

  iDestruct (big_sepML_empty_m with "Hbufamap_todo") as "%Hbufamap_todo_empty"; subst.
  replace (bufamap ∖ ∅) with (bufamap).
  2: { admit. }

  iApply "HΦ". iFrame.
Admitted.

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

Theorem wp_txn__installBufs l q gData walptr γ lwh bufs buflist (bufamap : gmap addr buf) :
  {{{ inv invN (is_txn_always γ.(wal_heap_h) gData) ∗
      is_wal walN (wal_heap_inv γ) walptr ∗
      readonly (l ↦[Txn.S :: "log"] #walptr) ∗
      is_locked_walheap γ lwh ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist,
        is_txn_buf_pre bufptrval a buf gData
  }}}
    Txn__installBufs #l (slice_val bufs)
  {{{ (blkslice : Slice.t) upds, RET (slice_val blkslice);
      is_locked_walheap γ lwh ∗
      updates_slice blkslice upds ∗
      ( [∗ map] a ↦ buf ∈ bufamap,
        ∃ data, @mapsto_txn buf.(bufKind) gData a data ) ∗
      [∗ maplist] blkno ↦ offmap; upd ∈ gmap_addr_by_block bufamap; upds,
        ⌜ upd.(update.addr) = blkno ⌝ ∗
        ⌜ updBlockKindOK blkno upd.(update.b) gData (locked_wh_disk lwh) offmap ⌝
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
                                          ⌜ updBlockKindOK blkno b gData (locked_wh_disk lwh) offmap ⌝ ) ∗
        "Hmdone" ∷ ( [∗ maplist] blkno↦offmap;upd ∈ offmaps_done;upds,
                                          ⌜ upd.(update.addr) = blkno ⌝ ∗
                                          ⌜ updBlockKindOK blkno upd.(update.b) gData (locked_wh_disk lwh) offmap ⌝ )
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
    { admit. }
    { iFrame. }
    iIntros (blks') "Hblks'".
    wp_store.
    iApply "HΦ'".

    iExists _, _, (delete k offmaps_todo), (<[k := x]> offmaps_done).
    iFrame "Hblks_var Hblks' Hmtodo".
    iSplitR.
    { iPureIntro. rewrite H1. admit. }
    iSplitR.
    { iPureIntro. set_solver. }
    iApply big_sepML_insert_app.
    { admit. }
    iFrame "Hmdone".
    simpl. done.
  }

  iIntros "[Hblkmapref H]".
  iNamed "H".
  wp_load.
  iDestruct (big_sepM2_empty_r with "Hmtodo") as "->".
  rewrite left_id in H0. subst.
  iApply "HΦ".
  iFrame.
Admitted.

Theorem wp_txn__doCommit l q gData bufs buflist bufamap :
  {{{ is_txn l gData ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist,
        is_txn_buf_pre bufptrval a buf gData
  }}}
    Txn__doCommit #l (slice_val bufs)
  {{{ (commitpos : u64) (ok : bool), RET (#commitpos, #ok);
      if ok then
        [∗ map] a ↦ buf ∈ bufamap,
          mapsto_txn gData a buf.(bufData)
      else emp
  }}}.
Proof.
  iIntros (Φ) "(#Htxn & Hbufs & Hbufpre) HΦ".
  iPoseProof "Htxn" as "Htxn0".
  iNamed "Htxn".

  wp_call.
  wp_loadField.
  wp_apply acquire_spec; eauto.
  iIntros "[Hlocked Htxnlocked]".

  wp_pures.
  iNamed "Htxnlocked".

  wp_apply (wp_txn__installBufs with "[$Histxna $Hiswal $Histxn_wal $Hbufs $Hbufpre $Hwal_latest]").
  iIntros (blks updlist) "(Hwal_latest & Hblks & Hmapstos & Hupdmap)".
  wp_pures.
  wp_apply util_proof.wp_DPrintf.
  wp_loadField.

  wp_apply (wp_Walog__MemAppend _ _
    (is_locked_walheap walHeap lwh)
    (λ npos, ∃ lwh', is_locked_walheap walHeap lwh' ∗ emp)%I
    with "[$Hiswal $Hblks Hupdmap Hmapstos $Hwal_latest]").
  { (*
    iApply (wal_heap_memappend _ (⊤ ∖ ↑walN ∖ ↑invN)). iFrame.
    iInv invN as ">Hinner" "Hinner_close".
    iModIntro.
    iNamed "Hinner".
    rewrite /memappend_pre.

    iDestruct (big_sepM_mono _
      (λ a buf,
        ( ∃ data : bufDataT buf.(bufKind), mapsto_txn gData a data ) ∗
        ⌜ ∃ γ, gData !! a.(addrBlock) = Some (existT buf.(bufKind) γ) ⌝
      )%I with "Hmapstos") as "Hmapstos".
    {
      iIntros (k x Hkx) "H".
      iDestruct "H" as (data h γ) "(% & % & H0 & H1)".
      iSplitL.
      { iExists _, _, _. iFrame. done. }
      iExists _. done.
    }
    iDestruct (big_sepM_sep with "Hmapstos") as "[Hmapstos #Hbufamap_gdata]".

    iDestruct (big_sepM2_mono _ (λ k gm gh, gmDataP gm gh ∗ emp)%I with "Hgmdata") as "Hgmdata".
    { iIntros; iFrame. }
    iDestruct (big_sepM2_sep with "Hgmdata") as "[Hgmdata #Hmdata_gmdata]".

    iDestruct (big_sepML_sepL with "Hupdmap") as "[#Hupdmap0 Hupdmap1]".
    iDestruct (big_sepML_map_val_exists with "Hupdmap0 []") as (mx) "Hx".
    {
      iIntros (k v lv Hkv Hp).
      specialize (Hcomplete k).
      destruct Hcomplete as [Hcomplete1 Hcomplete2].
      edestruct Hcomplete2 as [off Hoff]; eauto.
      destruct Hoff.

      iDestruct (big_sepM_lookup with "Hbufamap_gdata") as "%Hgdata"; eauto.
      destruct Hgdata. simpl in *.

      iDestruct (big_sepM2_lookup_2_some with "Hmdata_gmdata") as (mv) "%Hmdata"; eauto.

      iExists mv.
      iPureIntro.
      apply Hmdata.
    }

    iAssert (⌜ ∀ k v, mx !! k = Some v -> mData !! k = Some v ⌝)%I as "%Hsubset".
    { iIntros (k v Hkv).
      iDestruct (big_sepML_lookup_m_acc with "Hx") as (i lv) "(% & Hx2 & _)"; eauto.
      iDestruct "Hx2" as (_) "(Hx2 & _)". done.
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
      iDestruct "H0" as (_) "[H00 <-]".
      iDestruct "H1" as (installed bs) "[H10 H11]".
      iExists (installed, bs). iFrame. done. }

    iDestruct (big_sepML_exists with "Hx_mx") as (updlist_olds) "[-> Hx_mx]".
    iExists (snd <$> updlist_olds).

    iDestruct (big_sepML_sepL with "Hx_mx") as "[Hx_mx Hupdlist_olds]".

    iSplitL "Hupdlist_olds".
    {
      iApply big_sepL2_alt.
      iSplitR.
      { repeat rewrite fmap_length. eauto. }
      rewrite zip_fst_snd. iFrame.
    }

    iIntros (txn_id glatest') "[Hlatestfrag Hq]".
    rewrite /memappend_q.
    rewrite big_sepL2_alt.
    iDestruct "Hq" as "[_ Hq]".
    rewrite zip_fst_snd.

    (* XXX gen_heap_update for every item in bufamap *)

    iExists _. iFrame.
    iApply "Hinner_close".
    iNext.
    iExists _.
    admit.
  }

  iIntros (npos ok) "Hnpos".
  wp_pures.
  wp_storeField.
  wp_loadField.
(*
  wp_apply (release_spec with "[$Histxn_lock $Hlocked Histxn_nextid Hlatestfrag Histxn_pos]").
  { iExists _, _, _. iFrame. }

  wp_pures.
  iApply "HΦ".
  destruct ok; last by iFrame.
*)
*)
  admit.
Admitted.

Theorem wp_txn_CommitWait l q gData bufs buflist bufamap (wait : bool) (id : u64) :
  {{{ is_txn l gData ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist,
        is_txn_buf_pre bufptrval a buf gData
  }}}
    Txn__CommitWait #l (slice_val bufs) #wait #id
  {{{ (ok : bool), RET #ok;
      if ok then
        [∗ map] a ↦ buf ∈ bufamap,
          mapsto_txn gData a buf.(bufData)
      else emp
  }}}.
Proof.
  iIntros (Φ) "(#Htxn & Hbufs & Hbufpre) HΦ".

  wp_call.
  wp_apply wp_ref_to; [val_ty|].
  iIntros (commit) "Hcommit".
  wp_pures.
  wp_apply wp_slice_len.
  wp_pures.
  rewrite bool_decide_decide.
  destruct (decide (int.val 0 < int.val bufs.(Slice.sz))).
  - wp_pures.
    wp_apply (wp_txn__doCommit with "[$Htxn $Hbufs $Hbufpre]").
    iIntros (commitpos ok) "Hbufpost".

    wp_pures.
    destruct ok; wp_pures.
    + destruct wait; wp_pures.
      * iNamed "Htxn".
        wp_loadField.
        wp_apply (wp_Walog__Flush with "[$Hiswal]").
        { admit. }
        iIntros "HQ".
        wp_load.
        iApply "HΦ".
        admit.

      * wp_pures.
        wp_load.
        iApply "HΦ".
        iFrame.

    + wp_apply util_proof.wp_DPrintf.
      wp_store.
      wp_load.
      iApply "HΦ".
      iFrame.

  - wp_apply util_proof.wp_DPrintf.
    wp_load.
    iApply "HΦ".

    iDestruct (is_slice_sz with "Hbufs") as %Hbuflistlen.
    (* buflist is nil, so bufamap is ∅, so goal is emp *)
    iFrame.
Admitted.

Theorem wp_Txn__GetTransId l gData :
  {{{ is_txn l gData }}}
    txn.Txn__GetTransId #l
  {{{ (i : u64), RET #i; emp }}}.
Proof.
  iIntros (Φ) "#Htxn HΦ".
  iNamed "Htxn".
  wp_call.
  wp_loadField.
  wp_apply acquire_spec; eauto.
  iIntros "[Hlocked Htxnlocked]".
  iNamed "Htxnlocked".
  wp_loadField.
  wp_apply wp_ref_to; eauto.
  iIntros (id) "Hid".
  wp_pures.
  wp_load.
  wp_pures.
  destruct (bool_decide (#nextId = #0)); wp_pures.
  - wp_loadField.
    wp_storeField.
    wp_store.
    wp_loadField.
    wp_storeField.
    wp_loadField.
    wp_apply (release_spec with "[$Histxn_lock $Hlocked Hwal_latest Histxn_nextid Histxn_pos]").
    {
      iExists _, _, _. iFrame.
    }
    wp_load.
    iApply "HΦ". done.
  - wp_loadField.
    wp_storeField.
    wp_loadField.
    wp_apply (release_spec with "[$Histxn_lock $Hlocked Hwal_latest Histxn_nextid Histxn_pos]").
    {
      iExists _, _, _. iFrame.
    }
    wp_load.
    iApply "HΦ". done.
Qed.

End heap.
