From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import deletable_heap.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import kvs.
From Perennial.program_proof Require Import txn.txn_proof buftxn.buftxn_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import NamedProps Map List.

Module kvpair.
  Record t :=
    mk { key: specs.addr;
         val: Slice.t
       }.
  Global Instance _eta: Settable _ := settable! mk <key; val>.
End kvpair.

Section heap.
Context `{!lockG Σ}.
Context `{!buftxnG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Definition LogSz := 513.

Definition valid_key (key: specs.addr) (sz: nat):=
  key = specs.Build_addr key.(specs.addrBlock) 0 ∧
  specs.valid_addr key ∧
  int.Z key.(specs.addrBlock) >= int.Z LogSz ∧
  int.Z key.(specs.addrBlock) < int.Z sz.

Lemma valid_key_under_sz (kvsblks : gmap specs.addr {K & defs.bufDataT K}) key sz :
  valid_key key sz -> ∃ b, kvsblks !! key = Some (existT defs.KindBlock b).
Admitted.

Definition nat_key_to_addr key : specs.addr :=
  specs.Build_addr key 0.

(*XXXway to generalize from wal/abstractions.v?*)
Definition kvpair_val (pair : kvpair.t): val :=
  (#(pair.(kvpair.key).(specs.addrBlock)), (slice_val (pair.(kvpair.val)), #()))%V.

Theorem kvpair_val_t key data : val_ty (kvpair_val (kvpair.mk key data)) (struct.t KVPair.S).
Proof.
  repeat constructor.
  rewrite /blockT; val_ty.
Qed.

(* Links a list of kvpairs to a slice *)
Definition kvpairs_valid_slice (slice_val: Slice.t) (ls_kvps: list kvpair.t) sz: iProp Σ :=
  ∃ slice_kvps, is_slice slice_val (struct.t KVPair.S) 1 (kvpair_val <$> slice_kvps)
                         ∗ [∗ list] _ ↦ slice_kvp;ls_kvp ∈ slice_kvps;ls_kvps,
  let '(kvpair.mk key bs) := ls_kvp in ∃ (blk: Block),
      ⌜slice_kvp.(kvpair.key) = key ∧ valid_key key sz⌝ ∗
      ⌜bs = slice_kvp.(kvpair.val)⌝ ∗
      is_block bs 1 blk.

Definition kvpairs_valid_match (pairs: list kvpair.t) (kvsblks : gmap specs.addr {K & defs.bufDataT K}) γDisk sz : iProp Σ :=
  [∗ list] kvp ∈ pairs, let '(kvpair.mk key bs) := kvp in
                        (∃ blk, is_block bs 1 blk ∗ mapsto_txn γDisk key (existT defs.KindBlock (defs.bufBlock blk))
        ∗ ⌜kvsblks !! key = Some (existT defs.KindBlock (defs.bufBlock blk))⌝
        ∗ ⌜valid_key key sz⌝)%I.

Definition ptsto_kvs (kvsl: loc) (kvsblks : gmap specs.addr {K & defs.bufDataT K})
           (sz : nat) γDisk : iProp Σ :=
  ( ∃ (l : loc),
      kvsl↦[KVS.S :: "txn"] #l ∗
      kvsl ↦[KVS.S :: "sz"] #(U64 (Z.of_nat sz)) ∗
      is_txn l γDisk ∗
      ⌜(∀ n : nat, n < sz -> ∃ blk,
             kvsblks !! (nat_key_to_addr n) = Some (existT defs.KindBlock (defs.bufBlock blk))
      )⌝
      ∗ [∗ map] k↦b ∈ kvsblks, mapsto_txn γDisk k b)%I.

Definition crashed_kvs kvp_ls kvsblks γDisk sz : iProp Σ :=
      ([∗ map] k↦b ∈ kvsblks, mapsto_txn γDisk k b)%I
      ∗ kvpairs_valid_match kvp_ls kvsblks γDisk sz.

Theorem wpc_MkKVS d (sz: nat) k E1 E2:
  {{{ True }}}
    MkKVS #d #(U64(Z.of_nat sz)) @ NotStuck; k; E1; E2
  {{{ kvsl kvsblks γDisk, RET #kvsl; ptsto_kvs kvsl kvsblks sz γDisk}}}
  {{{ True }}}.
Proof.
  iIntros (ϕ ϕc) "_ Hϕ".
  rewrite /MkKVS.
  wpc_pures; eauto.
Admitted.

 Theorem wpc_KVS__Get kvsl kvsblks sz γDisk key blk:
  {{{
       ptsto_kvs kvsl kvsblks sz γDisk
       ∗ ⌜kvsblks !! key = Some (existT defs.KindBlock (defs.bufBlock blk))⌝
       ∗ ⌜valid_key key sz⌝
  }}}
    KVS__Get #kvsl #((key.(specs.addrBlock)))
    {{{(pairl: loc) ok data, RET (#pairl, #ok);
       ptsto_kvs kvsl kvsblks sz γDisk
      (* State of KVS remains unchanged *)
      ∗ ⌜kvsblks !! key = Some (existT defs.KindBlock (defs.bufBlock blk))⌝
      (* Data returned is the data at the specified kvs block *)
      ∗ is_block data 1 blk
      (* Data returned is in the form of a kvpair *)
      ∗ pairl ↦[struct.t KVPair.S] (kvpair_val (kvpair.mk key data))
  }}}.
Proof.
  iIntros (ϕ) "[Hkvs [%HkeyLookup %Hkey ]] Hϕ".
  iDestruct "Hkvs" as (l) "[Htxnl [Hsz [#Htxn [%HinKvs HkvsMt]]]]".
  pose Hkey as Hkey'.
  destruct Hkey' as [HbuildAddr [Hkaddr [Hklgsz Hsz]]].
  wp_call.
  wp_loadField.
  wp_pures.
  remember(bool_decide (int.Z sz < int.Z _)) as Hszcomp.
  destruct Hszcomp; wp_pures.
  - wp_apply wp_panic.
    destruct (decide_rel Z.lt (int.Z sz) _); try discriminate. lia.
  - change (u64_instance.u64.(@word.add 64) (u64_instance.u64.(@word.divu 64) (u64_instance.u64.(@word.sub 64) 4096 8) 8) 2)
      with (U64 LogSz).
    remember(bool_decide (int.Z _ < int.Z LogSz)) as Hlgszcomp.
    destruct Hlgszcomp; wp_pures.
    * wp_apply wp_panic.
      destruct (decide_rel Z.lt _ (int.Z LogSz)); try discriminate. lia.
    * wp_loadField.
      wp_apply (wp_buftxn_Begin l γDisk _ with "[Htxn]"); auto.
      iIntros (buftx) "Hbtxn".
      wp_let.
      wp_call.
      change (u64_instance.u64.(@word.mul 64) 4096 8) with (U64 32768).
      change (#key.(specs.addrBlock), (#0, #()))%V with (specs.addr2val (specs.Build_addr key.(specs.addrBlock) 0)).
      pose Hkey as Hkey'.

      iDestruct (big_sepM_lookup_acc (λ k b, mapsto_txn γDisk k b) kvsblks key (existT defs.KindBlock (defs.bufBlock blk)) HkeyLookup with "HkvsMt") as "[HkeyMt HrestMt]".
      pose ({[key := existT defs.KindBlock (defs.bufBlock blk)]} : gmap (specs.addr) ({K & defs.bufDataT K})) as keyMp.

      iDestruct (BufTxn_lift buftx _ γDisk keyMp _ with "[Hbtxn HkeyMt]") as "He".
      1: admit. (* E top? *)
      1: iFrame.
      { iApply big_sepM_singleton; auto. }
      rewrite right_id.
      iMod "He".

      wp_apply (wp_BufTxn__ReadBuf buftx keyMp γDisk (specs.Build_addr key.(specs.addrBlock) 0) (Z.to_nat 32768) with "[He]").
      -- iSplitL "He"; auto.
         iPureIntro. split.
         {
           rewrite <- HbuildAddr. simpl.
           apply lookup_insert.
         }
         { simpl. auto. }
      -- iIntros (bptr dirty) "[HisBuf HPostRead]".
         simpl in *.
         iSpecialize ("HPostRead" $! (defs.bufBlock blk) dirty).
         iNamed "HisBuf". simpl.
         iDestruct "Hisbuf_without_data" as (sz0) "[Hbaddr [Hbsz [Hbdata Hbdirty]]]"; simpl.
         wp_loadField.
         wp_apply (util_proof.wp_CloneByteSlice with "Hbufdata").
         iIntros (data') "[HisBlkData HisBlkData']".

         wp_let.
         iMod ("HPostRead" with "[-Hϕ Htxnl Hsz HrestMt HisBlkData']") as "HisBuf"; unfold specs.is_buf.
         { iSplit; eauto. iExists data. iFrame; auto. iExists sz0; simpl. iSplitL "Hbsz"; auto. }
         (* {[key := existT defs.KindBlock (defs.bufBlock blk)]} *)
         wp_apply (wp_BufTxn__CommitWait _ _ γDisk _ _
                                       (* TODO: need a real Q *)
                                       (λ _, emp)%I  with "[HisBuf]").
         {
           iFrame; auto.
           rewrite -HbuildAddr.
           admit.
         }
         iIntros (ok) "Hpost".
Admitted.

Theorem wpc_KVS__MultiPut kvsl kvsblks sz γDisk kvp_ls_before kvp_ls_new kvp_slice:
  {{{
       ptsto_kvs kvsl kvsblks sz γDisk
       ∗ kvpairs_valid_match kvp_ls_before kvsblks γDisk sz
       ∗ kvpairs_valid_slice kvp_slice kvp_ls_new sz
  }}}
    KVS__MultiPut #kvsl (slice_val kvp_slice)
  {{{ (ok: bool), RET #ok;
      ptsto_kvs kvsl kvsblks sz γDisk
       ∗ kvpairs_valid_match kvp_ls_new kvsblks γDisk sz
  }}}.
Proof.
  iIntros (ϕ) "[Hkvs [HkvpBefore HkvpArgs]] Hϕ".
  iDestruct "Hkvs" as (l) "[Htxnl [Hsz [#Htxn [%HinKvs HkvsMt]]]]".
  wp_call.
  wp_loadField.
  wp_pures.
  wp_apply (wp_buftxn_Begin l γDisk _ with "[Htxn]"); auto.
  iIntros (buftx) "Hbtxn".
  wp_let.
  wp_apply (wp_forSlicePrefix
        (fun done todo =>
           ∃ kvp_ls_done kvp_ls_todo kvsblks_todo kvsblks_done,
                     "<-" ∷ ⌜ kvp_ls_done ++ kvp_ls_todo = kvp_ls_new ⌝ ∗
        "->" ∷ ⌜ kvsblks_done = kvsblks ∖ kvsblks_todo ⌝ ∗
        "%" ∷ ⌜ kvsblks_todo ⊆ kvsblks ⌝ ∗
        "Hkvs" ∷ (ptsto_kvs kvsl kvsblks sz γDisk) ∗
        "Hdone_kvp_val" ∷ ([∗ list] val; kvp ∈ done; kvp_ls_done, ⌜ val = kvpair_val kvp ⌝) ∗
        "Htodo_kvp_val" ∷ ([∗ list] val; kvp ∈ todo; kvp_ls_todo, ⌜ val = kvpair_val kvp ⌝) ∗
        "Hkvp_done_match_new" ∷ kvpairs_valid_match kvp_ls_done kvsblks_done γDisk sz
        )%I with "[Hsz Htxnl]").
  { iIntros (i x vs vs').
    iModIntro.
    iIntros (lϕ) "Hinv HΦ"; iNamed "Hinv".
    wp_pures.
    iDestruct "Hkvs" as (l') "(txn&sz&Htxn'&%&Hkvsblks)".
    wp_loadField.
    wp_pures.

Admitted.


End heap.
