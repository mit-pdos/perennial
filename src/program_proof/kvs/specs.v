From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import deletable_heap liftable.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import kvs.
From Perennial.program_proof Require Import txn.specs buftxn.specs.
From Perennial.goose_lang.lib Require Import encoding.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import marshal_proof.

Module kvpair.
  Record t :=
    mk { key: specs.addr;
         val: Slice.t
       }.
  Global Instance _eta: Settable _ := settable! mk <key; val>.
End kvpair.

Section heap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!lockG Σ}.
Context `{!buftxnG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Definition LogSz := 513.

Definition valid_key (key: specs.addr) (sz: nat):=
  key = specs.Build_addr key.(specs.addrBlock) 0 ∧
  specs.valid_addr key ∧
  int.val key.(specs.addrBlock) >= int.val LogSz ∧
  int.val key.(specs.addrBlock) < int.val sz.

Lemma valid_key_under_sz (kvsblks : gmap specs.addr {K & defs.bufDataT K}) key sz :
  valid_key key sz -> ∃ b, kvsblks !! key = Some (existT defs.KindBlock b).
Admitted.

Definition nat_key_to_addr key : specs.addr :=
  specs.Build_addr key 0.

(*XXXway to generalize from wal/abstractions.v?*)
Definition kvpair_val (pair : (specs.addr * Slice.t)): val :=
  (#(fst pair).(specs.addrBlock), (slice_val (snd pair), #()))%V.

Theorem kvpair_val_t key data : val_ty (kvpair_val (key, data)) (struct.t KVPair.S).
Proof.
  repeat constructor.
  rewrite /blockT; val_ty.
Qed.

(* Links a list of kvpairs to a slice *)
Definition kvpairs_slice (slice_val: Slice.t) (ls_kvps: list kvpair.t): iProp Σ :=
  ∃ slice_kvps, is_slice slice_val (struct.t KVPair.S) 1 (kvpair_val <$> slice_kvps)
                         ∗ [∗ list] _ ↦ slice_kvp;ls_kvp ∈ slice_kvps;ls_kvps,
  let '(kvpair.mk key bs) := ls_kvp in ∃ (blk: Block),
      ⌜bs = snd slice_kvp⌝ ∗
      is_block bs 1 blk ∗
      ⌜fst slice_kvp = key⌝.

Definition kvpairs_match (pairs: list kvpair.t) γDisk : iProp Σ :=
  [∗ list] kvp ∈ pairs, let '(kvpair.mk a bs) := kvp in
                        (∃ blk, is_block bs 1 blk ∗ mapsto_txn γDisk a (defs.bufBlock blk))%I.

Definition ptsto_kvs (kvsl: loc) (kvsblks : gmap specs.addr {K & defs.bufDataT K})
           (sz : nat) γDisk : iProp Σ :=
  ( ∃ (l : loc),
      kvsl↦[KVS.S :: "txn"] #l ∗
      kvsl ↦[KVS.S :: "sz"] #(U64 (Z.of_nat sz)) ∗
      is_txn l γDisk ∗
      ⌜(∀ n : nat, n < sz -> ∃ blk,
             kvsblks !! (nat_key_to_addr n) = Some (existT defs.KindBlock (defs.bufBlock blk))
      )⌝
      ∗ [∗ map] k↦b ∈ kvsblks, mapsto_txn γDisk k (projT2 b))%I.

Definition crashed_kvs kvp_ls kvsblks γDisk : iProp Σ :=
      ([∗ map] k↦b ∈ kvsblks, mapsto_txn γDisk k (projT2 b))%I
      ∗ kvpairs_match kvp_ls γDisk.

Definition ptsto_kvpair (l: loc) (pair: specs.addr * Slice.t) : iProp Σ :=
  (l↦[struct.t KVPair.S] (kvpair_val pair) ∗ ∃ blk, is_block (snd pair) 1 blk)%I.

Theorem wpc_MkKVS d (sz: nat) k E1 E2:
  {{{ True }}}
    MkKVS #d #(U64(Z.of_nat sz)) @ NotStuck; k; E1; E2
  {{{ kvsl kvsblks γDisk, RET #kvsl; ptsto_kvs kvsl kvsblks sz γDisk}}}
  {{{ True }}}.
Proof.
  iIntros (ϕ ϕc) "_ Hϕ".
  rewrite /MkKVS.
  wpc_pures; eauto.
  wpc_bind (super.MkFsSuper _).
Admitted.

Lemma is_slice_small_same data1 data2 blk :
  is_slice_small data1 u8T 1 (Block_to_vals blk) ∗ is_slice_small data2 u8T 1 (Block_to_vals blk) -∗
  is_slice_small data1 u8T 1 (Block_to_vals blk) ∗ is_slice_small data2 u8T 1 (Block_to_vals blk) ∗ ⌜data1=data2⌝.
Proof.
  iIntros "[H1 H2]".
  unfold is_slice_small.
  iDestruct "H1" as "[HD1 %Hl1]".
  iDestruct "H2" as "[HD2 %Hl2]".
  induction data1; induction data2; subst.
  simpl in *.
  admit.
Admitted. (*XXX is this true??? *)

 Theorem wpc_KVS__Get kvsl kvsblks sz γDisk key blk data:
  {{{
       ptsto_kvs kvsl kvsblks sz γDisk
       ∗ ⌜kvsblks !! key = Some (existT defs.KindBlock (defs.bufBlock blk))⌝
       ∗ ⌜valid_key key sz⌝
       ∗ specs.is_buf_data data (defs.bufBlock blk) key
  }}}
    KVS__Get #kvsl #((key.(specs.addrBlock)))
    {{{(pairl: loc) ok, RET (#pairl, #ok);
       ptsto_kvs kvsl kvsblks sz γDisk
       ∗ ⌜kvsblks !! key = Some (existT defs.KindBlock (defs.bufBlock blk))⌝
                                ∗ ptsto_kvpair pairl (key, data)
  }}}.
Proof.
  iIntros (ϕ) "[Hkvs [%HkeyLookup [%Hkey Hdata]]] Hϕ".
  iDestruct "Hkvs" as (l) "[Htxnl [Hsz [#Htxn [%HinKvs HkvsMt]]]]".
  pose Hkey as Hkey'.
  destruct Hkey' as [HbuildAddr [Hkaddr [Hklgsz Hsz]]].
  wp_call.
  wp_loadField.
  wp_pures.
  remember(bool_decide (int.val sz < int.val _)) as Hszcomp.
  destruct Hszcomp; wp_pures.
  - wp_apply wp_panic.
    destruct (decide_rel Z.lt (int.val sz) _); try discriminate. lia.
  - change (u64_instance.u64.(@word.add 64) (u64_instance.u64.(@word.divu 64) (u64_instance.u64.(@word.sub 64) 4096 8) 8) 2)
      with (U64 LogSz).
    remember(bool_decide (int.val _ < int.val LogSz)) as Hlgszcomp.
    destruct Hlgszcomp; wp_pures.
    * wp_apply wp_panic.
      destruct (decide_rel Z.lt _ (int.val LogSz)); try discriminate. lia.
    * wp_loadField.
      wp_apply (wp_buftxn_Begin l γDisk _ with "[Htxn]"); auto.
      iIntros (buftx γt) "Hbtxn".
      wp_let.
      wp_call.
      change (u64_instance.u64.(@word.mul 64) 4096 8) with (U64 32768).
      change (#key.(specs.addrBlock), (#0, #()))%V with (specs.addr2val (specs.Build_addr key.(specs.addrBlock) 0)).
      pose Hkey as Hkey'.

      (*rewrite Map.delete_insert_union _ _ _ _ kvsblks {[key := Some (existT defs.KindBlock blk)]} key (existT defs.KindBlock blk).*)
      pose ({[key := existT defs.KindBlock (defs.bufBlock blk)]} : gmap (specs.addr) ({K & defs.bufDataT K})) as keyMp.
      assert ((delete key kvsblks) ##ₘ keyMp) as HMapDisjoint.
      {
        apply map_disjoint_singleton_r.
        apply lookup_delete.
      }
      assert ((delete key kvsblks) ∪ keyMp = kvsblks) as HMapUnion.
      { rewrite Map.delete_insert_union; auto.
        eapply (union_empty_r kvsblks).
        unfold elem_of. auto.
      }
      rewrite <- HMapUnion.
      iPoseProof (big_opM_union (λ k b, mapsto_txn γDisk k (projT2 b)) (delete key kvsblks) keyMp) as "H"; auto.
      iPoseProof ("H" with "HkvsMt") as "HkvsMt".
      iDestruct "HkvsMt" as "[HrestMt HkeyMt]".

      iMod (BufTxn_lift buftx _ γDisk keyMp with "[Hbtxn HkeyMt]") as "[Hbtxn HkeyMt]"; iFrame; eauto.

      wp_apply (wp_BufTxn__ReadBuf buftx γt γDisk (specs.Build_addr key.(specs.addrBlock) 0) 32768 with "[Hbtxn HkeyMt]").
      -- iSplitL "Hbtxn"; auto.
         iSplitL "HkeyMt".
         {
           rewrite <- HbuildAddr. simpl.
           iPoseProof (big_sepM_lookup _ keyMp key (existT defs.KindBlock (defs.bufBlock blk)) with "HkeyMt") as "HsepM"; eauto.
           pose (lookup_union_r (delete key kvsblks) (keyMp) key) as Hun.
           rewrite <- HMapUnion in HkeyLookup.
           assert ((delete key kvsblks) !! key =None) as Hdel by apply lookup_delete.
           apply Hun in Hdel. rewrite HkeyLookup in Hdel. auto.
         }
         { simpl. auto. }
      -- iIntros (bptr dirty) "[HisBuf HPostRead]".
         simpl in *.
         iSpecialize ("HPostRead" $! (defs.bufBlock blk) dirty).
         iDestruct "HisBuf" as (data0 sz0) "[Hbaddr [Hbsz [Hbdata [Hbdirty [HvalidA [Hsz0 [Hnotnil HisBufData]]]]]]]".

         iPoseProof (is_slice_small_same data data0 blk with "[Hdata HisBufData]") as "[Hdata [HisBufData <-]]"; iFrame; eauto.

         wp_loadField; wp_let.
         iMod ("HPostRead" with "[-Hϕ Htxnl Hsz HrestMt Hdata]") as "[Hmapsto HisBuf]"; unfold specs.is_buf.
         { iSplit; eauto. iExists data, sz0; iFrame; auto. }
         wp_apply (wp_BufTxn__CommitWait buftx γt γDisk {[key := existT defs.KindBlock (defs.bufBlock blk)]} with "[Hmapsto HisBuf]").
         {
           iFrame; auto.
           rewrite <- HbuildAddr, big_opM_singleton; auto.
         }
         iIntros (ok) "Hmapsto".
         iPoseProof ("H" with "[HrestMt Hmapsto]") as "HkvsMt"; iFrame; auto.
         wp_let.
         wp_pures.
         wp_apply wp_allocStruct; [ val_ty | iIntros (lptr) "Hs" ].
         wp_pures. iApply ("Hϕ" $! lptr).
         iSplitL "Htxnl Hsz HkvsMt".
         { unfold ptsto_kvs. iExists l. rewrite HMapUnion. iFrame; auto. }
         iSplitR; rewrite HMapUnion; auto.
         {
           unfold ptsto_kvpair.
           unfold ptsto_kvpair, is_block, kvpair_val. simpl in *.
           change u8T with byteT.
           iFrame; auto.
         }
Admitted.

Theorem wpc_KVS__MultiPut kvsl s sz kvp_ls_before kvp_slice kvp_ls stk k E1 E2:
  {{{
       ptsto_kvs kvsl s sz
                 ∗ kvpairs_match s kvp_ls_before
                 ∗ kvpairs_slice kvp_slice kvp_ls
  }}}
    KVS__MultiPut #kvsl (slice_val kvp_slice) @ stk; k; E1; E2
  {{{ (ok: bool), RET #ok;
      ptsto_kvs kvsl s sz ∗ kvpairs_match s kvp_ls
  }}}
  {{{ crashed_kvs s sz kvp_ls ∨ crashed_kvs s sz kvp_ls_before }}}.
Proof.
Admitted.
End heap.
