From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import deletable_heap liftable log_heap.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import addr.specs.
From Perennial.program_proof Require Import buf.specs buf.defs.
From Perennial.program_proof Require Import txn.specs.
(*
From Perennial.program_proof Require Import buftxn.specs.
*)


Module state.
  Record ver := mkver {
    b0 : Block;
    b1 : Block;
  }.
  Global Instance _eta: Settable _ := settable! mkver <b0; b1>.
  Global Instance ver_eqdec : EqDecision ver. Admitted.
  Global Instance ver_countable : Countable ver. Admitted.
  Definition t := async ver.
End state.


Section heap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!lockG Σ}.
Context `{!txnG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Definition LogSz := 513.
Definition A0 := LogSz + 0.
Definition A1 := LogSz + 1.

Definition is_ver γ (v : state.ver) : iProp Σ :=
  "Hv0" ∷ is_lock (mapsto (hG := γ) (Build_addr A0 0) 1%Qp (existT _ (bufBlock v.(state.b0)))) ∗
  "Hv1" ∷ is_lock (mapsto (Build_addr A1 0) 1%Qp (existT _ (bufBlock v.(state.b1)))).

Definition is_state (l : loc) γ (sl : state.t) : iProp Σ :=
  ∃ txn_id,
    "#Histxn" ∷ is_txn l γ ∗
    "Hpossible" ∷ is_ver γ (latest sl).




Definition is_ver (M : addr -> {K & bufDataT K} -> iProp Σ) (v : state.ver) : iProp Σ :=
  "Hv0" ∷ M (Build_addr A0 0) (existT _ (bufBlock v.(state.b0))) ∗
  "Hv1" ∷ M (Build_addr A1 0) (existT _ (bufBlock v.(state.b1))).

Definition is_state (l : loc) γ (sl : state.t) : iProp Σ :=
  ∃ txn_id,
    "#Histxn" ∷ is_txn l γ ∗
    "Hpossible" ∷ [∗ list] i ↦ s ∈ possible sl,
      is_ver (λ a v, mapsto_range (hG := γ.(txn_logheap)) (txn_id+i) (S txn_id+i) a 1%Qp v) s.

(* Q1: where does mapsto_txn go?
  could go into lockmap, but is this the way it's usually done?
*)

(* Q2: how to re-prove [is_ver] for a new txn_id without decomposing into mapsto facts? *)

Example is_state_write_0 l γ sl first data' data E :
  is_state l γ sl ∗
  mapsto_txn γ first (Build_addr A0 0) (existT KindBlock data')
(*
  ( ∀ a q v,
      a ∉ writtenBufs ->
      mapsto_range γ first (S first) a q v -∗
      mapsto_range γ (S first) (S (S first)) a q v )
*)
  ={E}=∗
  ∃ txn_id,
    is_state l γ (async_put (set state.b0 (λ _, data) (latest sl)) sl) ∗
    mapsto_txn γ txn_id (Build_addr A0 0) (existT KindBlock (bufBlock data)).
Proof.
  iIntros "[Hs H0]".
  iNamed "Hs".
  rewrite /possible. iDestruct (big_sepL_app with "Hpossible") as "[Hpossible Hlatest]".
  iDestruct "Hlatest" as "[Hlatest _]".
  iNamed "Hlatest".
  iNamed "H0".
  iDestruct (mapsto_cur_range_agree with "Hmapsto_log Hv0") as %Hagree.
  { admit. }

  iNamed "Histxn".
(*
  iInv "Histxna" as "Htxinv". "Htxinv_close".
*)
  iDestruct (mapsto_cur_snapshot with "[] Hmapsto_log") as "[Hmapsto_log Hmapsto_snap]".
  { admit. }

  iModIntro.
  iExists 0%nat.
  iSplitR "Hmapsto_log Hmapsto_meta Hmod_frag".
  2: { iExists _. iFrame. admit. }

  { iExists _. iSplitR.
    { admit. }
    iFrame. rewrite big_sepL_nil.
    iSplitR; first by done.
    simpl.
    iSplitL; last by done.
    unfold is_ver.
    unfold set. simpl.
    
  }
Admitted.


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
      ∗ pairl ↦[struct.t KVPair.S] (kvpair_val (pair key data))
  }}}.
Proof.
  iIntros (ϕ) "[Hkvs [%HkeyLookup %Hkey ]] Hϕ".
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

      iDestruct (big_sepM_lookup_acc (λ k b, mapsto_txn γDisk k (projT2 b)) kvsblks key (existT defs.KindBlock (defs.bufBlock blk)) HkeyLookup with "HkvsMt") as "[HkeyMt HrestMt]".
      pose ({[key := existT defs.KindBlock (defs.bufBlock blk)]} : gmap (specs.addr) ({K & defs.bufDataT K})) as keyMp.

      iMod (BufTxn_lift buftx _ γDisk keyMp with "[Hbtxn HkeyMt]") as "[Hbtxn HkeyMt]"; iFrame; eauto.
      { iApply big_sepM_singleton; auto. }

      wp_apply (wp_BufTxn__ReadBuf buftx γt γDisk (specs.Build_addr key.(specs.addrBlock) 0) 32768 with "[Hbtxn HkeyMt]").
      -- iSplitL "Hbtxn"; auto.
         iSplitL "HkeyMt".
         {
           rewrite <- HbuildAddr. simpl.
           iPoseProof (big_sepM_lookup _ keyMp key (existT defs.KindBlock (defs.bufBlock blk)) with "HkeyMt") as "HsepM"; eauto.
           apply lookup_singleton.
         }
         { simpl. auto. }
      -- iIntros (bptr dirty) "[HisBuf HPostRead]".
         simpl in *.
         iSpecialize ("HPostRead" $! (defs.bufBlock blk) dirty).
         iDestruct "HisBuf" as (data sz0) "[Hbaddr [Hbsz [Hbdata [Hbdirty [HvalidA [Hsz0 [Hnotnil HisBufData]]]]]]]".
         wp_loadField.
         wp_apply (util_proof.wp_CloneByteSlice with "HisBufData").
         iIntros (data') "[HisBlkData HisBlkData']".

         wp_let.
         iMod ("HPostRead" with "[-Hϕ Htxnl Hsz HrestMt HisBlkData']") as "[Hmapsto HisBuf]"; unfold specs.is_buf.
         { iSplit; eauto. iExists data, sz0; iFrame; auto. }
         wp_apply (wp_BufTxn__CommitWait buftx γt γDisk {[key := existT defs.KindBlock (defs.bufBlock blk)]} with "[Hmapsto HisBuf]").
         {
           iFrame; auto.
           rewrite <- HbuildAddr, big_opM_singleton; auto.
         }
         iIntros (ok) "Hmapsto".
         rewrite big_sepM_singleton.
         iPoseProof ("HrestMt" with "Hmapsto") as "Hmapsto".
         wp_let.
         wp_pures.
         wp_apply wp_allocStruct; [ val_ty | iIntros (lptr) "Hs" ].
         wp_pures. iApply ("Hϕ" $! lptr).
         iSplitL "Htxnl Hsz Hmapsto".
         { unfold ptsto_kvs. iExists l. iFrame; auto. }
         iSplitR; auto.
         {
           iFrame; eauto.
           unfold is_block.
           iApply is_slice_to_small; auto.
         }
Qed.

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
