From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import liftable log_heap.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import wal.specs wal.heapspec.
From Perennial.program_proof Require Import addr.addr_proof.
From Perennial.program_proof Require Import buf.buf_proof.
From Perennial.program_proof Require Import obj.obj_proof.
From Perennial.program_proof Require Import jrnl.jrnl_proof.
From Perennial.goose_lang Require Import spec_assert.


Module state.
  Record t := mk {
    b0 : async {K & bufDataT K};
    b1 : async {K & bufDataT K};
  }.
  Global Instance _eta: Settable _ := settable! mk <b0; b1>.
  Global Instance ver_eqdec : EqDecision t. Admitted.
  Global Instance ver_countable : Countable t. Admitted.
End state.


Section heap.
Context `{!heapGS Σ}.
Context `{!txnG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Definition LogSz := 513.
Definition A0 : addr := (Build_addr (LogSz + 0) 0).
Definition A1 : addr := (Build_addr (LogSz + 1) 0).

Theorem a0_a1 : A0 ≠ A1.
  unfold A0, A1, LogSz. intro H.
  inversion H.
Qed.

Hint Resolve a0_a1 : core.


Definition kvN := nroot .@ "kv".

Definition is_one_of {T} (o : option T) (choices : async T) :=
  ∃ v,
    o = Some v ∧
    v ∈ possible choices.

Lemma is_one_of_put T o av (v' : T) :
  is_one_of o av ->
  is_one_of o (async_put v' av).
Proof.
  intros.
  destruct H; intuition idtac.
  eexists _; intuition eauto.
  unfold possible in H1.
  rewrite /async_put /possible /=.
  eapply elem_of_app.
  eauto.
Qed.

Lemma is_one_of_latest T (v : T) av :
  is_one_of (Some v) (async_put v av).
Proof.
  intros.
  eexists _. intuition eauto.
  unfold possible, async_put. simpl.
  eapply elem_of_app; right.
  eapply elem_of_list_here.
Qed.

Hint Resolve is_one_of_put : core.
Hint Resolve is_one_of_latest : core.


Definition is_state_ver (s : state.t) (crashσ : gmap addr {K & bufDataT K}) : Prop :=
  is_one_of (crashσ !! A0) s.(state.b0) ∧
  is_one_of (crashσ !! A1) s.(state.b1).

Axiom source_state_is : state.t -> iProp Σ.
Global Instance source_state_timeless : Timeless (source_state_is s). Admitted.

(* XXX interesting tidbit:

  how to make sure that the value observed by a read is the latest simulated state?

  the invariant below allows the in-memory state to correspond to some pending [inmem_s]
  guys that haven't flushed yet (if they are synchronous).

  one solution is to extend the lock invariant for an object (e.g., block b0 or block b1,
  or inode in nfs server).  the lock invariant should promise that all pending changes to
  that object have been simulated.  that is, the object's part of the [state.t] satisfying
  the current [source_state_is] predicate must be equal to that object's part in every
  pending [state.t] in [inmem_s] as well.

  i.e., ∀ s' ∈ inmem_s, s'.(state.b0) = s.(state.b0)
*)

Definition is_state_always γ : iProp Σ :=
  ∃ lb (σl : async (gmap addr {K & bufDataT K})) s (inmem_s : list state.t),
    "Hsource" ∷ source_state_is s ∗
    "Hinmem_s" ∷ (
      [∗ list] s0;s1 ∈ (s :: take (length inmem_s - 1) inmem_s);inmem_s,
        source_state_is s0 ==∗ source_state_is s1
    ) ∗
    "Hdurable" ∷ own γ.(txn_walnames).(wal_heap_durable_lb) (◯ (lb : mnat)) ∗
    "Hcrash" ∷ own γ.(txn_crashstates (Σ:=Σ)) (◯ (Excl' σl)) ∗
    (* XXX not sufficient: need to make sure that s' for a later state in (possible σl)
      cannot be older than the s' of an earlier state in (possible σl). *)
    "%Hstate" ∷ ⌜ Forall (λ σ, ∃ s', s' ∈ s :: inmem_s /\ is_state_ver s' σ) (skipn lb (possible σl)) ⌝ ∗
    (* XXX should perhaps come from the txn layer *)
    "%Hlb_ok" ∷ ⌜ lb < length (possible σl) ⌝.

Global Instance is_state_always_timeless : Timeless (is_state_always γ). Admitted.
(* XXX how to make the fupd's in Hinmem_s timeless? *)

Definition is_state (l : loc) γ : iProp Σ :=
  "#Histxn" ∷ is_txn l γ ∗
  "#Hstateinv" ∷ inv kvN (is_state_always γ).


Inductive op :=
| Write0async : {K & bufDataT K} -> op
| Write0sync : {K & bufDataT K} -> op
| Read0 : op.

Axiom pending_op : nat -> op -> iProp Σ.
Axiom done_op : nat -> {K & bufDataT K} -> iProp Σ.

Theorem pending_write_0_async_exec s j v :
  source_state_is s ∗ pending_op j (Write0async v) ==∗
  source_state_is (set state.b0 (λ v0, async_put v v0) s) ∗ done_op j v.
Admitted.

Theorem pending_write_0_sync_exec s j v :
  source_state_is s ∗ pending_op j (Write0sync v) ==∗
  source_state_is (set state.b0 (λ _, sync v) s) ∗ done_op j v.
Admitted.

Theorem pending_read_0_exec s j :
  source_state_is s ∗ pending_op j Read0 ==∗
  source_state_is s ∗ done_op j (latest s.(state.b0)).
Admitted.


Example write_0_async j (v : {K & bufDataT K}) l γ :
  let mt := <[A0 := v]> (∅ : gmap addr {K & bufDataT K}) in
  is_state l γ -∗
  pending_op j (Write0async v) -∗
  ( |={⊤ ∖ ↑walN ∖ ↑invN, ⊤ ∖ ↑walN ∖ ↑invN ∖ ↑kvN}=>
      ∃ (σl : async (gmap addr {K & bufDataT K})),
        "Hcrashstates_frag" ∷ own γ.(txn_crashstates) (◯ (Excl' σl)) ∗
        "Hcrashstates_fupd" ∷ (
          let σ := mt ∪ latest σl in
          own γ.(txn_crashstates) (◯ (Excl' (async_put σ σl)))
          ={⊤ ∖ ↑walN ∖ ↑invN ∖ ↑kvN, ⊤ ∖ ↑walN ∖ ↑invN}=∗ done_op j v )).
Proof.
  iIntros (mt) "#Hs Hop".
  iNamed "Hs".
  iInv kvN as ">Hkv" "Hkvclose"; eauto.
  iNamed "Hkv".
  iModIntro.
  iExists _. iFrame.
  iIntros "Hcrash".
  iMod (pending_write_0_async_exec with "[$Hsource $Hop]") as "[Hsource Hop]".
  iMod ("Hkvclose" with "[Hsource Hdurable Hcrash]") as "Hkvclose".
  {
    iNext. iExists _, _, _. iFrame.
    iPureIntro. subst mt.

    unfold possible in *. rewrite -> app_length in *. simpl in *.
    rewrite -> drop_app_le in Hstate by lia.
    apply Forall_app in Hstate as Hstate'; destruct Hstate' as [Hpending Hlatest].

    rewrite /async_put /possible /=.
    rewrite app_length. simpl. split; last by lia.

    rewrite -> drop_app_le by len.
    rewrite -> drop_app_le by len.

    apply Forall_app; split.
    {
      eapply Forall_impl; eauto.
      intros σ [Hσ0 Hσ1].
      destruct s; simpl in *.
      rewrite /set /=.
      split; eauto.
      simpl.
      eapply is_one_of_put; eauto.
    }

    inversion Hlatest; subst.
    eapply Forall_cons; split; last by eauto.
    destruct H1. unfold set. destruct s; simpl in *.
    split; simpl.
    { erewrite lookup_union_Some_l.
      2: rewrite lookup_insert; eauto.
      eapply is_one_of_latest. }
    rewrite lookup_union_r; eauto.
    rewrite -> lookup_insert_ne by eauto; apply lookup_empty.
  }

  done.
Qed.



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
  int.Z key.(specs.addrBlock) >= int.Z LogSz ∧
  int.Z key.(specs.addrBlock) < int.Z sz.

Lemma valid_key_under_sz (kvsblks : gmap specs.addr {K & defs.bufDataT K}) key sz :
  valid_key key sz -> ∃ b, kvsblks !! key = Some (existT defs.KindBlock b).
Admitted.

Definition nat_key_to_addr key : specs.addr :=
  specs.Build_addr key 0.

(*XXXway to generalize from wal/abstractions.v?*)
Definition kvpair_val (pair : (specs.addr * Slice.t)): val :=
  (#(fst pair).(specs.addrBlock), (slice_val (snd pair), #()))%V.

Theorem kvpair_val_t key data : val_ty (kvpair_val (key, data)) (struct.t KVPair).
Proof.
  repeat constructor.
  rewrite /blockT; val_ty.
Qed.

(* Links a list of kvpairs to a slice *)
Definition kvpairs_slice (slice_val: Slice.t) (ls_kvps: list kvpair.t): iProp Σ :=
  ∃ slice_kvps, is_slice slice_val (struct.t KVPair) 1 (kvpair_val <$> slice_kvps)
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
      kvsl↦[KVS :: "txn"] #l ∗
      kvsl ↦[KVS :: "sz"] #(U64 (Z.of_nat sz)) ∗
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
      ∗ pairl ↦[struct.t KVPair] (kvpair_val (pair key data))
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
      wp_apply (wp_jrnl_Begin l γDisk _ with "[Htxn]"); auto.
      iIntros (buftx γt) "Hbtxn".
      wp_let.
      wp_call.
      change (u64_instance.u64.(@word.mul 64) 4096 8) with (U64 32768).
      change (#key.(specs.addrBlock), (#0, #()))%V with (specs.addr2val (specs.Build_addr key.(specs.addrBlock) 0)).
      pose Hkey as Hkey'.

      iDestruct (big_sepM_lookup_acc (λ k b, mapsto_txn γDisk k (projT2 b)) kvsblks key (existT defs.KindBlock (defs.bufBlock blk)) HkeyLookup with "HkvsMt") as "[HkeyMt HrestMt]".
      pose ({[key := existT defs.KindBlock (defs.bufBlock blk)]} : gmap (specs.addr) ({K & defs.bufDataT K})) as keyMp.

      iMod (Op_lift buftx _ γDisk keyMp with "[Hbtxn HkeyMt]") as "[Hbtxn HkeyMt]"; iFrame; eauto.
      { iApply big_sepM_singleton; auto. }

      wp_apply (wp_Op__ReadBuf buftx γt γDisk (specs.Build_addr key.(specs.addrBlock) 0) 32768 with "[Hbtxn HkeyMt]").
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
         wp_apply (wp_Op__CommitWait buftx γt γDisk {[key := existT defs.KindBlock (defs.bufBlock blk)]} with "[Hmapsto HisBuf]").
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
