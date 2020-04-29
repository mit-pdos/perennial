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
         val: defs.bufDataT defs.KindBlock
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

Lemma valid_key_under_sz (kvsblks : gmap specs.addr {K & defs.bufDataT K}) key sz : valid_key key sz -> ∃ b, kvsblks !! key = Some b.
Admitted.

Definition nat_key_to_addr key : specs.addr :=
  specs.Build_addr key 0.

(*XXXway to generalize from wal/abstractions.v?*)
Definition kvpair_val (pair : specs.addr*Slice.t): val :=
  (#(fst pair).(specs.addrBlock), (slice_val (snd pair), #()))%V.

(* Links a list of kvpairs to a slice *)
Definition kvpairs_slice (slice_val: Slice.t) (ls_kvps: list kvpair.t): iProp Σ :=
  ∃ slice_kvps, is_slice slice_val (struct.t KVPair.S) 1 (kvpair_val <$> slice_kvps)
                         ∗ [∗ list] _ ↦ slice_kvp;ls_kvp ∈ slice_kvps;ls_kvps,
  let '(kvpair.mk key buf) := ls_kvp in ∃ blk,
      ⌜specs.is_bufData_at_off blk 0 buf⌝
      ∗ is_block (snd slice_kvp) blk
      ∗ ⌜fst slice_kvp = key⌝.

Definition kvpairs_match (pairs: list kvpair.t) γDisk : iProp Σ :=
  [∗ list] kvp ∈ pairs, let '(kvpair.mk a b) := kvp in
                        (mapsto_txn γDisk a b)%I.

Definition ptsto_kvs (kvsl: loc) (kvsblks : gmap specs.addr {K & defs.bufDataT K})
           (sz : nat) γDisk : iProp Σ :=
  ( ∃ (l : loc),
      kvsl↦[KVS.S :: "txn"] #l ∗
      kvsl ↦[KVS.S :: "sz"] #(U64 (Z.of_nat sz)) ∗
      is_txn l γDisk ∗
      ⌜(∀ n : nat, n < sz -> ∃ blk, kvsblks !! (nat_key_to_addr n) = Some blk)⌝ ∗
      [∗ map] k↦b ∈ kvsblks, mapsto_txn γDisk k (projT2 b))%I.

Definition crashed_kvs kvp_ls kvsblks γDisk : iProp Σ :=
      ([∗ map] k↦b ∈ kvsblks, mapsto_txn γDisk k (projT2 b))%I
      ∗ kvpairs_match kvp_ls γDisk.

Definition ptsto_kvpair (l: loc) (pair: kvpair.t) : iProp Σ :=
      ∃ bs blk, (l↦[KVPair.S :: "Key"] #(pair.(kvpair.key).(specs.addrBlock)) ∗
                  l ↦[KVPair.S :: "Val"] (slice_val bs) ∗ is_block bs
 blk
                  ∗ ⌜specs.is_bufData_at_off blk 0 pair.(kvpair.val)⌝)%I.

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

Theorem wpc_KVS__Get kvsl kvsblks sz γDisk key:
  {{{
       ptsto_kvs kvsl kvsblks sz γDisk
       ∗ ⌜valid_key key sz⌝
  }}}
    KVS__Get #kvsl #((key.(specs.addrBlock)))
  {{{(pairl: loc) v, RET #pairl;
     ptsto_kvs kvsl kvsblks sz γDisk ∗ ptsto_kvpair pairl (kvpair.mk key v)
  }}}.
Proof.
  iIntros (ϕ) "[Hkvs %Hkey] Hϕ".
  iDestruct "Hkvs" as (l) "[Htxnl [Hsz [Htxn [%HinKvs HkvsMt]]]]".
  pose Hkey as Hkey'.
  destruct Hkey' as [HbuildAddr [Hkaddr [Hklgsz Hsz]]].
  wp_call.
  wp_loadField.
  wp_pures.
  remember(bool_decide (int.val sz < int.val _)) as Hszcomp.
  destruct Hszcomp; wp_pures.
  - wp_apply wp_panic.
    destruct (decide_rel Z.lt (int.val sz) _); try discriminate. omega.
  - change (u64_instance.u64.(@word.add 64) (u64_instance.u64.(@word.divu 64) (u64_instance.u64.(@word.sub 64) 4096 8) 8) 2)
      with (U64 LogSz).
    remember(bool_decide (int.val _ < int.val LogSz)) as Hlgszcomp.
    destruct Hlgszcomp; wp_pures.
    * wp_apply wp_panic.
      destruct (decide_rel Z.lt _ (int.val LogSz)); try discriminate. omega.
    * wp_loadField.
      Check wp_buftxn_Begin.
      wp_apply (wp_buftxn_Begin l γDisk _ with "[Htxn]"); auto.
      iIntros (buftx γt) "Hbtxn".
      wp_let.
      wp_call.
      change (u64_instance.u64.(@word.mul 64) 4096 8) with (U64 32768).
      change (#key.(specs.addrBlock), (#0, #()))%V with (specs.addr2val (specs.Build_addr key.(specs.addrBlock) 0)).

      iMod (BufTxn_lift buftx _ γDisk kvsblks with "[Hbtxn HkvsMt]") as "[Hbtxn Hkvs]"; iFrame; eauto.

      wp_apply (wp_BufTxn__ReadBuf buftx γt γDisk (specs.Build_addr key.(specs.addrBlock) 0) 32768 with "[Hbtxn Hkvs]").
      -- iSplitL "Hbtxn"; auto.
         pose Hkey as Hkey'.
         destruct (valid_key_under_sz kvsblks key sz Hkey') as [blk HkeyLookup].
         iSplitL "Hkvs".
         { iPoseProof (big_sepM_lookup _ kvsblks key blk with "Hkvs") as "HsepM"; eauto.
           rewrite <- HbuildAddr.
           iApply "HsepM".
         iPoseProof (big_sepL_elem_of (λ k, (∃ v0, mapsto k 1 v0))%I (valid_keys sz) key Hkey' with "[Hkvs]") as "HkeyMt"; auto.
         {
           iApply (big_sepL_mono with "Hkvs").
           iIntros (k y HkeysLkup) "HkeyMt".
           iDestruct "HkeyMt" as (v0) "HkeyMt".
           iExists (existT _ v0).
           Search
           auto.
         - iSplitL "HkeyMt"; eauto.






         {
           rewrite <- (valid_key_eq_addr _ _ Hkey).
           iApply "HkeyMt".

  - iSplitL "Hbm"; auto.
    iPureIntro.
    destruct Hkey as [knat [Hknat Hkey]].
    rewrite Hknat.
    unfold abstraction.LogSz in *. simpl in *.
    admit.
    (*apply Hkey.
    Print specs.valid_addr.
    simpl. split; simpl; try word; auto.*)
  - iIntros (bptr).
    iDestruct "Hmapsto" as "[Hmaps0 Hmaps]".
    iApply "Hmapsto".
  specs.wp_BufMap__Lookup.
  wp_loadField.
  Searchabout "Begin".
  wp_pures; eauto.
  iPoseProof (wp_buftxn_Begin _ _ _ with "Htxn") as "WP_buftxn_Begin".
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
