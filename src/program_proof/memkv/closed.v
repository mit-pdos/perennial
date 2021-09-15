From Perennial.algebra Require Import auth_map.
From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import lang notation typing lifting.
From Perennial.goose_lang.lib Require Import map.impl list.impl list_slice.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv connman bank.


From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export
     memkv_shard_definitions memkv_shard_start_proof memkv_shard_make_proof memkv_shard_ghost_init.
From Perennial.program_proof.memkv Require Export
     memkv_coord_definitions memkv_coord_start_proof memkv_coord_make_proof memkv_coord_ghost_init.
From Perennial.program_proof.memkv Require Export memkv_clerk_proof bank_proof.

From Perennial.goose_lang Require adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require grove_ffi_adequacy.

Module closed1.

Definition shard_boot (host : u64) : expr :=
  let: "s" := MakeKVShardServer #true in
  KVShardServer__Start "s" #host.

Definition coord_boot (host : u64) (init : u64) : expr :=
  let: "s" := MakeKVCoordServer #init in
  KVCoord__Start "s" #host.

Definition client_boot (coord : u64) : expr :=
  let: "cm" := MakeConnMan #() in
  MakeKVClerk #coord "cm".

Import adequacy dist_adequacy grove_ffi_adequacy.

Definition shardΣ := #[heapΣ; kvMapΣ; rpcΣ ShardReplyC; rpcregΣ].

(* TODO: move *)
Lemma heapG_heap_globalG_roundtrip {Σ} Hheap Hcrash local_names :
  Hheap =
  @heapG_heap_globalG Σ
    (@dist_heapGS_heapGS grove_op grove_model grove_semantics grove_interp grove_interp_adequacy Σ Hheap
       Hcrash local_names).
Proof.
  rewrite /heapG_heap_globalG. rewrite /dist_heapGS_heapGS //=.
  destruct Hheap => //=. f_equal.
  * destruct dist_heapGpreS => //= . f_equal.
    { destruct heap_preG_iris => //=. }
    { destruct heap_preG_crash => //=. }
    { destruct heap_preG_heap => //=. }
    { destruct heap_preG_ffi => //=. }
    { destruct heap_preG_trace => //=. }
    { destruct heap_preG_credit => //=. }
  * rewrite gen_heapG_update_pre_get //=.
  * rewrite /inv_get_names //=.
    destruct dist_heapGS_inv_names => //=.
Qed.

Lemma shard_coord_boot (shardId coordId : chan) σshard σcoord σclient (g : ffi_global_state) :
  shardId ≠ coordId →
  ffi_initgP g →
  ffi_initP σshard.(world) g →
  ffi_initP σcoord.(world) g →
  ffi_initP σclient.(world) g →
  (g : gmap chan (gset message)) !! shardId = Some (∅ : gset message) →
  (g : gmap chan (gset message)) !! coordId = Some (∅ : gset message) →
  dist_adequate_failstop [(shard_boot shardId, σshard);
                          (coord_boot coordId shardId, σcoord);
                          (client_boot coordId, σclient)] g (λ _, True).
Proof.
  intros Hneq Hinitg Hinitshard Hinitcoord Hinitclient Hlookup1 Hlookup2.
  eapply (grove_ffi_dist_adequacy_failstop (shardΣ)).
  { assumption. }
  intros Hheap.
  iIntros "Hchan".

  (* Init the channel inv for the shard server *)
  iDestruct (big_sepM_delete with "Hchan") as "(Hshard_chan&Hrest)"; first eapply Hlookup1.
  remember (uNSHARD) as uNSHARD' eqn:Heq_unSHARD'.
  iMod (kvptsto_init uNSHARD') as (γkv) "(Hserver_shards&Hclients_ptstos)"; first done.
  iMod (shard_server_ghost_init shardId γkv with "[$Hshard_chan]")
    as (γ Heq_kv) "(#Hdom&#Hsrv&Hsrv_rpc_ghost&Hsrv_cid)".

  (* Init the channel inv for the shard server *)
  iDestruct (big_sepM_delete with "Hrest") as "(Hcoord_chan&_)".
  { rewrite lookup_delete_ne; first eapply Hlookup2; eauto. }
  iMod (coord_server_ghost_init coordId γkv with "[$Hcoord_chan]")
    as (γ' Heq_kv') "(#Hdom'&#Hsrv')".

  iModIntro.
  iSplitR ""; last first.
  { iMod (fupd_mask_subseteq ∅); eauto. }
  iSplitL "Hserver_shards Hsrv_rpc_ghost Hsrv_cid".
  {
    iIntros (Hcrash local_names).
    iModIntro. iExists (λ _, True%I).
    rewrite /shard_boot. simpl.
    wp_bind (MakeKVShardServer #true).
    wp_apply (wp_MakeKVShardServer with "[Hsrv_cid Hserver_shards Hsrv_rpc_ghost]").
    { iSplitL "".
      { rewrite is_shard_server_unfold. iNamed "Hsrv". iFrame "#". }
      iClear "Hsrv". iFrame "Hsrv_rpc_ghost".
      rewrite -Heq_unSHARD' Heq_kv. iFrame "Hserver_shards".
      eauto. }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVShardServer__Start with "[] [] [$His_server]").
    { iExactEq "Hdom". rewrite //=. f_equal. set_solver. }
    { iExactEq "Hsrv". f_equal. apply heapG_heap_globalG_roundtrip. }
    eauto.
  }
  iSplitR "Hclients_ptstos".
  {
    iIntros (Hcrash local_names).
    iModIntro. iExists (λ _, True%I).
    rewrite /coord_boot. simpl.
    wp_bind (MakeKVCoordServer #(shardId : u64)).
    wp_apply (wp_MakeKVCoordServer with "[]").
    { iSplitL ""; last first.
      { rewrite /named. iExactEq "Hsrv".
        f_equal. apply heapG_heap_globalG_roundtrip. }
      { iPureIntro. rewrite Heq_kv; symmetry; eauto. }
    }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVCoordServer__Start with "[] [] [His_server]").
    { iExactEq "Hdom'". rewrite //=. f_equal. set_solver. }
    { iExactEq "Hsrv'". rewrite -heapG_heap_globalG_roundtrip. eauto. }
    { iFrame "His_server". }
    eauto.
  }
  iSplitR ""; last eauto.
  {
    iIntros (Hcrash local_names).
    iModIntro. iExists (λ _, True%I).
    rewrite /client_boot. iEval simpl.
    wp_apply wp_MakeConnMan.
    iIntros (cm) "Hcm".
    wp_apply (wp_MakeKVClerk with "[] Hcm").
    {
      iExactEq "Hsrv'". rewrite -heapG_heap_globalG_roundtrip. f_equal.
    }
    eauto.
  }
Qed.

End closed1.

Module closed2.

Definition shard_boot (host : u64) : expr :=
  let: "s" := MakeKVShardServer #true in
  KVShardServer__Start "s" #host.

Definition coord_boot (host : u64) (init : u64) : expr :=
  let: "s" := MakeKVCoordServer #init in
  KVCoord__Start "s" #host.

Definition transferrer_boot (lockcoord kvcoord : u64) (init acc1 acc2 : u64)  : expr :=
  let: "cm" := MakeConnMan #() in
  let: "ck" := MakeBankClerk #lockcoord #kvcoord "cm" #init #acc1 #acc2 #0 in
  BankClerk__SimpleTransfer "ck" #1.

Definition auditor_boot (lockcoord kvcoord : u64) (init acc1 acc2 : u64)  : expr :=
  let: "cm" := MakeConnMan #() in
  let: "ck" := MakeBankClerk #lockcoord #kvcoord "cm" #init #acc1 #acc2 #0 in
  BankClerk__SimpleAudit "ck".

Import adequacy dist_adequacy grove_ffi_adequacy.

Definition shardΣ := #[heapΣ; kvMapΣ; rpcΣ ShardReplyC; rpcregΣ; mapΣ u64 u64].

(* TODO: move *)
Lemma heapG_heap_globalG_roundtrip {Σ} Hheap Hcrash local_names :
  Hheap =
  @heapG_heap_globalG Σ
    (@dist_heapGS_heapGS grove_op grove_model grove_semantics grove_interp grove_interp_adequacy Σ Hheap
       Hcrash local_names).
Proof.
  rewrite /heapG_heap_globalG. rewrite /dist_heapGS_heapGS //=.
  destruct Hheap => //=. f_equal.
  * destruct dist_heapGpreS => //= . f_equal.
    { destruct heap_preG_iris => //=. }
    { destruct heap_preG_crash => //=. }
    { destruct heap_preG_heap => //=. }
    { destruct heap_preG_ffi => //=. }
    { destruct heap_preG_trace => //=. }
    { destruct heap_preG_credit => //=. }
  * rewrite gen_heapG_update_pre_get //=.
  * rewrite /inv_get_names //=.
    destruct dist_heapGS_inv_names => //=.
Qed.

Definition lockshardId := U64 0.
Definition lockcoordId := U64 1.
Definition kvshardId := U64 2.
Definition kvcoordId := U64 3.

Definition init := U64 0.
Definition acc1 := U64 1.
Definition acc2 := U64 2.

Lemma bank_boot σlockshard σlockcoord σkvshard σkvcoord σclient (g : ffi_global_state) :
  ffi_initgP g →
  ffi_initP σlockshard.(world) g →
  ffi_initP σlockcoord.(world) g →
  ffi_initP σkvshard.(world) g →
  ffi_initP σkvcoord.(world) g →
  ffi_initP σclient.(world) g →
  (g : gmap chan (gset message)) !! lockshardId = Some (∅ : gset message) →
  (g : gmap chan (gset message)) !! lockcoordId = Some (∅ : gset message) →
  (g : gmap chan (gset message)) !! kvshardId = Some (∅ : gset message) →
  (g : gmap chan (gset message)) !! kvcoordId = Some (∅ : gset message) →
  dist_adequate_failstop [
                          (shard_boot lockshardId, σlockshard);
                          (coord_boot lockcoordId lockshardId, σlockcoord);
                          (shard_boot kvshardId, σkvshard);
                          (coord_boot kvcoordId kvshardId, σkvcoord);
                          (transferrer_boot lockcoordId kvcoordId init acc1 acc2, σclient);
                          (auditor_boot lockcoordId kvcoordId init acc1 acc2, σclient)] g (λ _, True).
Proof.
  intros Hinitg
         Hinitlockshard Hinitlockcoord
         Hinitkvshard Hinitkvcoord
         Hinitclient Hlookup1 Hlookup2 Hlookup3 Hlookup4.
  eapply (grove_ffi_dist_adequacy_failstop (shardΣ)).
  { assumption. }
  intros Hheap.
  iIntros "Hchan".

  (* Init the channel inv for the lock shard server *)
  iDestruct (big_sepM_delete with "Hchan") as "(Hlockshard_chan&Hrest)"; first eapply Hlookup1.
  remember (uNSHARD) as uNSHARD' eqn:Heq_unSHARD'.
  iMod (kvptsto_init uNSHARD') as (γlk) "(Hserver_lockshards&Hclients_lockptstos)"; first done.
  iMod (shard_server_ghost_init lockshardId γlk with "[$Hlockshard_chan]")
    as (γlk_shard Heq_lockshard) "(#Hdom&#Hsrv&Hsrv_rpc_ghost&Hsrv_cid)".

  (* Init the channel inv for the lock coord server *)
  iDestruct (big_sepM_delete with "Hrest") as "(Hlockcoord_chan&Hrest)".
  { rewrite lookup_delete_ne; first eapply Hlookup2; eauto. }
  iMod (coord_server_ghost_init lockcoordId γlk with "[$Hlockcoord_chan]")
    as (γlk_coord Heq_lockcoord) "(#Hdom'&#Hsrv')".

  (* Init the channel inv for the kv shard server *)
  iDestruct (big_sepM_delete with "Hrest") as "(Hkvshard_chan&Hrest)".
  { rewrite ?lookup_delete_ne; first eapply Hlookup3; eauto. }
  iMod (kvptsto_init uNSHARD') as (γkv) "(Hserver_kvshards&Hclients_kvptstos)"; first done.
  iMod (shard_server_ghost_init kvshardId γkv with "[$Hkvshard_chan]")
    as (γkv_shard Heq_kvshard) "(#Hdom''&#Hsrv_kv&Hsrv_kv_rpc_ghost&Hsrv_kv_cid)".

  (* Init the channel inv for the kv coord server *)
  iDestruct (big_sepM_delete with "Hrest") as "(Hkvcoord_chan&_)".
  { rewrite ?lookup_delete_ne; first eapply Hlookup4; eauto. }
  iMod (coord_server_ghost_init kvcoordId γkv with "[$Hkvcoord_chan]")
    as (γkv_coord Heq_kvcoord) "(#Hdom'''&#Hsrv'')".

  (* Initialize the lock invariant for the init flag lock *)
  (* Pull out the kv pts tos *)
  iDestruct (big_sepS_delete _ _ init with "Hclients_kvptstos") as "(Hinit&Hclients_kvptstos)".
  { apply elem_of_fin_to_set. }
  iDestruct (big_sepS_delete _ _ acc1 with "Hclients_kvptstos") as "(Hacc1&Hclients_kvptstos)".
  { set_unfold. eauto. }
  iDestruct (big_sepS_delete _ _ acc2 with "Hclients_kvptstos") as "(Hacc2&Hclients_kvptstos)".
  { set_unfold. eauto. }

  (* Pull out the lock pts tos *)
  iDestruct (big_sepS_delete _ _ init with "Hclients_lockptstos") as "(Hinit_lock&Hclients_lockptstos)".
  { apply elem_of_fin_to_set. }
  iDestruct (big_sepS_delete _ _ acc1 with "Hclients_lockptstos") as "(Hacc1_lock&Hclients_lockptstos)".
  { set_unfold. eauto. }
  iDestruct (big_sepS_delete _ _ acc2 with "Hclients_lockptstos") as "(Hacc2_lock&Hclients_lockptstos)".
  { set_unfold. eauto. }

  (* Finally alloc lock *)
  iMod (lock_alloc lockN ⊤ _ init (init_lock_inv init acc1 acc2 _ _) with
            "[$] [Hinit Hacc1 Hacc2 Hacc1_lock Hacc2_lock]") as "#His_lock".
  { iLeft. iFrame "Hinit". iFrame. }

  iSplitR ""; last first.
  { iModIntro. iMod (fupd_mask_subseteq ∅); eauto. }

  iModIntro.

  (* lockserver shard *)
  iSplitL "Hserver_lockshards Hsrv_rpc_ghost Hsrv_cid".
  {
    iIntros (Hcrash local_names).
    iModIntro. iExists (λ _, True%I).
    rewrite /shard_boot. simpl.
    wp_bind (MakeKVShardServer #true).
    wp_apply (wp_MakeKVShardServer with "[Hsrv_cid Hserver_lockshards Hsrv_rpc_ghost]").
    { iSplitL "".
      { rewrite is_shard_server_unfold. iNamed "Hsrv". iFrame "#". }
      iClear "Hsrv". iFrame "Hsrv_rpc_ghost".
      rewrite -Heq_unSHARD' Heq_lockshard. iFrame "Hserver_lockshards".
      eauto. }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVShardServer__Start with "[] [] [$His_server]").
    { iExactEq "Hdom". rewrite //=. f_equal. set_solver. }
    { iExactEq "Hsrv". f_equal. apply heapG_heap_globalG_roundtrip. }
    eauto.
  }

  (* lockserver coordinator *)
  iSplitL "".
  {
    iIntros (Hcrash local_names).
    iModIntro. iExists (λ _, True%I).
    rewrite /coord_boot. simpl.
    wp_bind (MakeKVCoordServer #(lockshardId : u64)).
    wp_apply (wp_MakeKVCoordServer with "[]").
    { iSplitL ""; last first.
      { rewrite /named. iExactEq "Hsrv".
        f_equal. apply heapG_heap_globalG_roundtrip. }
      { iPureIntro. rewrite Heq_lockshard; symmetry; eauto. }
    }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVCoordServer__Start with "[] [] [His_server]").
    { iExactEq "Hdom'". rewrite //=. f_equal. set_solver. }
    { iExactEq "Hsrv'". rewrite -heapG_heap_globalG_roundtrip. eauto. }
    { iFrame "His_server". }
    eauto.
  }

  (* kv shard *)
  iSplitL "Hserver_kvshards Hsrv_kv_rpc_ghost Hsrv_kv_cid".
  {
    iIntros (Hcrash local_names).
    iModIntro. iExists (λ _, True%I).
    rewrite /shard_boot. simpl.
    wp_bind (MakeKVShardServer #true).
    wp_apply (wp_MakeKVShardServer with "[Hsrv_kv_cid Hserver_kvshards Hsrv_kv_rpc_ghost]").
    { iSplitL "".
      { iEval (rewrite is_shard_server_unfold) in "Hsrv_kv". iNamed "Hsrv_kv". iFrame "#". }
      iClear "Hsrv". iFrame "Hsrv_kv_rpc_ghost".
      rewrite -Heq_unSHARD' Heq_kvshard. iFrame "Hserver_kvshards".
      eauto. }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVShardServer__Start with "[] [] [$His_server]").
    { iExactEq "Hdom''". rewrite //=. f_equal. set_solver. }
    { iExactEq "Hsrv_kv". f_equal. apply heapG_heap_globalG_roundtrip. }
    eauto.
  }

  (* kv coordinator *)
  iSplitL "".
  {
    iIntros (Hcrash local_names).
    iModIntro. iExists (λ _, True%I).
    rewrite /coord_boot. simpl.
    wp_bind (MakeKVCoordServer #(kvshardId : u64)).
    wp_apply (wp_MakeKVCoordServer with "[]").
    { iSplitL ""; last first.
      { rewrite /named. iExactEq "Hsrv_kv".
        f_equal. apply heapG_heap_globalG_roundtrip. }
      { iPureIntro. rewrite Heq_kvshard; symmetry; eauto. }
    }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVCoordServer__Start with "[] [] [His_server]").
    { iExactEq "Hdom'''". rewrite //=. f_equal. set_solver. }
    { iExactEq "Hsrv''". rewrite -heapG_heap_globalG_roundtrip. eauto. }
    { iFrame "His_server". }
    eauto.
  }

  iSplitR "".
  {
    iIntros (Hcrash local_names).
    iModIntro. iExists (λ _, True%I).
    rewrite /transferrer_boot. iEval simpl.
    wp_apply wp_MakeConnMan.
    iIntros (cm) "Hcm".
    wp_pures.
    wp_apply (wp_MakeBankClerk with "[Hcm]").
    { eauto. }
    {
      iSplitL "".
      { iExactEq "Hsrv'". rewrite -heapG_heap_globalG_roundtrip. f_equal. }
      iSplitL "".
      { iExactEq "Hsrv''". rewrite -heapG_heap_globalG_roundtrip. f_equal. }
      iFrame "Hcm". iExactEq "His_lock".
      rewrite Heq_kvcoord Heq_lockcoord; auto.
    }
    iIntros (??) "(?&?)". wp_pures.
    wp_apply (Bank__SimpleTransfer_spec with "[$]").
    eauto.
  }

  iSplitR "".
  {
    iIntros (Hcrash local_names).
    iModIntro. iExists (λ _, True%I).
    rewrite /auditor_boot. iEval simpl.
    wp_apply wp_MakeConnMan.
    iIntros (cm) "Hcm".
    wp_pures.
    wp_apply (wp_MakeBankClerk with "[Hcm]").
    { eauto. }
    {
      iSplitL "".
      { iExactEq "Hsrv'". rewrite -heapG_heap_globalG_roundtrip. f_equal. }
      iSplitL "".
      { iExactEq "Hsrv''". rewrite -heapG_heap_globalG_roundtrip. f_equal. }
      iFrame "Hcm". iExactEq "His_lock".
      rewrite Heq_kvcoord Heq_lockcoord; auto.
    }
    iIntros (??) "(?&?)". wp_pures.
    wp_apply (Bank__SimpleAudit_spec with "[$]").
    eauto.
  }
  eauto.
Qed.

End closed2.
