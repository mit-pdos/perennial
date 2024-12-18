From Perennial.algebra Require Import auth_map.
From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import lang notation typing lifting.
From Perennial.goose_lang.lib Require Import map.impl list.impl list_slice.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv connman memkv.bank.


From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export
     memkv_shard_definitions memkv_shard_start_proof memkv_shard_make_proof memkv_shard_ghost_init.
From Perennial.program_proof.memkv Require Export
     memkv_coord_definitions memkv_coord_start_proof memkv_coord_make_proof memkv_coord_ghost_init.
From Perennial.program_proof.memkv Require Export memkv_clerk_proof bank_proof.

From Perennial.goose_lang Require adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require grove_ffi.adequacy.

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

Import goose_lang.adequacy dist_adequacy grove_ffi.adequacy.

Definition shardΣ := #[heapΣ; kvMapΣ; erpcΣ; urpcregΣ].

Lemma shard_coord_boot (shardId coordId : chan) σshard σcoord σclient (g : goose_lang.global_state) :
  shardId ≠ coordId →
  ffi_initgP g.(global_world) →
  ffi_initP σshard.(world) g.(global_world) →
  ffi_initP σcoord.(world) g.(global_world) →
  ffi_initP σclient.(world) g.(global_world) →
  g.(global_world).(grove_net) !! shardId = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! coordId = Some (∅ : gset message) →
  dist_adequate_failstop [(shard_boot shardId, σshard);
                          (coord_boot coordId shardId, σcoord);
                          (client_boot coordId, σclient)] g (λ _, True).
Proof.
  intros Hneq Hinitg Hinitshard Hinitcoord Hinitclient Hlookup1 Hlookup2.
  eapply (grove_ffi_dist_adequacy_failstop (shardΣ)).
  { assumption. }
  { repeat constructor; naive_solver. }
  intros Hheap.
  iIntros "Hchan".

  (* Init the channel inv for the shard server *)
  iDestruct (big_sepM_delete with "Hchan") as "(Hshard_chan&Hrest)"; first eapply Hlookup1.
  remember (uNSHARD) as uNSHARD' eqn:Heq_unSHARD'.
  iMod (kvptsto_init uNSHARD') as (γkv) "(Hserver_shards&Hclients_ptstos)"; first done.
  iMod (shard_server_ghost_init shardId γkv with "[$Hshard_chan]")
    as (γ Heq_kv) "(#Hdom&#Hsrv&Herpc_ghost)".

  (* Init the channel inv for the shard server *)
  iDestruct (big_sepM_delete with "Hrest") as "(Hcoord_chan&_)".
  { rewrite lookup_delete_ne; first eapply Hlookup2; eauto. }
  iMod (coord_server_ghost_init coordId γkv with "[$Hcoord_chan]")
    as (γ' Heq_kv') "(#Hdom'&#Hsrv')".

  iModIntro.
  iSplitR ""; last first.
  { iMod (fupd_mask_subseteq ∅); eauto. }
  simpl. iSplitL "Hserver_shards Herpc_ghost".
  {
    iIntros (HL) "_ _".
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)

    iModIntro. iExists (λ _, True%I).
    rewrite /shard_boot. simpl.
    wp_bind (MakeKVShardServer #true).
    wp_apply (wp_MakeKVShardServer with "[Hserver_shards $Herpc_ghost]").
    { rewrite -Heq_unSHARD' Heq_kv. done. }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVShardServer__Start with "[] [] [$His_server]").
    { iExactEq "Hdom". rewrite //=. f_equal. set_solver. }
    { done. }
    eauto.
  }
  iSplitR "Hclients_ptstos".
  {
    iIntros (HL) "_ _".
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    iModIntro. iExists (λ _, True%I).
    rewrite /coord_boot. simpl.
    wp_bind (MakeKVCoordServer #(shardId : u64)).
    wp_apply (wp_MakeKVCoordServer with "[]").
    { iSplitL ""; last first.
      { rewrite /named. iExactEq "Hsrv".
        f_equal.  }
      { iPureIntro. rewrite Heq_kv; symmetry; eauto. }
    }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVCoordServer__Start with "[] [] [His_server]").
    { iExactEq "Hdom'". rewrite //=. f_equal. set_solver. }
    { done. }
    { iFrame "His_server". }
    eauto.
  }
  iSplitR ""; last eauto.
  {
    iIntros (HL) "_ _".
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    iModIntro. iExists (λ _, True%I).
    rewrite /client_boot. iEval simpl.
    wp_apply wp_MakeConnMan.
    iIntros (cm) "Hcm".
    wp_apply (wp_MakeKVClerk with "[] Hcm").
    { done. }
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
  BankClerk__SimpleTransfer "ck".

Definition auditor_boot (lockcoord kvcoord : u64) (init acc1 acc2 : u64)  : expr :=
  let: "cm" := MakeConnMan #() in
  let: "ck" := MakeBankClerk #lockcoord #kvcoord "cm" #init #acc1 #acc2 #0 in
  BankClerk__SimpleAudit "ck".

Import goose_lang.adequacy dist_adequacy grove_ffi.adequacy.

Definition shardΣ := #[heapΣ; kvMapΣ; erpcΣ; urpcregΣ; mapΣ u64 u64].

Definition lockshardId := W64 0.
Definition lockcoordId := W64 1.
Definition kvshardId := W64 2.
Definition kvcoordId := W64 3.

Definition init := W64 0.
Definition acc1 := W64 1.
Definition acc2 := W64 2.

Lemma bank_boot σlockshard σlockcoord σkvshard σkvcoord σclient (g : goose_lang.global_state) :
  ffi_initgP g.(global_world) →
  ffi_initP σlockshard.(world) g.(global_world) →
  ffi_initP σlockcoord.(world) g.(global_world) →
  ffi_initP σkvshard.(world) g.(global_world) →
  ffi_initP σkvcoord.(world) g.(global_world) →
  ffi_initP σclient.(world) g.(global_world) →
  g.(global_world).(grove_net) !! lockshardId = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! lockcoordId = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! kvshardId = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! kvcoordId = Some (∅ : gset message) →
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
  { simpl. repeat constructor; naive_solver. }
  intros Hheap.
  iIntros "Hchan".

  (* Init the channel inv for the lock shard server *)
  iDestruct (big_sepM_delete with "Hchan") as "(Hlockshard_chan&Hrest)"; first eapply Hlookup1.
  remember (uNSHARD) as uNSHARD' eqn:Heq_unSHARD'.
  iMod (kvptsto_init uNSHARD') as (γlk) "(Hserver_lockshards&Hclients_lockptstos)"; first done.
  iMod (shard_server_ghost_init lockshardId γlk with "[$Hlockshard_chan]")
    as (γlk_shard Heq_lockshard) "(#Hdom&#Hsrv&Herpc_ghost)".

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
    as (γkv_shard Heq_kvshard) "(#Hdom''&#Hsrv_kv&Herpc_ghost_kv)".

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
  iMod (lock_alloc lockN ⊤ _ init (init_lock_inv init _ _ {[acc1; acc2]}) with
            "[$] [Hinit Hacc1 Hacc2 Hacc1_lock Hacc2_lock]") as "#His_lock".
  { iLeft. iFrame "Hinit".
    iApply big_sepS_elements.
    rewrite elements_disj_union; last by set_solver.
    rewrite ?elements_singleton //.
    iFrame. rewrite big_sepL_nil. done.
  }

  iSplitR ""; last first.
  { iModIntro. iMod (fupd_mask_subseteq ∅); eauto. }

  iModIntro.

  (* lockserver shard *)
  simpl. iSplitL "Hserver_lockshards Herpc_ghost".
  {
    iIntros (HL) "_ _".
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    iModIntro. iExists (λ _, True%I).
    rewrite /shard_boot. simpl.
    wp_bind (MakeKVShardServer #true).
    wp_apply (wp_MakeKVShardServer with "[Hserver_lockshards $Herpc_ghost]").
    { rewrite -Heq_unSHARD' Heq_lockshard. done. }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVShardServer__Start with "[] [] [$His_server]").
    { iExactEq "Hdom". rewrite //=. f_equal. set_solver. }
    { done. }
    eauto.
  }

  (* lockserver coordinator *)
  iSplitL "".
  {
    iIntros (HL) "_ _".
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    iModIntro. iExists (λ _, True%I).
    rewrite /coord_boot. simpl.
    wp_bind (MakeKVCoordServer #(lockshardId : u64)).
    wp_apply (wp_MakeKVCoordServer with "[]").
    { iSplitL ""; last first.
      { rewrite /named. done. }
      { iPureIntro. rewrite Heq_lockshard; symmetry; eauto. }
    }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVCoordServer__Start with "[] [] [His_server]").
    { iExactEq "Hdom'". rewrite //=. f_equal. set_solver. }
    { iExact "Hsrv'". }
    { iFrame "His_server". }
    eauto.
  }

  (* kv shard *)
  iSplitL "Hserver_kvshards Herpc_ghost_kv".
  {
    iIntros (HL) "_ _".
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    iModIntro. iExists (λ _, True%I).
    rewrite /shard_boot. simpl.
    wp_bind (MakeKVShardServer #true).
    wp_apply (wp_MakeKVShardServer with "[Hserver_kvshards $Herpc_ghost_kv]").
    { rewrite -Heq_unSHARD' Heq_kvshard. done. }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVShardServer__Start with "[] [] [$His_server]").
    { iExactEq "Hdom''". rewrite //=. f_equal. set_solver. }
    { iExact "Hsrv_kv". }
    eauto.
  }

  (* kv coordinator *)
  iSplitL "".
  {
    iIntros (HL) "_ _".
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    iModIntro. iExists (λ _, True%I).
    rewrite /coord_boot. simpl.
    wp_bind (MakeKVCoordServer #(kvshardId : u64)).
    wp_apply (wp_MakeKVCoordServer with "[]").
    { iSplitL ""; last first.
      { rewrite /named. iExact "Hsrv_kv". }
      { iPureIntro. rewrite Heq_kvshard; symmetry; eauto. }
    }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVCoordServer__Start with "[] [] [His_server]").
    { iExactEq "Hdom'''". rewrite //=. f_equal. set_solver. }
    { iExact "Hsrv''". }
    { iFrame "His_server". }
    eauto.
  }

  iSplitR "".
  {
    iIntros (HL) "_ _".
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    iModIntro. iExists (λ _, True%I).
    rewrite /transferrer_boot. iEval simpl.
    wp_apply wp_MakeConnMan.
    iIntros (cm) "Hcm".
    wp_pures.
    wp_apply (wp_MakeBankClerk with "[Hcm]").
    { iFrame. iFrame "Hsrv'' Hsrv'".
      rewrite Heq_lockcoord Heq_kvcoord. iFrame "#". done. }
    iIntros (??) "(?&?)". wp_pures.
    wp_apply (Bank__SimpleTransfer_spec with "[$]").
    eauto.
  }

  iSplitR "".
  {
    iIntros (HL) "_ _".
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    iModIntro. iExists (λ _, True%I).
    rewrite /auditor_boot. iEval simpl.
    wp_apply wp_MakeConnMan.
    iIntros (cm) "Hcm".
    wp_pures.
    wp_apply (wp_MakeBankClerk with "[Hcm]").
    { iFrame. iFrame "Hsrv'' Hsrv'".
      rewrite Heq_lockcoord Heq_kvcoord. iFrame "#". done. }
    iIntros (??) "(?&?)". wp_pures.
    wp_apply (Bank__SimpleAudit_spec with "[$]").
    eauto.
  }
  eauto.
Qed.

End closed2.
