From Perennial.Helpers Require Import ModArith.
From Goose.github_com.mit_pdos.gokv Require Import connman.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.algebra Require Import auth_map.
From Perennial.program_proof.memkv Require Import rpc_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section connman_proof.

Context `{!rpcregG Σ}.
Context `{hG: !heapGS Σ}.
Definition connmanN := nroot .@ "connman".
Definition own_ConnMan (c_ptr:loc) (lock: val) : iProp Σ :=
  ∃ (rpcCls making:loc) (rpcClsM makingM:gmap u64 loc),
    "HrpcCls" ∷ c_ptr ↦[ConnMan :: "rpcCls"] #rpcCls ∗
    "Hmaking" ∷ c_ptr ↦[ConnMan :: "making"] #making ∗
    "Hcls_map" ∷ is_map rpcCls 1 rpcClsM ∗
    "Hmaking_map" ∷ is_map making 1 makingM ∗
    "#HownRpcCls" ∷ ([∗ map] host ↦ cl ∈ rpcClsM, RPCClient_own cl host) ∗
    "#HownMaking" ∷ ([∗ map] host ↦ c ∈ makingM, is_cond c lock)
.

Definition is_ConnMan (c_ptr:loc) : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (c_ptr ↦[ConnMan :: "mu"] mu) ∗
  "#Hinv" ∷ is_lock connmanN mu (own_ConnMan c_ptr mu)
.

Lemma wp_MakeConnMan :
  {{{ True }}}
    MakeConnMan #()
  {{{ (c_ptr:loc), RET #c_ptr; is_ConnMan c_ptr }}}.
Proof.
  iIntros "%Φ _ HΦ".
  wp_lam. (* FIXME this unfolds zero_val and NewMap... *)
  wp_apply wp_allocStruct. { val_ty. }
  iIntros (c_ptr) "Hc".
  iDestruct (struct_fields_split with "Hc") as "HH".
  iNamed "HH".
  wp_apply wp_new_free_lock.
  iIntros (mu) "Hfreelock".
  wp_storeField.
  replace (ref (InjLV #null))%E with (NewMap (struct.ptrT rpc.RPCClient)) at 2 by naive_solver.
  wp_apply (wp_NewMap).
  iIntros (rpcCls) "HrpcCls".
  wp_storeField.
  replace (ref (InjLV #null))%E with (NewMap condvarRefT) at 1 by naive_solver.
  wp_apply (wp_NewMap).
  iIntros (making) "Hmaking".
  wp_storeField.
  iApply "HΦ".
  iExists #mu.
  iMod (readonly_alloc_1 with "mu") as "$".
  iMod (alloc_lock with "Hfreelock [-]") as "$"; last done.
  rewrite /own_ConnMan. iModIntro. iExists rpcCls, making, _, _.
  iFrame. by rewrite !big_sepM_empty.
Qed.

Local Lemma wp_ConnMan__getClient (c_ptr:loc) (host:u64) :
  is_ConnMan c_ptr -∗
  {{{ True }}}
    ConnMan__getClient #c_ptr #host
  {{{
    (cl_ptr:loc), RET #cl_ptr; RPCClient_own cl_ptr host
  }}}.
Proof.
  iIntros "#Hconn !# %Φ _ HΦ".
  iNamed "Hconn".
  Opaque rpc.RPCClient.
  Opaque zero_val.
  wp_lam. wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (cl_ptr) "Hcl_ptr".
  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "Hinv").
  iIntros "[Hlocked Hown]".
  wp_pures.
  wp_apply (wp_forBreak' with "[-]").
  { iNamedAccu. }
  iIntros "!> H". iNamed "H". wp_pures.
  iNamed "Hown".
  (* Inside the loop body *)
  wp_loadField.
  wp_apply (wp_MapGet with "Hcls_map").
  iIntros (cl1 ok1) "[%Hcl1 Hcls_map]".
  wp_pures.
  destruct ok1.
  { apply map_get_true in Hcl1.
    wp_pures.
    wp_store.
    wp_pures.
    iModIntro. iRight. iSplitR; first done.
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[$Hinv $Hlocked HrpcCls Hmaking Hmaking_map Hcls_map]").
    { rewrite /own_ConnMan. eauto 10 with iFrame. }
    wp_pures.
    wp_load.
    iApply "HΦ".
    iDestruct (big_sepM_lookup with "HownRpcCls") as "$"; done. }
  apply map_get_false in Hcl1.
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapGet with "Hmaking_map").
  iIntros (mk2 ok2) "[%Hmk2 Hmaking_map]".
  wp_pures.
  destruct ok2.
  { apply map_get_true in Hmk2.
    wp_pures.
    iDestruct (big_sepM_lookup with "HownMaking") as "Hcond"; first done.
    wp_apply (wp_condWait with "[$Hinv $Hcond $Hlocked HrpcCls Hmaking Hmaking_map Hcls_map]").
    { rewrite /own_ConnMan. eauto 10 with iFrame. }
    iIntros "[Hlocked Hown]".
    wp_pures.
    iModIntro. iLeft. iSplitR; first done.
    iFrame. }
  apply map_get_false in Hmk2.
  wp_pures.
  wp_loadField.
  wp_apply (wp_newCond with "Hinv").
  iIntros (cond) "#Hcond".
  wp_loadField.
  wp_apply (wp_MapInsert _ _ _ _ cond with "Hmaking_map"); first done.
  iIntros "Hmaking_map".
  wp_pures.
  iDestruct (big_sepM_insert_2 with "[Hcond] HownMaking") as "{HownMaking} #HownMaking".
  { done. }
  wp_loadField.
  wp_apply (release_spec with "[$Hinv $Hlocked HrpcCls Hmaking Hmaking_map Hcls_map]").
  { rewrite /own_ConnMan. eauto 10 with iFrame. }
  wp_pures.
  wp_apply wp_MakeRPCClient.
  iIntros (cl_new) "#Hcl_new".
  wp_store.
  wp_loadField.
  wp_apply (acquire_spec with "Hinv").
  iIntros "[Hlocked Hown]".
  iClear "HownRpcCls HownMaking". clear rpcCls making rpcClsM makingM cl1 mk2 Hcl1 Hmk2.
  wp_pures.
  iNamed "Hown".
  wp_load.
  wp_loadField.
  wp_apply (wp_MapInsert _ _ _ _ cl_new with "Hcls_map"); first done.
  iIntros "Hcls_map".
  iDestruct (big_sepM_insert_2 with "[Hcl_new] HownRpcCls") as "{HownRpcCls} #HownRpcCls".
  { done. }
  wp_pures.
  wp_apply (wp_condBroadcast with "Hcond").
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapDelete with "Hmaking_map"). iIntros "Hmaking_map".
  iDestruct (big_sepM_subseteq _ _ (map_del makingM host) with "HownMaking") as "{HownMaking} HownMaking".
  { apply: delete_subseteq. }
  wp_pures.
  iModIntro. iRight. iSplitR; first done.
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[$Hinv $Hlocked HrpcCls Hmaking Hmaking_map Hcls_map]").
  { rewrite /own_ConnMan. eauto 10 with iFrame. }
  wp_load.
  iApply "HΦ". done.
Qed.

Lemma wp_ConnMan__CallAtLeastOnce {X:Type} (x:X) γsmap (c_ptr:loc) (rpcid:u64) (host:u64) req rep_out_ptr
      (timeout_ms : u64) dummy_sl_val (reqData:list u8) Pre Post :
  is_ConnMan c_ptr -∗
  handler_is γsmap X host rpcid Pre Post -∗
  □(▷ Pre x reqData) -∗
  {{{
      is_slice req byteT 1 reqData ∗
      rep_out_ptr ↦[slice.T byteT] dummy_sl_val
  }}}
      ConnMan__CallAtLeastOnce #c_ptr #host #rpcid (slice_val req) #rep_out_ptr #timeout_ms
    {{{
      RET #();
      is_slice req byteT 1 reqData ∗
      ∃ rep_sl (repData:list u8),
        rep_out_ptr ↦[slice.T byteT] (slice_val rep_sl) ∗
        typed_slice.is_slice rep_sl byteT 1 repData ∗
        (▷ Post x reqData repData)
    }}}
    .
Proof.
  iIntros "#Hconn #Hhandler #Hpre !#" (Φ) "H HΦ".
  iDestruct "H" as "(Hslice & Hrep)".
  Opaque rpc.RPCClient.
  Opaque zero_val.
  wp_lam.
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (cl_ptr) "Hcl_ptr".
  wp_pures.
  wp_apply (wp_ConnMan__getClient with "Hconn").
  iIntros (cl) "Hcl".
  wp_store.
  iAssert (∃ cl : loc, cl_ptr ↦[refT (struct.t rpc.RPCClient)] #cl ∗ RPCClient_own cl host)%I with "[Hcl Hcl_ptr]" as "Hcl".
  { eauto with iFrame. }
  clear cl.
  wp_pures.
  wp_apply (wp_forBreak' with "[-]").
  { iNamedAccu. }
  iIntros "!> H". iNamed "H". wp_pures.
  (* Inside loop body *)
  iPoseProof "Hconn" as "Hconn2".
  iNamed "Hconn2".
  iDestruct "Hcl" as (cl) "[Hcl_ptr #Hcl]".
  wp_load.
  wp_apply (wp_RPCClient__Call with "[$Hslice $Hrep $Hhandler $Hcl Hpre]").
  { done. }
  iIntros (err).
  iIntros "(_ & Hslice & Hrep)".
  wp_pures.
  destruct err as [|].
  {
    wp_pures.
    destruct c.
    { (* ErrTimeout *)
      wp_pures.
      iModIntro.
      iLeft.
      iSplitR; first done.
      eauto with iFrame.
    }
    { (* ErrDisconnected *)
      wp_pures.
      wp_loadField.
      wp_apply (acquire_spec with "Hinv").
      iIntros "[Hlocked Hown]".
      iClear "Hcl".
      iNamed "Hown".
      wp_pures.
      wp_load.
      wp_loadField.
      wp_apply (wp_MapGet with "Hcls_map").
      iIntros (cl2 ok2) "[%Hcl2 Hcls_map]".
      wp_apply (wp_If_join_evar with "[HrpcCls Hcls_map]").
      { iIntros (succ Hsucc).
        case_bool_decide as Heq; wp_pures.
        - wp_loadField.
          wp_apply (wp_MapDelete with "Hcls_map").
          iIntros "Hcls_map".
          wp_pures. iModIntro. iSplitR; first done.
          replace (map_del rpcClsM host) with
            (if succ then (map_del rpcClsM host) else rpcClsM); last by rewrite Hsucc.
          iNamedAccu.
        - iModIntro. iSplitR; first done.
          rewrite Hsucc. iFrame. }
      iIntros "H". iNamed "H". wp_pures.
      wp_loadField.
      wp_apply (release_spec with "[$Hinv $Hlocked HrpcCls Hmaking Hmaking_map Hcls_map]").
      { rewrite /own_ConnMan. iModIntro. do 4 iExists _. iFrame. iFrame "HownMaking".
        case_bool_decide as Heq.
        - iDestruct (big_sepM_subseteq with "HownRpcCls") as "$".
          { apply: delete_subseteq. }
        - iFrame "#". }
      wp_pures.
      iClear "HownRpcCls HownMaking". clear rpcCls making rpcClsM makingM Hcl2.
      wp_apply (wp_ConnMan__getClient with "Hconn").
      iIntros (cl') "#Hcl'".
      wp_store.
      wp_pures.
      iModIntro. iLeft. iSplitR; first done.
      eauto with iFrame.
    }
  } 
  (* no err *)
  wp_pures.
  iModIntro. iRight. iSplitR; first done.
  iApply "HΦ".
  iDestruct "Hrep" as (rep_sl repData) "(? & ? & ?)".
  eauto with iFrame.
Qed.

End connman_proof.
