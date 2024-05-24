From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.

From Perennial.program_proof.memkv Require Export
  memkv_shard_definitions
  memkv_put_proof memkv_conditional_put_proof memkv_get_proof memkv_install_shard_proof memkv_getcid_proof memkv_move_shard_proof
  common_proof.

#[local] Set Universe Polymorphism.

Section memkv_shard_start_proof.

Context `{!heapGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

Lemma wp_KVShardServer__Start (s:loc) (host : u64) γ :
is_urpc_dom γ.(urpc_gn) {[ W64 0; W64 1; W64 2; W64 3; W64 4; W64 5 ]} -∗
is_shard_server host γ -∗
is_KVShardServer s γ -∗
  {{{
       True
  }}}
    KVShardServer__Start #s #host
  {{{
       RET #(); True
  }}}.
Proof.
  iIntros "#Hdom #His_shard #His_memkv !#" (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  wp_apply (map.wp_NewMap u64).
  iIntros (handlers_ptr) "Hmap".
  iAssert (∃ erpc, is_erpc_server γ.(erpc_gn) erpc ∗ readonly (s ↦[KVShardServer :: "erpc"] #erpc))%I as (erpc) "[#Herpc ?]".
  { iNamed "His_memkv". eauto. }
  wp_loadField.
  wp_pures.
  rewrite is_shard_server_unfold.
  iNamed "His_shard".

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (wp_erpc_Server_HandleRequest (is_shard_server_putSpec γ.(kv_gn)) with "Herpc").

  iIntros (put_handler) "#Hput_handler".

  iSpecialize ("Hput_handler" with "[]").
  {
    clear Φ.
    iIntros ([Q req1] ???) "!#".
    iIntros (Φ) "Hpre HΦ".
    wp_pures.
    wp_apply (wp_allocStruct).
    {
      naive_solver.
    }
    iIntros (rep_ptr) "Hrep".
    wp_pures.
    iDestruct "Hpre" as "(Hreq_sl & Hrep_ptr & [%Henc Hpre])".
    wp_apply (wp_DecodePutRequest with "[$Hreq_sl]").
    { done. }
    iIntros (args_ptr val_sl) "Hargs".
    wp_apply (wp_PutRPC with "His_memkv [$Hargs Hrep $Hpre]").
    {
      iDestruct (struct_fields_split with "Hrep") as "HH".
      iNamed "HH".
      iExists (mkPutReplyC _).
      iFrame.
    }
    iIntros (rep') "[Hrep Hpost']".
    wp_pures.
    wp_apply (wp_EncodePutReply with "Hrep").
    iIntros (repData rep_sl) "[Hrep_sl %HrepEnc]".
    iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
    wp_store.
    iApply "HΦ". by iFrame.
  }

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (wp_erpc_Server_HandleRequest (is_shard_server_getSpec γ.(kv_gn)) with "Herpc").
  iIntros (get_handler) "#Hget_handler".

  iSpecialize ("Hget_handler" with "[]").
  {
    clear Φ.
    iIntros ([Q req1] ???) "!#".
    iIntros (Φ) "Hpre HΦ".
    wp_pures.
    wp_apply (wp_allocStruct).
    { val_ty. }
    iIntros (rep_ptr) "Hrep".
    wp_pures.
    iDestruct "Hpre" as "(Hreq_sl & Hrep_ptr & [%Henc Hpre])".
    wp_apply (wp_DecodeGetRequest with "[$Hreq_sl]").
    { done. }
    iIntros (args_ptr) "Hargs".
    iDestruct (typed_slice.own_slice_zero byteT (DfracOwn 1)) as "Hzero_sl".
    iDestruct (typed_slice.own_slice_small_acc with "Hzero_sl") as "{Hzero_sl} [Hzero_sl _]".
    iMod (own_slice_small_persist with "Hzero_sl") as "{Hzero_sl} #Hzero_sl".
    wp_apply (wp_GetRPC with "His_memkv [$Hargs Hrep $Hpre Hzero_sl]").
    {
      rewrite 2!zero_prod_val zero_slice_val.

      iDestruct (struct_fields_split with "Hrep") as "HH".
      iNamed "HH".
      iExists (mkGetReplyC _ []).
      iFrame "∗#".
    }
    iIntros (rep') "[Hrep Hpost']".
    wp_pures.
    wp_apply (wp_EncodeGetReply with "Hrep").
    iIntros (repData rep_sl) "[Hrep_sl %HrepEnc]".
    iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
    wp_store.
    iApply "HΦ". by iFrame.
  }

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (wp_erpc_Server_HandleRequest (is_shard_server_conditionalPutSpec γ.(kv_gn)) with "Herpc").
  iIntros (cput_handler) "#Hcput_handler".
  iSpecialize ("Hcput_handler" with "[]").
  {
    clear Φ.
    iIntros ([Q req1] ???) "!#".
    iIntros (Φ) "Hpre HΦ".
    wp_pures.
    wp_apply (wp_allocStruct).
    {
      naive_solver.
    }
    iIntros (rep_ptr) "Hrep".
    wp_pures.
    iDestruct "Hpre" as "(Hreq_sl & Hrep_ptr & [%Henc Hpre])".
    wp_apply (wp_DecodeConditionalPutRequest with "[$Hreq_sl]").
    { done. }
    iIntros (args_ptr expv_sl newv) "Hargs".
    wp_apply (wp_ConditionalPutRPC with "His_memkv [$Hargs $Hpre Hrep]").
    {
      iDestruct (struct_fields_split with "Hrep") as "HH".
      iNamed "HH".
      iExists (mkConditionalPutReplyC _ _).
      iFrame.
    }
    iIntros (rep') "[Hrep Hpost']".
    wp_pures.
    wp_apply (wp_EncodeConditionalPutReply with "Hrep").
    iIntros (repData rep_sl) "[Hrep_sl %HrepEnc]".
    iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
    wp_store.
    iApply "HΦ". by iFrame.
  }

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (wp_erpc_Server_HandleRequest (is_shard_server_installSpec γ.(kv_gn)) with "Herpc").
  iIntros (install_handler) "#Hinstall_handler".

  iSpecialize ("Hinstall_handler" with "[]").
  {
    clear Φ.
    iIntros ([] ???) "!#".
    iIntros (Φ) "Hpre HΦ".
    wp_pures.

    iDestruct "Hpre" as "(Hpre_sl & Hrep & Hpre)".
    iDestruct "Hpre" as (?) "(%Hargs_enc & %HsidLe & Hshard)".
    wp_apply (wp_decodeInstallShardRequest with "[$Hpre_sl]").
    { done. }
    iIntros (args_ptr) "Hargs".
    wp_apply (wp_InstallShardRPC with "His_memkv [$Hargs $Hshard]").
    {
      iPureIntro.
      word.
    }
    wp_pures.
    wp_apply (typed_slice.wp_NewSlice (V:=u8)).
    iIntros (reply_sl) "Hrep_sl".
    iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
    wp_store.
    iApply "HΦ".
    iFrame. done.
  }

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (wp_MakeServer with "[$Hmap]").
  iIntros (rs) "Hsown".
  wp_pures.

  wp_apply (wp_StartServer with "[$Hsown]").
  { rewrite ?dom_insert_L; set_solver. }
  {
    iSplitL "".
    { rewrite /handlers_complete.
      rewrite ?dom_insert_L dom_empty_L. iExactEq "Hdom". f_equal. set_solver. }
    iApply (big_sepM_insert_2 with "").
    { (* MoveShardRPC handler_is *)
      simpl. iExists _.
      iFrame "HmoveSpec".

      clear Φ.
      iIntros (????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.
      iDestruct "Hpre" as "(Hreq_sl & Hrep & Hargs)".
      simpl.
      iDestruct "Hargs" as (?) "(%HencArgs & %HsidLe & #Hdst_is_shard)".
      wp_apply (wp_decodeMoveShardRequest with "[$Hreq_sl]").
      { done. }
      iIntros (args_ptr) "Hargs".
      wp_apply (wp_MoveShardRPC with "His_memkv [$Hargs $Hdst_is_shard]").
      { done. }
      wp_pures.
      wp_apply (typed_slice.wp_NewSlice (V:=u8)).
      iIntros (rep_sl) "Hrep_sl".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      wp_store.
      iApply "HΦ".
      by iFrame.
    }

    iApply (big_sepM_insert_2 with "").
    { iExists _. iFrame "HinstallSpec Hinstall_handler".
    }

    iApply (big_sepM_insert_2 with "").
    { (* ConditionalPutRPC handler_is *)
      iExists _. iFrame "HconditionalPutSpec Hcput_handler".
    }

    iApply (big_sepM_insert_2 with "").
    { (* Get() handler_is *)
      iExists _; iFrame "HgetSpec Hget_handler".
    }

    iApply (big_sepM_insert_2 with "").
    { (* PutRPC handler_is *)
      iExists _. iFrame "HputSpec Hput_handler".
    }

    iApply (big_sepM_insert_2 with "").
    { (* GetCIDRPC handler_is *)
      iExists _.
      iFrame "HfreshSpec".

      clear Φ. rewrite /is_urpc_handler_pred.
      iIntros (????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.
      wp_apply (wp_GetCIDRPC with "His_memkv").
      iIntros (cid) "Hcid".
      wp_apply (wp_EncodeUint64).
      iIntros (rep_sl repData) "[Hrep_sl %HrepEnc]".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iDestruct "Hpre" as "(Hreq_sl & Hrep & Hpre)".
      iSimpl in "Hpre".
      wp_store.
      iApply "HΦ".
      by iFrame.
    }

    iApply big_sepM_empty.
    done.
  }
  wp_pures. by iApply "HΦ".

Unshelve.
  - exact w64.
  - typeclasses eauto.
Qed.

End memkv_shard_start_proof.
