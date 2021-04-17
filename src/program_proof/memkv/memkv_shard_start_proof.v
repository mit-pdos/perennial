From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Export memkv_shard_proof memkv_install_shard_proof common_proof.

Section memkv_shard_start_proof.

Context `{!heapG Σ, rpcG Σ GetReplyC}.

Lemma wp_MemKVShardServer__Start (s:loc) host γ :
is_shard_server host γ -∗
is_MemKVShardServer s γ -∗
  {{{
       True
  }}}
    MemKVShardServer__Start #s
  {{{
       RET #(); True
  }}}.
Proof.
  iIntros "#His_shard #His_memkv !#" (Φ) "_ HΦ".
  wp_rec.
  change (Alloc (InjLV (λ: <>, (λ: <>, #())%V))) with
      (NewMap grove_common.RawRpcFunc).
  wp_apply map.wp_NewMap.
  iIntros (handlers_ptr) "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (grove_ffi.wp_StartRPCServer with "[$Hmap]").
  {
    iApply (big_sepM_insert_2 with "").
    { admit. }

    iApply (big_sepM_insert_2 with "").
    { (* InstallShard() handler_is *)
      simpl.
      iNamed "His_shard".
      iExists _, _, _.
      iFrame "#HinstallSpec".

      clear Φ.
      iIntros (?????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.

      iDestruct "Hpre" as "(Hpre_sl & Hrep & Hpre)".
      iDestruct "Hpre" as (?) "(%Hargs_enc & %HsidLe & HreqInv)".
      wp_apply (wp_decodeInstallShardRequest with "[$Hpre_sl]").
      { done. }
      iIntros (args_ptr) "Hargs".
      wp_apply (wp_InstallShardRPC with "His_memkv [$Hargs $HreqInv]").
      {
        done.
      }
      wp_pures.
      wp_apply (typed_slice.wp_NewSlice (V:=u8)).
      iIntros (reply_sl) "Hrep_sl".
      wp_store.
      iApply "HΦ".
      iFrame.
      done.
    }

    iApply (big_sepM_insert_2 with "").
    { (* Get() handler_is *)
      iNamed "His_shard".
      simpl.
      iExists _, _, _; iFrame "HgetSpec".

      clear Φ.
      iIntros (?????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.
      wp_apply (wp_allocStruct).
      { admit. } (* TODO: typecheck *)
      iIntros (rep_ptr) "Hrep".
      wp_pures.
      iDestruct "Hpre" as "(Hreq_sl & Hrep_ptr & Hpre)".
      iDestruct "Hpre" as (args) "(%Henc & #HreqInv)".
      wp_apply (wp_decodeGetRequest with "[$Hreq_sl]").
      { done. }
      iIntros (args_ptr) "Hargs".
      wp_apply (wp_GetRPC with "His_memkv [$Hargs Hrep $HreqInv]").
      {
        replace (zero_val (struct.t GetReply.S)) with ((#0, (slice.nil, #()))%V); last first.
        {
          admit. (* zero value of GetReply *)
        }

        iDestruct (struct_fields_split with "Hrep") as "HH".
        iNamed "HH".
        iExists (mkGetReplyC _ []).
        iFrame.
        iExists (Slice.nil).
        iFrame.
        simpl.
        iDestruct (typed_slice.is_slice_zero byteT 1%Qp) as "HH".
        iDestruct (typed_slice.is_slice_small_acc with "HH") as "[H _]".
        iExists 1%Qp.
        iFrame "H".
      }
      iIntros (rep') "[Hrep Hpost]".
      wp_pures.
      wp_apply (wp_encodeGetReply with "Hrep").
      iIntros (repData rep_sl) "[Hrep_sl %HrepEnc]".
      wp_store.
      iApply "HΦ".
      iModIntro.
      iFrame.
      iNext.
      iExists _, _; iFrame.
      done.
    }

    iApply (big_sepM_insert_2 with "").
    { admit. }


    iApply (big_sepM_insert_2 with "").
    { admit. }

    iApply big_sepM_empty.
    done.
  }
  by iApply "HΦ".
Admitted.

End memkv_shard_start_proof.
