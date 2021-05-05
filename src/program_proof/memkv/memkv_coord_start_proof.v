From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.

From Perennial.program_proof.memkv Require Export memkv_shard_definitions memkv_coord_definitions common_proof.

Section memkv_coord_start_proof.

Context `{!heapG Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Lemma wp_encodeShardMap s (shardMap_sl : Slice.t) (shardMapping : list u64) :
  {{{ "Hs_ptr" ∷ s ↦[slice.T HostName] (slice_val shardMap_sl) ∗
      "HshardMap_sl" ∷ typed_slice.is_slice (V:=u64) shardMap_sl HostName 1 shardMapping
  }}}
    encodeShardMap #s
  {{{ (sl: Slice.t) (data: list u8), RET (slice_val sl);
      "%Henc" ∷ ⌜ has_encoding_shardMapping data shardMapping ⌝ ∗
      "Hdata" ∷  typed_slice.is_slice sl byteT 1 data ∗
      "Hs_ptr" ∷ s ↦[slice.T HostName] (slice_val shardMap_sl) ∗
      "HshardMap_sl" ∷ typed_slice.is_slice (V:=u64) shardMap_sl HostName 1 shardMapping
  }}}.
Proof.
  wp_pures. iIntros (Φ) "H HΦ".
  iNamed "H".
  wp_lam.
Admitted.

Lemma wp_MemKVCoord__AddServerRPC s x γ γsh rep dummy_rep_sl :
  {{{ "#His_memkv" ∷ is_MemKVCoordServer s γ ∗
      "#His_shard" ∷ is_shard_server x γsh ∗
      "Hrep" ∷ rep ↦[slice.T byteT] dummy_rep_sl
  }}}
    MemKVCoord__AddServerRPC #s #x
  {{{ (rep_sl : Slice.t) (repData : list u8), RET #();
     rep ↦[slice.T byteT] (slice_val rep_sl) ∗
     typed_slice.is_slice rep_sl byteT 1 repData }}}.
Proof.
Admitted.

Lemma wp_MemKVCoordServer__Start (s:loc) (host : u64) γ :
handlers_dom host γ.(coord_urpc_gn) {[ U64 1; U64 2 ]} -∗
is_coord_server host γ -∗
is_MemKVCoordServer s γ -∗
  {{{
       True
  }}}
    MemKVCoord__Start #s #host
  {{{
       RET #(); True
  }}}.
Proof.
  iIntros "#Hdom #His_coord #His_memkv !#" (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  change (Alloc (InjLV (λ: <>, (λ: <>, #())%V))) with
      (NewMap ((slice.T byteT -> refT (slice.T byteT) -> unitT)%ht)).
  wp_apply map.wp_NewMap.
  iIntros (handlers_ptr) "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.
  rewrite /MemKVCoord__GetShardMapRPC.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (wp_MakeRPCServer with "[$Hmap]").
  iIntros (rs) "Hsown".
  wp_pures.

  iNamed "His_coord".
  wp_apply (wp_StartRPCServer with "[$Hsown]").
  { rewrite ?dom_insert_L; set_solver. }
  {
    iSplitL "".
    { rewrite /handlers_complete.
      rewrite ?dom_insert_L dom_empty_L. iExactEq "Hdom". f_equal. set_solver. }
    iApply (big_sepM_insert_2 with "").
    { (* GetShardMapping RPC handler_is *)
      iExists _, _, _.
      iFrame "#HgetSpec".

      clear Φ.
      iIntros (?????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.
      iDestruct "Hpre" as "(Hreq_sl & Hrep & _)".
      simpl.
      iNamed "His_memkv".
      wp_loadField.
      wp_apply (acquire_spec with "[$HmuInv]").
      iIntros "[Hlocked Hown]".
      iNamed "Hown".
      wp_pures.
      wp_apply (wp_struct_fieldRef_mapsto with "[$shardMap]").
      { eauto. }
      iIntros (fl) "(H1&H2)".
      wp_apply (wp_encodeShardMap with "[$]").
      iIntros (sl data) "(%Henc&H)".
      wp_apply (wp_StoreAt with "[$]").
      { apply slice_val_ty. }
      iIntros "Hrep".
      iNamed "H".
      wp_pures.
      wp_loadField.
      wp_apply (release_spec with "[-HΦ Hrep Hdata]").
      { iFrame "Hlocked HmuInv".
        iNext. iExists _, _, _, _, _, _. iFrame. iFrame "#". iFrame "%".
        iDestruct "H1" as %Hequiv. iApply Hequiv. iFrame. }
      iApply "HΦ". iFrame. iNext. iExists _. iFrame "% #".
    }
    iApply (big_sepM_insert_2 with "").
    { (* AddServerRPC *)
      iExists _, _, _.
      iFrame "#HaddSpec".

      clear Φ.
      iIntros (?????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.
      iDestruct "Hpre" as "(Hreq_sl & Hrep & Hpre)".
      simpl.
      iDestruct "Hpre" as "(%Henc&Hshard)".
      iDestruct "Hshard" as (γsh Heq) "#His_shard".
      wp_apply (wp_decodeUint64 with "[$Hreq_sl]"); first eauto.
      wp_pures.
      simpl in x.
      wp_apply (wp_MemKVCoord__AddServerRPC with "[Hrep]").
      { iSplitL "". 
        { rewrite /named. iExactEq "His_memkv". eauto. }
        iFrame "His_shard". eauto.
      }
      iIntros (??) "(H1&H2)". iApply ("HΦ" with "[$H1 $H2]"); eauto.
    }
    rewrite big_sepM_empty. eauto.
  }
  iApply "HΦ".
  auto.
Qed.

End memkv_coord_start_proof.
