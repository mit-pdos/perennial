From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Import memkv_marshal_get_proof common_proof.

Section memkv_shard_proof.

Context `{!heapG Σ, rpcG Σ GetReplyC}.

Axiom kvptsto : gname → u64 → list u8 → iProp Σ.

Global Instance kvptst_tmlss γkv k v : Timeless (kvptsto γkv k v).
Admitted.

Definition uKV_GET := 2.

Record memkv_shard_names := {
 rpc_gn : rpc_names ;
 kv_gn : gname
}
.

Implicit Type γ : memkv_shard_names.

(* FIXME: lastReplyMap type *)

Axiom shardOfC : u64 → u64.

Definition own_shard γkv sid (m:gmap u64 (list u8)) : iProp Σ :=
  [∗ set] k ∈ (fin_to_set u64), ⌜shardOfC k ≠ sid⌝ ∨
                                kvptsto γkv k (default [] (m !! k))
.

Definition own_MemKVShardServer (s:loc) γ : iProp Σ :=
  ∃ (lastReply_ptr lastSeq_ptr peers_ptr:loc) (kvss_sl shardMap_sl:Slice.t)
    (lastReplyM:gmap u64 GetReplyC) (lastReplyMV:gmap u64 goose_lang.val) (lastSeqM:gmap u64 u64) (nextCID:u64) (shardMapping:list bool) (kvs_ptrs:list loc),
  "HlastReply" ∷ s ↦[MemKVShardServer.S :: "lastReply"] #lastReply_ptr ∗
  "HlastReplyMap" ∷ map.is_map lastReply_ptr (lastReplyMV, #0) ∗ (* TODO: default *)
  "%HlastReplyMVdom" ∷ ⌜dom (gset u64) lastReplyMV = dom (gset u64) lastSeqM⌝ ∗
  "HlastReply_structs" ∷ ([∗ map] k ↦ v;rep ∈ lastReplyMV ; lastReplyM, (∃ val_sl q, ⌜v = (#rep.(GR_Err), (slice_val val_sl, #()))%V⌝ ∗ typed_slice.is_slice_small val_sl byteT q rep.(GR_Value))) ∗
  "HlastSeq" ∷ s ↦[MemKVShardServer.S :: "lastSeq"] #lastSeq_ptr ∗
  "HlastSeqMap" ∷ is_map lastSeq_ptr lastSeqM ∗
  "HnextCID" ∷ s ↦[MemKVShardServer.S :: "nextCID"] #nextCID ∗
  "HshardMap" ∷ s ↦[MemKVShardServer.S :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷ typed_slice.is_slice shardMap_sl boolT 1%Qp shardMapping ∗
  "Hkvss" ∷ s ↦[MemKVShardServer.S :: "kvss"] (slice_val kvss_sl) ∗
  "Hkvss_sl" ∷ slice.is_slice kvss_sl (mapT (slice.T byteT)) 1%Qp (fmap (λ x:loc, #x) kvs_ptrs) ∗
  "Hpeers" ∷ s ↦[MemKVShardServer.S :: "peers"] #peers_ptr ∗
  "Hrpc" ∷ RPCServer_own_ghost γ.(rpc_gn) lastSeqM lastReplyM ∗
  "%HshardMapLength" ∷ ⌜length shardMapping = uNSHARD⌝ ∗
  "HownShards" ∷ ([∗ set] sid ∈ (fin_to_set u64),
                  ⌜(shardMapping !! (int.nat sid)) ≠ Some true⌝ ∨
                  (∃ (kvs_ptr:loc) (m:gmap u64 (list u8)) (mv:gmap u64 goose_lang.val),
                      own_shard γ.(kv_gn) sid m ∗ (* own shard *)
                      ⌜kvs_ptrs !! (int.nat sid) = Some kvs_ptr⌝ ∗
                      map.is_map kvs_ptr (mv, (slice_val Slice.nil)) ∗
                      ([∗ set] k ∈ (fin_to_set u64),
                       ⌜shardOfC k ≠ sid⌝ ∨ (∃ vsl, ⌜default (slice_val Slice.nil) (mv !! k) = (slice_val vsl)⌝ ∗ typed_slice.is_slice vsl byteT (1%Qp) (default [] (m !! k))) )
                  )
                 )
.

Definition memKVN := nroot .@ "memkv".

Definition is_MemKVShardServer (s:loc) γ : iProp Σ :=
  ∃ mu,
  "#His_srv" ∷ is_RPCServer γ.(rpc_gn) ∗
  "#Hmu" ∷ readonly (s ↦[MemKVShardServer.S :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock memKVN mu (own_MemKVShardServer s γ)
.

Definition PreShardGet Eo Ei γ key Q : iProp Σ :=
  |={Eo,Ei}=> (∃ v, kvptsto γ.(kv_gn) key v ∗ (kvptsto γ.(kv_gn) key v ={Ei,Eo}=∗ Q v))
.

Definition PostShardGet Eo Ei γ (key:u64) Q (rep:GetReplyC) : iProp Σ := ⌜rep.(GR_Err) ≠ 0⌝ ∗ (PreShardGet Eo Ei γ key Q) ∨
                                                        ⌜rep.(GR_Err) = 0⌝ ∗ (Q rep.(GR_Value)).

Definition is_shard_server host γ : iProp Σ :=
  "#His_rpc" ∷ is_RPCServer γ.(rpc_gn) ∗
  "#HgetSpec" ∷ handler_is (coPset * coPset * (list u8 → iProp Σ) * rpc_request_names) host uKV_GET
             (λ x reqData, ∃ req, ⌜has_encoding_GetRequest reqData req⌝ ∗
                                   is_RPCRequest γ.(rpc_gn) x.2 (PreShardGet x.1.1.1 x.1.1.2 γ req.(GR_Key) x.1.2)
                                                            (PostShardGet x.1.1.1 x.1.1.2 γ req.(GR_Key) x.1.2)
                                                            {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |}
             ) (* pre *)
             (λ x reqData repData, ∃ req rep, ⌜has_encoding_GetReply repData rep⌝ ∗
                                              ⌜has_encoding_GetRequest reqData req⌝ ∗
                                              (RPCRequestStale γ.(rpc_gn) {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |} ∨
                                              RPCReplyReceipt γ.(rpc_gn) {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |} rep)
             ) (* post *)
.

Lemma wp_shardOf key :
  {{{
       True
  }}}
    shardOf #key
  {{{
       RET #(shardOfC key); True
  }}}.
Proof.
Admitted.

Lemma own_shard_agree key v γkv sid m:
  shardOfC key = sid →
  own_shard γkv sid m -∗ kvptsto γkv key v -∗
  ⌜v = default [] (m !! key)⌝
.
Proof.
  iIntros (?) "Hown Hptsto".
  unfold own_shard.
  iDestruct (big_sepS_elem_of_acc _ _ key with "Hown") as "[[%Hbad|Hown] _]".
  { set_solver. }
  { exfalso. done. }
  admit.
Admitted.

Lemma wp_GetRPC (s args_ptr reply_ptr:loc) args γ Eo Ei γreq Q :
  is_MemKVShardServer s γ -∗
  {{{
       own_GetRequest args_ptr args ∗
       (∃ dummy_rep, own_GetReply reply_ptr dummy_rep) ∗
       is_RPCRequest γ.(rpc_gn) γreq (PreShardGet Eo Ei γ args.(GR_Key) Q)
                                (PostShardGet Eo Ei γ args.(GR_Key) Q)
                                {| Req_CID:=args.(GR_CID); Req_Seq:=args.(GR_Seq) |}
  }}}
    MemKVShardServer__GetRPC #s #args_ptr #reply_ptr
  {{{
       rep, RET #();
       own_GetReply reply_ptr rep ∗
       (RPCRequestStale γ.(rpc_gn) {| Req_CID:=args.(GR_CID); Req_Seq:=args.(GR_Seq) |} ∨
        RPCReplyReceipt γ.(rpc_gn) {| Req_CID:=args.(GR_CID); Req_Seq:=args.(GR_Seq) |} rep)
  }}}.
Proof.
  iIntros "#His_shard !#" (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hargs & Hrep & #HreqInv)".
  iNamed "Hargs". iNamed "Hrep".

  wp_lam.
  wp_pures.

  iNamed "His_shard".
  wp_loadField.
  wp_apply (acquire_spec with "[$HmuInv]").
  iIntros "[Hlocked Hown]".

  iNamed "Hown".

  wp_pures.
  wp_lam.
  wp_pures.

  wp_loadField. wp_loadField.
  wp_apply (wp_MapGet with "HlastSeqMap").
  iIntros (v ok) "[%HseqGet HlastSeqMap]".
  wp_pures.

  wp_apply (wp_and ok (int.Z args.(GR_Seq) ≤ int.Z v)%Z).
  { wp_pures. by destruct ok. }
  { iIntros "_". admit. (* tweak code to make less annoying *) }

  wp_if_destruct.
  { (* reply table *)
    wp_loadField.
    wp_loadField.
    wp_apply (map.wp_MapGet with "HlastReplyMap").
    iIntros (reply replyOk) "[%HlookupReply HlastReplyMap]".
    wp_pures.
    Transparent struct.store.
    unfold struct.store.
    Opaque struct.store.
    Opaque struct.t.
    wp_pures.

    iAssert (reply_ptr ↦[struct.t GetReply.S] (#_, (slice_val val_sl, #())) )%I with "[HValue HErr]" as "Hrep".
    {
      iApply struct_fields_split.
      iFrame.
      done.
    }

    destruct ok; last first.
    { exfalso. naive_solver. }
    apply map_get_true in HseqGet.
    destruct Heqb as [_ HseqLe].

    (* get a copy of the is_slice for the slice we're giving in reply *)
    assert (is_Some (lastReplyMV !! args.(GR_CID))) as [? HlastReplyMVlookup].
    {
      assert (args.(GR_CID) ∈ dom (gset u64) lastSeqM).
      { by eapply elem_of_dom_2. }
      assert (args.(GR_CID) ∈ dom (gset u64) lastReplyMV).
      { rewrite -HlastReplyMVdom in H0. done. }
      apply elem_of_dom.
      done.
    }

    iDestruct (big_sepM2_lookup_iff with "HlastReply_structs") as %Hdom.
    assert (is_Some (lastReplyM !! args.(GR_CID))) as [? HlastReplyMlookup].
    { apply Hdom. naive_solver. }

    iDestruct (big_sepM2_lookup_acc _ _ _ args.(GR_CID) with "HlastReply_structs") as "[HlastReply_struct HlastReply_structs]".
    {
      done.
    }
    {
      done.
    }

    iDestruct "HlastReply_struct" as (srv_val_sl ?) "[%Hx Hsrv_val_sl]".
    assert (x = reply) as ->.
    {
      unfold map.map_get in HlookupReply.
      rewrite HlastReplyMVlookup in HlookupReply.
      naive_solver.
    }

    rewrite Hx.
    Opaque typed_slice.is_slice_small. (* to split fraction *)
    iDestruct "Hsrv_val_sl" as "[Hsrv_val_sl Hrep_val_sl]".
    Transparent typed_slice.is_slice_small.
    iSpecialize ("HlastReply_structs" with "[Hsrv_val_sl]").
    {
      iExists _, _.
      iFrame.
      done.
    }
    (* Now we have a fraction of the slice we were looking for *)

    wp_apply (wp_StoreAt with "Hrep").
    { admit. } (* TODO: typecheck *)
    iIntros "Hrep".
    wp_pures.

    (* now split into stale/nonstale cases *)
    destruct (Z.lt_ge_cases (int.Z args.(GR_Seq)) (int.Z v)) as [Hcase|Hcase].
    { (* Stale *)
      iMod (smaller_seqno_stale_fact _ {| Req_CID:=_; Req_Seq:=_ |} v with "His_srv Hrpc") as "HH".
      { done. }
      { done. }
      { done. }
      iDestruct "HH" as "[Hrpc #Hstale]".
      wp_loadField.
      wp_apply (release_spec with "[-HΦ HCID HSeq HKey HValue_sl Hrep Hrep_val_sl]").
      {
        iFrame "#∗".
        iNext.
        iExists _,_,_, _, _, _, _, _.
        iExists _, _, _.
        iFrame.
        done.
      }
      iApply "HΦ".

      iDestruct (struct_fields_split with "Hrep") as "HH".
      iNamed "HH".
      iSplitL "Err Value Hrep_val_sl".
      {
        iExists _; iFrame.
        iExists _; iFrame.
      }
      iLeft.
      iFrame "#".
    }
    { (* Not stale *)
      assert (v = args.(GR_Seq)) by word.
      rewrite H0 in HseqGet.
      iMod (server_replies_to_request _ {| Req_CID:=_; Req_Seq:=_ |} with "His_srv Hrpc") as "HH".
      { done. }
      { done. }
      { eexists _. naive_solver. }
      iDestruct "HH" as "[#Hreceipt Hrpc]".

      (* prove that args.(GR_CID) is in lastReplyMV (probably just add [∗ map] _ ↦ _;_ ∈ lastReplyMV ; lastSeq, True) *)
      wp_loadField.
      wp_apply (release_spec with "[-HΦ HCID HSeq HKey HValue_sl Hrep Hrep_val_sl]").
      {
        iFrame "#∗".
        iNext.
        iExists _,_,_, _, _, _, _, _.
        iExists _, _, _.
        iFrame.
        done.
      }
      iApply "HΦ".
      iDestruct (struct_fields_split with "Hrep") as "HH".
      iNamed "HH".
      iSplitL "Err Value Hrep_val_sl".
      {
        iExists _; iFrame.
        iExists _; iFrame.
      }
      iRight.
      rewrite HlastReplyMlookup.
      simpl.
      iFrame "#".
    }
  }
  {
    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_MapInsert with "HlastSeqMap").
    { done. }
    iIntros "HlastSeqMap".

    wp_pures.
    wp_loadField.
    wp_apply (wp_shardOf).
    wp_pures.
    wp_loadField.

    iDestruct (typed_slice.is_slice_small_acc with "HshardMap_sl") as "[HshardMap_sl HshardMap_sl_close]".
    set (sid:=shardOfC args.(GR_Key)) in *.

    assert (∃ b, shardMapping !! int.nat sid = Some b) as [? ?].
    {
      eapply list_lookup_lt.
      rewrite HshardMapLength.
      admit. (* annoying mod ineq *)
    }
    wp_apply (typed_slice.wp_SliceGet with "[$HshardMap_sl]").
    {
      iPureIntro. done.
    }
    iIntros "HshardMap_sl".
    wp_pures.

    (* get resources out of escrow before splitting into cases *)
    iMod (server_takes_request with "HreqInv Hrpc") as "HH".
    { done. }
    {
      rewrite HseqGet.
      simpl.
      destruct ok.
      {
        apply map_get_true in HseqGet.
        admit. (* negate Heqb *)
      }
      {
        apply map_get_false in HseqGet as [_ HseqGet].
        rewrite HseqGet.
        admit. (* FIXME: add precondition that GR_Seq > 0 *)
      }
    }
    iDestruct "HH" as "(Hγpre & Hpre & Hproc)".

    wp_if_destruct.
    { (* have the shard *)
      wp_loadField.
      wp_loadField.
      iDestruct (is_slice_split with "Hkvss_sl") as "[Hkvss_sl Hkvss_sl_close]".
      iDestruct (big_sepS_elem_of_acc _ _ sid with "HownShards") as "[HownShard HownShards]".
      { set_solver. }
      iDestruct "HownShard" as "[%Hbad|HownShard]".
      { exfalso. done. }
      iDestruct "HownShard" as (kvs_ptr m mv) "(HshardGhost & %Hkvs_lookup & HkvsMap & HvalSlices)".
      wp_apply (wp_SliceGet _ _ _ _ _ _ _ (#kvs_ptr) with "[Hkvss_sl]").
      {
        iFrame "Hkvss_sl".
        iPureIntro.
        rewrite list_lookup_fmap.
        rewrite Hkvs_lookup.
        done.
      }
      iIntros "[Hkvss_sl %Hkvs_ty]".

      wp_apply (map.wp_MapGet with "[$HkvsMap]").
      iIntros (value okValue) "[%HlookupVal HkvsMap]".
      wp_pures.
      wp_apply (typed_slice.wp_NewSlice (V:=u8)).
      iIntros (val_sl') "Hval_sl".
      assert (value = default (slice_val Slice.nil) (mv !! args.(GR_Key))) as Hvalue.
      { naive_solver. }
      rewrite Hvalue.

      iDestruct (big_sepS_elem_of_acc _ _ args.(GR_Key) with "HvalSlices") as "[Hsrv_val_sl HvalSlices]".
      { set_solver. }
      iDestruct "Hsrv_val_sl" as "[%Hbad|Hsrv_val_sl]".
      { exfalso. done. }

      iDestruct "Hsrv_val_sl" as (?) "[%HvalSliceRe Hsrv_val_sl]".
      rewrite HvalSliceRe.
      iDestruct (typed_slice.is_slice_small_acc with "Hsrv_val_sl") as "[Hsrv_val_sl_small Hsrv_val_sl]".
      wp_apply (typed_slice.wp_SliceAppendSlice (V:=u8) with "[$Hval_sl $Hsrv_val_sl_small]").

      rewrite app_nil_l.
      iIntros (val_sl'') "[Hval_sl Hsrv_val_sl_small]".

      iSpecialize ("Hsrv_val_sl" with "Hsrv_val_sl_small").

      (* fill in reply struct *)
      wp_apply (wp_storeField with "HValue").
      { apply slice_val_ty. }
      iIntros "HValue".
      wp_pures.
      wp_storeField.

      (* save reply in reply table *)
      Transparent struct.load.
      unfold struct.load.
      iAssert (reply_ptr ↦[struct.t GetReply.S] (#0, (slice_val val_sl'', #())) )%I with "[HValue HErr]" as "Hrep".
      {
        iApply struct_fields_split.
        iFrame.
        done.
      }
      wp_load.
      wp_loadField.
      wp_loadField.

      wp_apply (map.wp_MapInsert with "HlastReplyMap").
      iIntros "HlastReplyMap".

      wp_pures.
      (* commit *)
      unfold PreShardGet.
      iApply fupd_wp.
      iMod (fupd_mask_subseteq _) as "Hclose"; last iMod "Hpre".
      { done. }
      iDestruct "Hpre" as (v0) "(Hkvptsto & HfupdQ)".
      iDestruct (own_shard_agree with "HshardGhost Hkvptsto") as %Hmatch.
      { done. }
      (* match up with HshardGhost *)
      rewrite -Hmatch.
      iMod ("HfupdQ" with "Hkvptsto") as "Q".
      iMod "Hclose" as "_".
      iMod (server_completes_request with "His_srv HreqInv Hγpre [Q] Hproc") as "HH".
      { done. }
      { done. }
      { simpl. admit. (* TODO: some more pure inequality reasoning *) }
      {
        iNext.
        iRight.
        instantiate (1:=mkGetReplyC _ _).
        iFrame "Q".
        simpl.
        done.
      }
      iDestruct "HH" as "(#Hreceipt & Hrpc)".
      iModIntro.

      iDestruct ("HshardMap_sl_close" with "HshardMap_sl") as "HshardMap_sl".
      wp_loadField.
      iDestruct (typed_slice.is_slice_small_acc with "Hval_sl") as "[Hval_sl _]".
      Opaque typed_slice.is_slice_small.
      iDestruct "Hval_sl" as "[Hrep_val_sl Hsrv_rep_val_sl]".
      Transparent typed_slice.is_slice.
      wp_apply (release_spec with "[-HΦ HCID HSeq HKey Hrep_val_sl Hrep]").
      {
        iFrame "#∗".
        iNext.
        iExists _,_,_, _, _, _, _, _.
        iExists _, _, _.
        iFrame.
        iSplitL "".
        {
          iPureIntro.
          simpl.
          rewrite !dom_insert_L.
          congruence.
        }
        iSplitL "HlastReply_structs Hsrv_rep_val_sl".
        {
          iApply (big_sepM2_insert_2 with "[Hsrv_rep_val_sl] HlastReply_structs").
          { simpl.
            iExists _, _.
            iFrame.
            done.
          }
        }
        iSplitL ""; first done.
        iApply "HownShards".
        iRight.
        iExists _, _, _.
        iFrame.
        iSpecialize ("HvalSlices" with "[Hsrv_val_sl]").
        {
          iRight. iExists _; iFrame. done.
        }
        iFrame "HvalSlices".
        done.
      }
      iApply "HΦ".
      iDestruct (struct_fields_split with "Hrep") as "HH".
      iNamed "HH".
      instantiate (1:= mkGetReplyC _ _).
      iSplitL "Err Value Hrep_val_sl".
      {
        iExists _; iFrame.
        iExists _; iFrame.
      }
      iSimpl.
      iRight.
      iFrame "#".
    }
    { (* don't have shard *)
      wp_storeField.

      iMod (server_completes_request with "His_srv HreqInv Hγpre [Hpre] Hproc") as "HH".
      { done. }
      { done. }
      { simpl. admit. (* TODO: more pure inequality reasoning *) }
      {
        iNext.
        iLeft.
        instantiate (1:=mkGetReplyC 1 dummy_rep.(GR_Value)).
        iFrame "Hpre".
        simpl.
        done.
      }
      iDestruct "HH" as "(#Hreceipt & Hrpc)".

      Transparent struct.load.
      unfold struct.load.
      iAssert (reply_ptr ↦[struct.t GetReply.S] (#1, (slice_val val_sl, #())) )%I with "[HValue HErr]" as "Hrep".
      {
        iApply struct_fields_split.
        iFrame.
        done.
      }
      wp_load.
      wp_loadField.
      wp_loadField.

      wp_apply (map.wp_MapInsert with "HlastReplyMap").
      iIntros "HlastReplyMap".
      wp_pures.

      wp_loadField.
      iDestruct ("HshardMap_sl_close" with "HshardMap_sl") as "HshardMap_sl".
      iDestruct "HValue_sl" as (?) "Hval_sl".
      Opaque typed_slice.is_slice_small.
      iDestruct "Hval_sl" as "[Hsrv_rep_val_sl Hrep_val_sl]".
      Transparent typed_slice.is_slice_small.
      wp_apply (release_spec with "[-HΦ HCID HSeq HKey Hrep_val_sl Hrep]").
      {
        iFrame "HmuInv Hlocked".
        iNext.
        iExists _,_,_, _, _, _, _, _.
        iExists _, _, _.
        iFrame.
        iSplitL "".
        { iPureIntro.
          rewrite !dom_insert_L /=.
          congruence. }
        iSplitL "HlastReply_structs Hsrv_rep_val_sl".
        {
          iApply (big_sepM2_insert_2 with "[Hsrv_rep_val_sl] HlastReply_structs").
          simpl.
          iExists _, _; iFrame.
          done.
        }
        done.
      }
      iApply "HΦ".
      iDestruct (struct_fields_split with "Hrep") as "HH".
      iNamed "HH".
      iSplitL "Err Value Hrep_val_sl".
      {
        iExists _.
        instantiate (1:=mkGetReplyC _ _).
        iFrame.
        iExists _.
        iFrame.
      }
      iSimpl.
      iRight.
      iFrame "#".
    }
  }
Admitted.

Lemma wp_encodeGetReply rep_ptr rep :
  {{{
       own_GetReply rep_ptr rep
  }}}
    encodeGetReply #rep_ptr
  {{{
       repData rep_sl , RET (slice_val rep_sl);
       typed_slice.is_slice rep_sl byteT 1%Qp repData ∗
       ⌜has_encoding_GetReply repData rep ⌝
  }}}.
Proof.
Admitted.

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
  wp_rec. (* FIXME: too much unfolding *)
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
    Search "big_sepM".
    iApply (big_sepM_insert_2 with "").
    { admit. }

    iApply (big_sepM_insert_2 with "").
    { admit. }

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
        Search "slice".
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

End memkv_shard_proof.
