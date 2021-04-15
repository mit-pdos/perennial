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
                      ([∗ map] k ↦ x;v ∈ m;mv, (∃ vsl, ⌜v = (slice_val vsl)⌝ ∗ typed_slice.is_slice vsl byteT 1%Qp x) )
                  )
                 )
.

Definition memKVN := nroot .@ "memkv".

Definition is_MemKVShardServer (s:loc) γ : iProp Σ :=
  ∃ mu,
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
    admit.
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
      destruct okValue.
      {
        apply map.map_get_true in HlookupVal.
        iDestruct (big_sepM2_lookup_iff with "HvalSlices") as %HvalSlicesIff.
        assert (∃ x, m !! args.(GR_Key) = Some x) as [? HlookupValM].
        {
          specialize (HvalSlicesIff args.(GR_Key)).
          apply HvalSlicesIff.
          naive_solver.
        }
        iDestruct (big_sepM2_lookup_acc _ _ _ args.(GR_Key)  with "HvalSlices") as "[HvalSlice HvalSlices]".
        { done. }
        { done. }
        iDestruct "HvalSlice" as (?) "[%HvalSliceRe Hvsl]".
        iEval (rewrite replicate_0) in "Hval_sl".
        rewrite HvalSliceRe.
        wp_apply (typed_slice.wp_SliceAppendSlice (V:=u8) with "[$Hval_sl $Hvsl]").
        rewrite app_nil_l.
        iIntros (val_sl'') "Hval_sl".

        (* fill in reply struct *)
        wp_apply (wp_storeField with "HValue").
        { apply slice_val_ty. }
        iIntros "HValue".
        wp_pures.
        wp_storeField.

        (* save reply in reply table *)
        Transparent struct.load.
        unfold struct.load.
        admit.
      }
      admit.
    }
    admit.
  }
Admitted.

End memkv_shard_proof.
