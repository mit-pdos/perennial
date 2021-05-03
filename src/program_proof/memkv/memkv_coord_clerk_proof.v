From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Import common_proof memkv_shard_clerk_proof memkv_shard_definitions memkv_marshal_get_proof.

Section memkv_coord_clerk_proof.

Context `{!heapG Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Axiom own_MemKVCoordClerk : loc → gname → iProp Σ.

Definition all_are_shard_servers (s:list u64) γkv : iProp Σ :=
  ∀ sid host, ⌜s !! sid = Some host⌝ →
              (∃ γ, is_shard_server host γ ∗ ⌜γ.(kv_gn) = γkv⌝)
.


Lemma wp_MemKVCoordClerk__GetShardMap (ck:loc) γkv :
  {{{
       own_MemKVCoordClerk ck γkv
  }}}
    MemKVCoordClerk__GetShardMap #ck
  {{{
       shardMap_sl (shardMapping:list u64), RET (slice_val shardMap_sl);
       own_MemKVCoordClerk ck γkv ∗
       typed_slice.is_slice shardMap_sl uint64T 1%Qp shardMapping ∗
       ⌜Z.of_nat (length shardMapping) = uNSHARD⌝ ∗
       all_are_shard_servers shardMapping γkv
  }}}
.
Proof.
Admitted.

Definition own_ShardClerkSet (s:loc) (γkv:gname) : iProp Σ :=
  ∃ (cls_ptr:loc) (clsM:gmap u64 loc),
  "Hcls" ∷ s ↦[ShardClerkSet :: "cls"] #cls_ptr ∗
  "HclsMap" ∷ is_map cls_ptr 1 clsM ∗
  "HclsOwn" ∷ [∗ map] host ↦ cl_ptr ∈ clsM, own_MemKVShardClerk cl_ptr γkv
.

(* TODO: need precondition that [[is_shard_server host]] *)
Lemma wp_ShardClerkSet__GetClerk (γ:memkv_shard_names) (γkv:gname) (s:loc) (host:u64) :
  {{{
       own_ShardClerkSet s γkv ∗
       is_shard_server host γ ∗
       ⌜γ.(kv_gn) = γkv⌝
  }}}
    ShardClerkSet__GetClerk #s #host
  {{{
       (ck_ptr:loc), RET #ck_ptr; own_MemKVShardClerk ck_ptr γkv ∗
                                    (own_MemKVShardClerk ck_ptr γkv -∗ own_ShardClerkSet s γkv)
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_lam.
  wp_pures.
  iDestruct "Hpre" as "(Hown & #His_shard & %Hγeq)".
  iNamed "Hown".

  wp_loadField.
  wp_apply (wp_MapGet with "HclsMap").
  iIntros (cl_ptr ok) "[%Hlookup HclsMap]".
  wp_pures.
  wp_if_destruct.
  { (* Make fresh clerk*)
    wp_apply (wp_MakeFreshKVClerk with "His_shard").
    iIntros (ck) "HownCk".
    wp_pures.
    wp_loadField.
    wp_apply (wp_MapInsert with "HclsMap").
    { done. }
    iIntros "HclsMap".
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iFrame "HownCk".
    iIntros "Hown".
    iExists _, _; iFrame "Hcls HclsMap".
    rewrite /typed_map.map_insert.
    apply map_get_false in Hlookup.
    iApply (big_sepM_insert with "[Hown $HclsOwn]").
    { naive_solver. }
    iFrame.
  }
  {
    apply map_get_true in Hlookup.
    iDestruct (big_sepM_lookup_acc with "HclsOwn") as "[Hcl HclsOwn]".
    { done. }
    iApply "HΦ".
    iModIntro.
    iFrame.
    iIntros "Hown".
    iSpecialize ("HclsOwn" with "Hown").
    iExists _, _; iFrame.
  }
Qed.

End memkv_coord_clerk_proof.
