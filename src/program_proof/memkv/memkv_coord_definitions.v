From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Import common_proof memkv_shard_definitions.

Definition uCOORD_ADD: nat :=
  Eval vm_compute in match COORD_ADD with LitV (LitInt n) => int.nat n | _ => 0 end.
Definition uCOORD_GET: nat :=
  Eval vm_compute in match COORD_GET with LitV (LitInt n) => int.nat n | _ => 0 end.

Record memkv_coord_names := {
 coord_urpc_gn : server_chan_gnames ;
 coord_kv_gn : gname
}
.

Section memkv_global_coord_definitions.

(* TODO: should it be heap_globalG or heapGS? *)
(* I think the former because it is sent from a coord server to a client *)
Context `{!dist_lifting.heap_globalG Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Definition all_are_shard_servers (s:list u64) γkv : iProp Σ :=
  ∀ sid host, ⌜s !! sid = Some host⌝ →
              (∃ γ, is_shard_server host γ ∗ ⌜γ.(kv_gn) = γkv⌝)
.

Definition is_coord_server_addSpec γkv : RPCSpec :=
  {| spec_rpcid := uCOORD_ADD;
     spec_ty := u64;
     spec_Pre := (λ host reqData, ⌜has_encoding_Uint64 reqData host ⌝ ∗
                                   ∃ γ, ⌜ γ.(kv_gn) = γkv ⌝ ∗ is_shard_server host γ)%I;
     spec_Post := (λ host reqData repData, True)%I |}.

Definition has_encoding_shardMapping (data : list u8) (l: list u64) :=
  has_encoding data (EncUInt64 <$> l) ∧
  length l = int.nat 65536.

Definition is_coord_server_getSpec γkv : RPCSpec :=
  {| spec_rpcid := uCOORD_GET;
     spec_ty := unit;
     spec_Pre := (λ _ reqData, True)%I;
     spec_Post := (λ _ reqData repData,
                   ∃ (shardMapping : list u64),
                     ⌜ has_encoding_shardMapping repData shardMapping ⌝ ∗
                     all_are_shard_servers shardMapping γkv)%I |}.

Definition is_coord_server (host : u64) γ :=
  ("#HaddSpec" ∷ has_handler γ.(coord_urpc_gn) host (is_coord_server_addSpec γ.(coord_kv_gn)) ∗
  "#HgetSpec" ∷ has_handler γ.(coord_urpc_gn) host (is_coord_server_getSpec γ.(coord_kv_gn)))%I.

End memkv_global_coord_definitions.

Section memkv_coord_definitions.

Context `{!heapGS Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Definition own_ShardClerkSet (s:loc) (γkv:gname) : iProp Σ :=
  ∃ (cls_ptr:loc) (clsM:gmap u64 loc),
  "Hcls" ∷ s ↦[ShardClerkSet :: "cls"] #cls_ptr ∗
  "HclsMap" ∷ is_map cls_ptr 1 clsM ∗
  "HclsOwn" ∷ [∗ map] host ↦ cl_ptr ∈ clsM, own_MemKVShardClerk cl_ptr γkv
.

Definition own_MemKVCoordServer (s : loc) γ : iProp Σ :=
  ∃ cfg (hostShards_ptr : loc) hostShards (clset : loc) shardMap_sl (shardMapping : list u64),
  "config" ∷ s ↦[MemKVCoord :: "config"] #cfg ∗
  "hostShards" ∷ s ↦[MemKVCoord :: "hostShards"] #hostShards_ptr ∗
  "shardClerks" ∷ s ↦[MemKVCoord :: "shardClerks"] #clset ∗
  "%Hlen_shardMapping" ∷ ⌜Z.of_nat (length shardMapping) = uNSHARD⌝%Z ∗
  "%HshardMapping_dom" ∷ ⌜∀ i : u64, int.Z i < int.Z uNSHARD → is_Some (shardMapping !! int.nat i)⌝ ∗
  "shardMap" ∷ s ↦[MemKVCoord :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷ typed_slice.is_slice (V:=u64) shardMap_sl HostName 1 shardMapping ∗
  "#HshardServers" ∷ all_are_shard_servers shardMapping γ ∗
  "Hmap" ∷ is_map (V:=u64) hostShards_ptr 1 hostShards ∗
  "HshardClerksSet" ∷ own_ShardClerkSet clset γ.

Definition is_MemKVCoordServer (s:loc) γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[MemKVCoord :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock memKVN mu (own_MemKVCoordServer s γ.(coord_kv_gn))
.


End memkv_coord_definitions.
