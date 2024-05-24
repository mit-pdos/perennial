From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.memkv Require Import common_proof memkv_shard_definitions.

#[local] Set Universe Polymorphism.

Definition uCOORD_ADD: nat :=
  Eval vm_compute in match COORD_ADD with LitV (LitInt n) => uint.nat n | _ => 0 end.
Definition uCOORD_GET: nat :=
  Eval vm_compute in match COORD_GET with LitV (LitInt n) => uint.nat n | _ => 0 end.

Record memkv_coord_names := {
 coord_urpc_gn : server_chan_gnames ;
 coord_kv_gn : gname
}.

Section memkv_global_coord_definitions.

Context `{!gooseGlobalGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

Definition all_are_shard_servers (s:list u64) γkv : iProp Σ :=
  ∀ sid host, ⌜s !! sid = Some host⌝ →
              (∃ γ, is_shard_server host γ ∗ ⌜γ.(kv_gn) = γkv⌝)
.

Polymorphic Definition is_coord_server_addSpec γkv : RpcSpec :=
  {| spec_ty := u64;
     spec_Pre := (λ host reqData, ⌜has_encoding_Uint64 reqData host ⌝ ∗
                                   ∃ γ, ⌜ γ.(kv_gn) = γkv ⌝ ∗ is_shard_server host γ)%I;
     spec_Post := (λ host reqData repData, True)%I |}.

Definition has_encoding_shardMapping (data : list u8) (l: list u64) :=
  has_encoding data (EncUInt64 <$> l) ∧
  length l = uint.nat 65536.

Polymorphic Definition is_coord_server_getSpec γkv : RpcSpec :=
  {| spec_ty := unit;
     spec_Pre := (λ _ reqData, True)%I;
     spec_Post := (λ _ reqData repData,
                   ∃ (shardMapping : list u64),
                     ⌜ has_encoding_shardMapping repData shardMapping ⌝ ∗
                     all_are_shard_servers shardMapping γkv)%I |}.

Definition is_coord_server (host : u64) γ :=
  ("#HaddSpec" ∷ is_urpc_spec γ.(coord_urpc_gn) host uCOORD_ADD (is_coord_server_addSpec γ.(coord_kv_gn)) ∗
  "#HgetSpec" ∷ is_urpc_spec γ.(coord_urpc_gn) host uCOORD_GET (is_coord_server_getSpec γ.(coord_kv_gn)))%I.

End memkv_global_coord_definitions.

Section memkv_coord_definitions.

Context `{!heapGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

Definition own_ShardClerkSet (s:loc) (γkv:gname) : iProp Σ :=
  ∃ (c:loc) (cls_ptr:loc)  (clsM:gmap u64 loc),
  "Hcls" ∷ s ↦[ShardClerkSet :: "cls"] #cls_ptr ∗
  "Hc" ∷ s ↦[ShardClerkSet :: "c"] #c ∗
  "HclsMap" ∷ own_map cls_ptr (DfracOwn 1) clsM ∗
  "HclsOwn" ∷ ([∗ map] host ↦ cl_ptr ∈ clsM, own_KVShardClerk cl_ptr γkv) ∗
  "#Hc_own" ∷ is_ConnMan c
.

Definition own_KVCoordServer (s : loc) γ : iProp Σ :=
  ∃ (hostShards_ptr : loc) (hostShards:gmap u64 u64) (clset : loc) shardMap_sl (shardMapping : list u64),
  "hostShards" ∷ s ↦[KVCoord :: "hostShards"] #hostShards_ptr ∗
  "shardClerks" ∷ s ↦[KVCoord :: "shardClerks"] #clset ∗
  "%Hlen_shardMapping" ∷ ⌜Z.of_nat (length shardMapping) = uNSHARD⌝%Z ∗
  "%HshardMapping_dom" ∷ ⌜∀ i : u64, uint.Z i < uint.Z uNSHARD → is_Some (shardMapping !! uint.nat i)⌝ ∗
  "shardMap" ∷ s ↦[KVCoord :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷ typed_slice.own_slice (V:=u64) shardMap_sl HostName (DfracOwn 1) shardMapping ∗
  "#HshardServers" ∷ all_are_shard_servers shardMapping γ ∗
  "Hmap" ∷ own_map hostShards_ptr (DfracOwn 1) hostShards ∗
  "HshardClerksSet" ∷ own_ShardClerkSet clset γ.

Definition is_KVCoordServer (s:loc) γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[KVCoord :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock memKVN mu (own_KVCoordServer s γ.(coord_kv_gn))
.

End memkv_coord_definitions.
