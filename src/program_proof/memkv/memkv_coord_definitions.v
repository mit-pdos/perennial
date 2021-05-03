From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Import common_proof memkv_shard_definitions.

Section memkv_coord_definitions.

(* TODO: should it be heap_globalG or heapG? *)
(* I think the former because it is sent from a coord server to a client *)
Context `{!dist_lifting.heap_globalG Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Definition all_are_shard_servers (s:list u64) γkv : iProp Σ :=
  ∀ sid host, ⌜s !! sid = Some host⌝ →
              (∃ γ, is_shard_server host γ ∗ ⌜γ.(kv_gn) = γkv⌝)
.

End memkv_coord_definitions.
