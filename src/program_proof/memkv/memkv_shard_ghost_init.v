From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import adequacy recovery_adequacy dist_adequacy.
From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.

From Perennial.program_proof.memkv Require Export memkv_shard_definitions.

Section memkv_shard_ghost_init_proof.

(* These lemmas happen *before* we get node local names (e.g. the gname for memory, crashes etc. *)
Context `{!heap_globalG Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Existing Instance global_groveG.


(* TODO: duplicating this specs is unfortunate, should try to unify with the set up in shard_definitions *)

Definition shard_SpecList γkv γrpc : RPCSpecList :=
  spec_cons (is_shard_server_putSpec γkv γrpc)
    (spec_cons (is_shard_server_conditionalPutSpec γkv γrpc)
      (spec_cons (is_shard_server_getSpec γkv γrpc)
        (spec_cons (is_shard_server_moveSpec γkv)
          (spec_cons (is_shard_server_installSpec γkv γrpc)
            (spec_cons (is_shard_server_freshSpec γrpc) spec_nil))))).

Lemma shard_server_ghost_init host (γkv : gname) :
  host c↦ ∅ ={⊤}=∗
  ∃ γ, ⌜ γ.(kv_gn) = γkv ⌝ ∗
       handlers_dom host γ.(urpc_gn) (dom_RPCSpecList (shard_SpecList (γ.(kv_gn)) (γ.(rpc_gn)))) ∗
       is_shard_server host γ ∗
       RPCServer_own_ghost γ.(rpc_gn) ∅ ∅ ∗
      ([∗ set] cid ∈ fin_to_set u64, RPCClient_own_ghost γ.(rpc_gn) cid 1).
Proof.
  iIntros "Hg".
  iMod (make_rpc_server (R := ShardReplyC)) as (γrpc) "(#Hown&Hrpc1&Hrpc2)".
  { set_solver. }
  iMod (handler_is_init_list host (shard_SpecList γkv γrpc) with "[Hg]") as (γ) "H".
  { simpl. set_solver. }
  { iExactEq "Hg". f_equal. }
  iDestruct "H" as "(#Hdom&#Hput&#Hcput&#Hget&#Hmove&#Hinstall&#Hfresh&_)".

  set (Γsrv := {| rpc_gn := γrpc; urpc_gn := γ; kv_gn := γkv |}).
  iAssert (is_shard_server host Γsrv) as "Hshard".
  {
    rewrite is_shard_server_unfold /is_shard_server_pre.
    iSplitL.
    { iFrame "#Hown". }
    iSplitL. { iFrame "Hput". }
    iSplitL. { iFrame "Hcput". }
    iSplitL. { iFrame "Hget". }
    iSplitL. { iFrame "Hmove". }
    iSplitL. { iFrame "Hinstall". }
    iFrame "Hfresh".
  }
  iExists Γsrv. iFrame "# ∗".
  eauto.
Qed.

End memkv_shard_ghost_init_proof.
