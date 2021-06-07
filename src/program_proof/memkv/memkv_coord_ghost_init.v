From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import adequacy recovery_adequacy dist_adequacy.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.

From Perennial.program_proof.memkv Require Export memkv_shard_definitions memkv_coord_definitions.

Section memkv_coord_ghost_init_proof.

(* These lemmas happen *before* we get node local names (e.g. the gname for memory, crashes etc. *)
Context `{!heap_globalG Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Existing Instance global_groveG.

Definition coord_SpecList γkv : RPCSpecList :=
  spec_cons (is_coord_server_addSpec γkv)
    (spec_cons (is_coord_server_getSpec γkv) spec_nil).

Lemma coord_server_ghost_init host (γkv : gname) :
  host c↦ ∅ ={⊤}=∗
  ∃ γ, ⌜ γ.(coord_kv_gn) = γkv ⌝ ∗
       handlers_dom γ.(coord_urpc_gn) (dom_RPCSpecList (coord_SpecList (γ.(coord_kv_gn)))) ∗
       is_coord_server host γ.
Proof.
  iIntros "Hg".
  iMod (handler_is_init_list host (coord_SpecList γkv) with "[Hg]") as (γ) "H".
  { simpl. set_solver. }
  { iExactEq "Hg". f_equal. }
  iDestruct "H" as "(#Hdom&#Hadd&#Hget&_)".

  set (Γsrv := {| coord_urpc_gn := γ; coord_kv_gn := γkv |}).
  iAssert (is_coord_server host Γsrv) as "Hcoord".
  {
    iSplitL. { iFrame "Hadd". }
    iFrame "Hget".
  }
  iExists Γsrv. iFrame "# ∗".
  eauto.
Qed.

End memkv_coord_ghost_init_proof.
