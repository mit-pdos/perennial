From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import adequacy recovery_adequacy dist_adequacy.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.

From Perennial.program_proof.memkv Require Export memkv_shard_definitions.

#[local] Set Universe Polymorphism.

Section memkv_shard_ghost_init_proof.

(* These lemmas happen *before* we get node local names (e.g. the gname for memory, crashes etc. *)
Context `{!gooseGlobalGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

(* TODO: duplicating this specs is unfortunate, should try to unify with the set up in shard_definitions *)

Definition shard_SpecList γkv γrpc : plist (pprod u64 RpcSpec) :=
    pcons (ppair (W64 uKV_PUT) (eRPCSpec_uRPC γrpc $ is_shard_server_putSpec γkv))
  $ pcons (ppair (W64 uKV_CONDITIONAL_PUT) (eRPCSpec_uRPC γrpc $ is_shard_server_conditionalPutSpec γkv))
  $ pcons (ppair (W64 uKV_GET) (eRPCSpec_uRPC γrpc $ is_shard_server_getSpec γkv))
  $ pcons (ppair (W64 uKV_MOV_SHARD) (is_shard_server_moveSpec γkv))
  $ pcons (ppair (W64 uKV_INS_SHARD) (eRPCSpec_uRPC γrpc $ is_shard_server_installSpec γkv))
  $ pcons (ppair (W64 uKV_FRESHCID) (is_shard_server_freshSpec γrpc))
  $ pnil.

Lemma shard_server_ghost_init host (γkv : gname) :
  host c↦ ∅ ={⊤}=∗
  ∃ γ, ⌜ γ.(kv_gn) = γkv ⌝ ∗
       is_urpc_dom γ.(urpc_gn) (dom_RpcSpec_list (shard_SpecList (γ.(kv_gn)) (γ.(erpc_gn)))) ∗
       is_shard_server host γ ∗
       own_erpc_pre_server γ.(erpc_gn).
Proof.
  iIntros "Hg".
  iMod (erpc_init_server_ghost) as (γrpc) "Herpc".
  iMod (alloc_is_urpc_list host (shard_SpecList γkv γrpc) with "[Hg]") as (γ) "H".
  { simpl. set_solver. }
  { iExactEq "Hg". f_equal. }
  iDestruct "H" as "(#Hdom&#Hput&#Hcput&#Hget&#Hmove&#Hinstall&#Hfresh&_)".

  set (Γsrv := {| erpc_gn := γrpc; urpc_gn := γ; kv_gn := γkv |}).
  iAssert (is_shard_server host Γsrv) as "Hshard".
  {
    rewrite is_shard_server_unfold /is_shard_server_pre.
    iSplitL. { iFrame "Hput". }
    iSplitL. { iFrame "Hcput". }
    iSplitL. { iFrame "Hget". }
    iSplitL. { iFrame "Hmove". }
    iSplitL. { iFrame "Hinstall". }
    iFrame "Hfresh".
  }
  iExists Γsrv. iFrame "∗#".
  eauto.
Qed.

End memkv_shard_ghost_init_proof.
