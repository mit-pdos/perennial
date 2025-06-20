From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import adequacy recovery_adequacy dist_adequacy.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.

From Perennial.program_proof.memkv Require Export memkv_shard_definitions memkv_coord_definitions.

#[local] Set Universe Polymorphism.

Section memkv_coord_ghost_init_proof.

(* These lemmas happen *before* we get node local names (e.g. the gname for memory, crashes etc. *)
Context `{!gooseGlobalGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

Definition coord_SpecList γkv : plist (pprod u64 RpcSpec) :=
  pcons (ppair (W64 uCOORD_ADD) (is_coord_server_addSpec γkv))
  $ pcons (ppair (W64 uCOORD_GET) (is_coord_server_getSpec γkv))
  $ pnil.

Lemma coord_server_ghost_init host (γkv : gname) :
  host c↦ ∅ ={⊤}=∗
  ∃ γ, ⌜ γ.(coord_kv_gn) = γkv ⌝ ∗
       is_urpc_dom γ.(coord_urpc_gn) (dom_RpcSpec_list (coord_SpecList (γ.(coord_kv_gn)))) ∗
       is_coord_server host γ.
Proof.
  iIntros "Hg".
  iMod (alloc_is_urpc_list host (coord_SpecList γkv) with "[Hg]") as (γ) "H".
  { simpl. set_solver. }
  { iExactEq "Hg". f_equal. }
  iDestruct "H" as "(#Hdom&#Hadd&#Hget&_)".

  set (Γsrv := {| coord_urpc_gn := γ; coord_kv_gn := γkv |}).
  iAssert (is_coord_server host Γsrv) as "Hcoord".
  {
    iSplitL. { iFrame "Hadd". }
    iFrame "Hget".
  }
  iExists Γsrv. iFrame "∗#".
  eauto.
Qed.

End memkv_coord_ghost_init_proof.
