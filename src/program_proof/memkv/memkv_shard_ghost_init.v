From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import adequacy recovery_adequacy dist_adequacy.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.

From Perennial.program_proof.memkv Require Export memkv_shard_definitions.

Section memkv_shard_ghost_init_proof.

(* These lemmas happen *before* we get node local names (e.g. the gname for memory, crashes etc. *)
Context `{!gooseGlobalGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

(* TODO: duplicating this specs is unfortunate, should try to unify with the set up in shard_definitions *)

Definition shard_SpecList γkv γrpc : uRPCSpecList :=
  spec_cons (eRPCSpec_uRPC γrpc $ is_shard_server_putSpec γkv)
    (spec_cons (eRPCSpec_uRPC γrpc $ is_shard_server_conditionalPutSpec γkv)
      (spec_cons (eRPCSpec_uRPC γrpc $ is_shard_server_getSpec γkv)
        (spec_cons (is_shard_server_moveSpec γkv)
          (spec_cons (eRPCSpec_uRPC γrpc $ is_shard_server_installSpec γkv)
            (spec_cons (is_shard_server_freshSpec γrpc) spec_nil))))).

Lemma shard_server_ghost_init host (γkv : gname) :
  host c↦ ∅ ={⊤}=∗
  ∃ γ, ⌜ γ.(kv_gn) = γkv ⌝ ∗
       handlers_dom γ.(urpc_gn) (dom_uRPCSpecList (shard_SpecList (γ.(kv_gn)) (γ.(erpc_gn)))) ∗
       is_shard_server host γ ∗
       own_erpc_pre_server γ.(erpc_gn).
Proof.
  iIntros "Hg".
  iMod (erpc_init_server_ghost) as (γrpc) "Herpc".
  iMod (handler_is_init_list host (shard_SpecList γkv γrpc) with "[Hg]") as (γ) "H".
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
  iExists Γsrv. iFrame "# ∗".
  eauto.
Qed.

End memkv_shard_ghost_init_proof.
