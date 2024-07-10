From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.grove_prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.ctrexample Require Import interface server client.
From Perennial.program_proof Require Import marshal_proof.
From Goose.github_com.mit_pdos.gokv Require Import ctrexample.client.
From Goose.github_com.mit_pdos.gokv Require Import ctrexample.server.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.ctrexample Require Import wpc_proofmode.
From Perennial.base_logic Require Import lib.ghost_map lib.saved_spec.

From Perennial.goose_lang Require adequacy dist_adequacy.
From Perennial.goose_lang.ffi.grove_ffi Require adequacy.

Section ctr_ghost_init.
Context `{!gooseGlobalGS Σ, !inG Σ mono_natUR, !urpcregG Σ}.

Lemma ctr_ghost_init (γ : gname) :
  localhost c↦ ∅ ={⊤}=∗
  ∃ γurpc_gn,
    is_CtrServer_urpc γurpc_gn γ.
Proof.
  iIntros "Hchan".
  unfold is_CtrServer_urpc.
(*
  iMod (map_alloc_ro (spec_rpcid hd) γsave
          with "Hmap_ctx") as "(Hmap_ctx&#Hsaved_name)"; auto.

  iMod (saved_spec_alloc (RPCSpec_Spec hd)) as (γsave) "#Hsaved".
  iMod (handler_is_init_list localhost (shard_SpecList γkv γrpc) with "[Hg]") as (γ) "H". *)
Admitted.

End ctr_ghost_init.

Section closed_proof.

Import goose_lang.adequacy dist_adequacy grove_ffi.adequacy.

Definition cfg σserver σclient :=
    [
       {|
         dist_lang.init_restart := server.main #();
         dist_lang.init_thread := server.main #();
         dist_lang.init_local_state := σserver;
       |} ;
       {|
         dist_lang.init_restart := client.main #();
         dist_lang.init_thread := client.main #();
         dist_lang.init_local_state := σclient;
       |}
        ].

Lemma wpd_theorem {Σ} {hG:gooseGlobalGS Σ} σserver σclient g :
  ffi_initgP g →
  ffi_initP σserver.(world) g →
  ⊢ wpd (interp:=grove_interp)⊤ (cfg σserver σclient)
.
Proof.
  intros.
  iStartProof.
  unfold wpd.
  unfold cfg.
  iSplitL "".
  {
    simpl. (* client *)
    admit.
  }
  iSplitL "".
  {
    simpl. (* client *)
    admit.
  }
  done.
Admitted.

Definition ctrΣ := #[urpcregΣ].

Lemma closed_theorem σserver σclient σglobal :
  ffi_initgP σglobal.(global_world) →
  ffi_initP σserver.(world) σglobal.(global_world) →
  ffi_initP σclient.(world) σglobal.(global_world) →
  dist_adequacy.dist_adequate (CS:=goose_crash_lang) (* FIXME: crash semantics *)
    (cfg σserver σclient)
    σglobal
    (λ _, True)
.
Proof.
  intros.
  eapply (goose_dist_adequacy ctrΣ); eauto.
  { simpl. intros σ Helem. set_unfold. naive_solver. }
  intros.
  iStartProof.
  iIntros "Hnet_init".
  iEval (rewrite /ffi_global_start /=) in "Hnet_init".

  (* allocate ghost state for counter *)

  iSplitR ""; last first.
  {
    iModIntro. iIntros. iApply fupd_mask_intro.
    { done. }
    iIntros.
    done.
  }
  by iApply wpd_theorem.
Admitted.

End closed_proof.
