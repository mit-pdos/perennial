From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.grove_prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Export ffi.grove_filesys_axioms.
From Perennial.program_proof.ctrexample Require Import interface.
From Perennial.program_proof Require Import marshal_proof.
From Goose.github_com.mit_pdos.gokv Require Import ctrexample.client.
From Goose.github_com.mit_pdos.gokv Require Import ctrexample.server.
From Perennial.program_proof.memkv Require Import rpc_proof.
From Perennial.program_proof.ctrexample Require Import wpc_proofmode.

From Perennial.goose_lang Require adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require grove_ffi_adequacy.


Section closed_proof.

Import adequacy dist_adequacy grove_ffi_adequacy.

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

Definition ctrΣ := #[rpcregΣ].

Lemma closed_theorem σserver σclient σglobal :
  ffi_initgP σglobal →
  ffi_initP σserver.(world) σglobal →
  ffi_initP σclient.(world) σglobal →
  dist_adequacy.dist_adequate (CS:=goose_crash_lang) (* FIXME: crash semantics *)
    (cfg σserver σclient)
    σglobal
    (λ _, True)
.
Proof.
  intros.
  eapply (goose_dist_adequacy ctrΣ); eauto.
  intros.
  iStartProof.
  iIntros "Hglobal_init".
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
