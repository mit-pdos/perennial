From Perennial.base_logic Require Import lib.saved_prop.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Export pb_ghost.
From Perennial.program_proof.simplepb Require Import pb_definitions.
From Perennial.program_proof.grove_shared Require Import urpc_spec.
From iris.algebra Require Import mono_list.

Section pb_init_proof.

Context {pb_record:PBRecord}.
Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_snap_encoding := (pb_has_snap_encoding pb_record).
Notation compute_reply := (pb_compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).
Context `{!gooseGlobalGS Σ}.
Context `{!pbG Σ}.

Lemma pb_server_init γsys γsrv :
  is_sys_init_witness γsys -∗
  own_server_pre γsrv -∗
  own_Server_ghost γsys γsrv (U64 0) [] false.
Proof.
  iIntros "#H1 Hpre".
  iDestruct (pb_ghost_server_init with "H1 Hpre") as "[Hrep Hprim]".
  iExists [].
  iSplitR; first done.
  iFrame.
Qed.

Definition pb_spec_list γsys γsrv :=
  [ (U64 0, ApplyAsBackup_spec γsys γsrv) ;
    (U64 1, SetState_spec γsys γsrv) ;
    (U64 2, GetState_spec γsys γsrv) ;
    (U64 3, BecomePrimary_spec γsys γsrv);
    (U64 4, Apply_spec γsys) ].

Lemma pb_host_init host γsys γsrv :
  host c↦ ∅ ={⊤}=∗
  is_pb_host host γsys γsrv.
Proof.
  iIntros "Hchan".
  iMod (handler_is_init_list2 host (pb_spec_list γsys γsrv) with "Hchan") as (γrpc) "H".
  { simpl. set_solver. }
  iModIntro.
  rewrite is_pb_host_unfold.
  iExists γrpc.
  simpl.
  iDestruct "H" as "(H1 & $ & $ & $ & $ & $ & _)".
  iExactEq "H1".
  f_equal.
  set_solver.
Qed.

Lemma pb_init_log γsys :
  own_ghost γsys [] ={⊤}=∗
  ∃ γlog, own_log γlog [] ∗ is_inv γlog γsys
.
Proof.
  iIntros "Hghost".
  iMod (own_alloc (●ML [])) as (γlog) "[Hlog1 Hlog2]".
  { apply mono_list_auth_valid. }
  iExists _; iFrame "Hlog2".
  iMod (inv_alloc with "[-]") as "$"; last done.
  iNext.
  iExists [].
  iFrame.
  iSplitL.
  {
    iExists [].
    iFrame.
    iSplitR; first done.
    iApply big_sepL2_nil.
    done.
  }
  iModIntro.
  iIntros.
  exfalso.
  rewrite H0 in H.
  apply prefix_nil_inv in H.
  apply (f_equal length) in H.
  rewrite app_length /= in H.
  lia.
Qed.

End pb_init_proof.
