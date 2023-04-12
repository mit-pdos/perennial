From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_protocol.
From Perennial.goose_lang.lib Require Import waitgroup.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_increasecommit_proof.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section pb_sendcommitthread_proof.

Context `{!heapGS Σ}.
Context {pb_record:Sm.t}.
Notation OpType := (pb_record.(Sm.OpType)).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).
Notation "server.t" := (server.t (pb_record:=pb_record)).
Notation pbG := (pbG (pb_record:=pb_record)).
Notation get_rwops := (get_rwops (pb_record:=pb_record)).

Context `{!pbG Σ}.

Lemma wp_Server__increaseCommitThread (s:loc) γ γsrv :
  {{{
        "#Hsrv" ∷ is_Server s γ γsrv
  }}}
    pb.Server__sendIncreaseCommitThread #s
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (?) "Hsrv HΦ".
  iNamed "Hsrv". iNamed "Hsrv".
  wp_call.
  wp_forBreak.
  wp_pures.

  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  wp_pures.
  wp_forBreak_cond.
  iNamed "Hown".
  iNamed "Hvol".
  wp_pures.
  wp_loadField.
  wp_if_destruct.
  { (* not the primary; wait and try again later *)
    wp_pures.
    wp_loadField.
    wp_apply (wp_condWait with "[- HΦ]").
    {
      iFrame "# Hlocked".
      repeat iExists _; iSplitR "HghostEph"; last iFrame.
      repeat iExists _. iFrame "∗#". done.
    }
    iIntros "[Hlocked Hown]".
    wp_pures.
    iLeft. iModIntro.
    eauto with iFrame.
  }
  (* we are the primary, so can send out the new commit index to backups *)
  iRight.
  iModIntro. iSplitR; first done.
  wp_pures.
  wp_loadField.
  wp_pures.

  (* This part is just like Apply() *)
Admitted.

End pb_sendcommitthread_proof.
