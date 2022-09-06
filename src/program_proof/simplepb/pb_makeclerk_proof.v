From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.simplepb Require Import pb_definitions.

Section pb_makeclerk_proof.
Context `{!heapGS Σ, !stagedG Σ}.
Context {pb_record:PBRecord}.

Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_snap_encoding := (pb_has_snap_encoding pb_record).
Notation has_op_encoding_injective := (pb_has_op_encoding_injective pb_record).
Notation compute_reply := (pb_compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).

Context `{!waitgroupG Σ}.
Context `{!pbG Σ}.

Lemma wp_MakeClerk γ γsrv host :
{{{
      is_pb_host host γ γsrv
}}}
  MakeClerk #host
{{{
      (ck:loc), RET #ck; is_Clerk ck γ γsrv
}}}.
Proof.
Admitted.

End pb_makeclerk_proof.
