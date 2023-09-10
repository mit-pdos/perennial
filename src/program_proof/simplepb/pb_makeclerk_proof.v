From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_definitions.
From Perennial.program_proof.reconnectclient Require Import proof.

Section pb_makeclerk_proof.
Context `{!heapGS Σ}.
Context {params:pbParams.t}.
Import pbParams.

Notation OpType := (Sm.OpType pb_record).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).

Context `{!waitgroupG Σ}.
Context `{!pbG Σ}.

Lemma wp_MakeClerk γ γsrv host :
{{{
      is_pb_rpcs host γ γsrv
}}}
  MakeClerk #host
{{{
      (ck:loc), RET #ck; is_Clerk ck γ γsrv
}}}.
Proof.
  iIntros (Φ) "#Hpb HΦ".
  wp_call.
  wp_apply (wp_MakeReconnectingClient).
  iIntros (?) "#His_cl".
  iApply wp_fupd.
  wp_apply (wp_allocStruct).
  { eauto. }
  iIntros (ck) "Hck".
  iDestruct (struct_fields_split with "Hck") as "HH".
  iNamed "HH".
  iMod (readonly_alloc_1 with "cl") as "#Hcl".
  iApply "HΦ".
  iModIntro.
  repeat iExists _.
  iFrame "#".
Qed.

End pb_makeclerk_proof.
