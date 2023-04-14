From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export clerk.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_apply_proof pb_makeclerk_proof.
From Perennial.program_proof.simplepb Require Import clerk_proof.

Section prophetic_read_proof.
Context `{!heapGS Σ}.
Context {pb_record:Sm.t}.

Notation OpType := (Sm.OpType pb_record).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).
Notation is_pb_Clerk := (pb_definitions.is_Clerk (pb_record:=pb_record)).

Context `{!pbG Σ}.
Context `{!config_proof.configG Σ}.

Lemma wp_Clerk__ApplyReadonly γ ck op_sl op (op_bytes:list u8) (Φ:val → iProp Σ) :
has_op_encoding op_bytes op →
own_Clerk ck γ -∗
is_slice_small op_sl byteT 1 op_bytes -∗
((|={⊤∖↑pbN,∅}=> ∃ ops, own_op_log γ ops ∗
  (own_op_log γ ops ={∅,⊤∖↑pbN}=∗
     (∀ reply_sl, is_slice_small reply_sl byteT 1 (compute_reply ops op) -∗
                  is_slice_small op_sl byteT 1 op_bytes -∗
                  own_Clerk ck γ -∗ Φ (slice_val reply_sl)%V)))) -∗
WP clerk.Clerk__ApplyRo #ck (slice_val op_sl) {{ Φ }}.
Proof.
  iIntros (?) "Hck Hsl Hupd".
Qed.

End prophetic_read_proof.
