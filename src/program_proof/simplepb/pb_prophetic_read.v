From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export clerk.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_apply_proof pb_makeclerk_proof.
From Perennial.program_proof.simplepb Require Import clerk_proof proph_proof.

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

Record proph_req_names :=
{
  op_gn:gname;
  finish_gn:gname;
}.

Implicit Types γreq : proph_req_names.

Context `{inG Σ dfracR}.

Definition operation_incomplete γreq : iProp Σ := own γreq.(op_gn) (DfracOwn 1).
Definition operation_receipt γreq : iProp Σ := own γreq.(op_gn) (DfracDiscarded).

Lemma complete_operation γreq :
  operation_incomplete γreq ==∗ operation_receipt γreq.
Proof.
  iIntros "H1".
  iApply (own_update with "H1").
  apply (cmra_update_exclusive).
  done.
Qed.

Definition result_claimed γreq : iProp Σ := own γreq.(finish_gn) (DfracOwn 1).
Definition result_unclaimed γreq : iProp Σ := own γreq.(finish_gn) (DfracOwn 1).

Definition read_fupd γ readOp (Q:list u8 → iProp Σ) : iProp Σ :=
(|={⊤∖↑pbN,∅}=> ∃ ops, own_op_log γ ops ∗
  (own_op_log γ ops ={∅,⊤∖↑pbN}=∗ Q (compute_reply ops readOp))).

Definition prophReadN := nroot .@ "prophread".

Definition prophetic_read_inv prophV γ γreq readOp Φ : iProp Σ :=
  inv prophReadN (
        (*
          XXX: This invariant is a bit ad-hoc. A more principled approach would be to
          give the server a fraction of the ghost resources for the "state" of
          this protocol at the beginning of time, and for this invariant to have
          only a fraction of it.
        *)
  operation_incomplete γreq ∗ read_fupd γ readOp Φ ∨
  operation_receipt γreq ∗ ((Φ prophV) ∨ result_claimed γreq))
.

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
  wp_call.
  wp_apply (wp_NewProphBytes).
  iIntros (??) "Hproph".
  wp_pures.
  iAssert (|={⊤}=> ∃ γreq, result_unclaimed γreq ∗ prophetic_read_inv b γ γreq _
  (λ reply, ∀ reply_sl : Slice.t,
             is_slice_small reply_sl byteT 1 reply -∗
             is_slice_small op_sl byteT 1 op_bytes -∗ own_Clerk ck γ -∗ Φ (slice_val reply_sl))
          )%I with "[Hupd]" as ">H".
  {
    iMod (own_alloc (DfracOwn 1)) as (γop) "Hop".
    { done. }
    iMod (own_alloc (DfracOwn 1)) as (γfinish) "Hfinish".
    { done. }
    iExists {| op_gn := γop ; finish_gn := γfinish |}.
    iFrame. iMod (inv_alloc with "[-]") as "$"; last done.
    iNext. iLeft. iFrame "Hop ∗".
  }
  iDestruct "H" as (?) "[Hfinish #Hinv]".
  wp_bind (Clerk__ApplyRo2 _ _).
  wp_apply (wp_frame_wand with "[Hproph Hfinish]").
  { iNamedAccu. }
  wp_apply (wp_Clerk__ApplyReadonly2 with "Hck Hsl []").
  { done. }
  iModIntro.
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as "[Hnotdone|Hdone]".
  2:{ (* case: one of the low-level uRPC requests already fired the fupd before. *)
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iRight.
    iIntros (?) "_". iMod "Hmask".
    iDestruct "Hdone" as "[#>? ?]".
    iMod ("Hclose" with "[-]").
    { iRight. iFrame "∗#". }
    iModIntro.
    iModIntro.
    iIntros (?) "Hrep_sl Hop_sl Hck".
    iNamed 1.
    wp_pures.
    wp_apply (wp_ResolveBytes with "Hproph").
Qed.

End prophetic_read_proof.
