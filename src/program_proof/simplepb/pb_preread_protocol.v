From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import auth dfrac_agree mono_list csum gset.
From Perennial.program_proof.simplepb Require Import pb_ghost.

Section pb_preread_protocol.
(* Use (authR gsetR) for monotonic sets. *)

Context `{EntryType:Type}.
Context `{pb_ghostG EntryType Σ}.
Context `{invGS Σ}.

(* FIXME: this is not actually countable. This is a requirement from gset, but
   feels like it shouldn't really be needed. We can make do by having a list
   instead of gset, and ignore the ordering.
 *)
Context `{Countable (list EntryType → iProp Σ)}.

(* This is the key ghost state, keeping track of RO ops that have been
   pre-applied before state is committed. *)
Implicit Types ros:list (gset (list EntryType → iProp Σ)).

Definition own_proposed_reads (γ:gname) (ros:list (gset (list EntryType → iProp Σ))) : iProp Σ.
Admitted.

Definition is_proposed_read (γ:gname) (idx:nat) (Q:(list EntryType → iProp Σ)) : iProp Σ.
Admitted.

Definition own_log (γlog:gname) (σ:list EntryType) : iProp Σ.
Admitted.

Definition is_log_lb (γlog:gname) (σ:list EntryType) : iProp Σ.
Admitted.

(* Maybe make the fupds non-persistent, and track things more carefully in the
   proof. *)
Definition have_proposed_reads_fupds γlog ros : iProp Σ :=
  [∗ list] idx ↦ rosAtIdx ∈ ros, [∗ set] Q ∈ rosAtIdx,
    □(|={⊤,∅}=> ∃ σ, own_log γlog σ ∗ (own_log γlog σ ={∅,⊤}=∗ □ Q σ))
.

(* Maybe make Q not persistent, and escrow it back to the caller *)
Definition have_completed_reads_Qs ros σ : iProp Σ :=
  let completed_ros := take (length σ) ros in
  [∗ list] idx ↦ rosAtIdx ∈ completed_ros, [∗ set] Q ∈ rosAtIdx,
    □ Q (take idx σ)
.

Definition prereadN := nroot .@ "preread".

Definition preread_inv γ γlog γreads : iProp Σ :=
  inv prereadN (
  ∃ σ ros,
  own_ghost γ σ ∗
  own_log γlog σ ∗
  (* For all i < length(σ), the read-op fupds for
   *)
  own_proposed_reads γreads ros ∗
  have_proposed_reads_fupds γlog ros ∗
  have_completed_reads_Qs ros σ
  )
.

Lemma start_read_step Q γ γlog γreads idx σ :
  idx < length σ →
  preread_inv γ γlog γreads -∗
  □(|={⊤,∅}=> ∃ σ, own_log γlog σ ∗ (own_log γlog σ ={∅,⊤}=∗ □ Q σ)) -∗
  own_log γlog σ
  ={↑prereadN}=∗
  is_proposed_read γreads idx Q ∗ own_log γlog σ
.
Proof.
Admitted.

Lemma finish_read_step Q γ γlog γreads idx σ :
  length σ = idx →
  preread_inv γ γlog γreads -∗
  is_log_lb γlog σ -∗
  is_proposed_read γreads idx Q
  ={↑prereadN}=∗
  □ Q σ
.
Proof.
Admitted.

End pb_preread_protocol.
