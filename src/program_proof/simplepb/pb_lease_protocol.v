From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import auth dfrac_agree mono_list csum gset.
From Perennial.program_proof.simplepb Require Import pb_ghost.

Section pb_lease_protocol.
(* Use (authR gsetR) for monotonic sets. *)

Context `{EntryType:Type}.
Context `{pb_ghostG EntryType Σ}.
Context `{invGS Σ}.

(* FIXME: this is not actually countable. This is a requirement from gset, but
   feels like it shouldn't really be needed. We can make do by having a list
   instead of gset, and ignore the ordering.
 *)
Context `{Countable (list EntryType → iProp Σ)}.
(*
 *)

Implicit Types ros:list (gset (list EntryType → iProp Σ)).
Definition own_proposed_reads (γ:gname) (ros:list (gset (list EntryType → iProp Σ))) : iProp Σ.
Admitted.

Definition is_proposed_read (γ:gname) (idx:nat) (Q:(list EntryType → iProp Σ)) : iProp Σ.
Admitted.

Definition own_log (γlog:gname) (σ:list EntryType) : iProp Σ.
Admitted.

Definition have_proposed_reads_fupds γlog ros : iProp Σ :=
  [∗ list] idx ↦ rosAtIdx ∈ ros, [∗ set] Q ∈ rosAtIdx,
    □(|={⊤,∅}=> ∃ σ, own_log γlog σ ∗ (own_log γlog σ ={∅,⊤}=∗ □ Q σ))
.

Definition have_completed_reads_Qs ros σ : iProp Σ :=
  let completed_ros := take (length σ) ros in
  [∗ list] idx ↦ rosAtIdx ∈ completed_ros, [∗ set] Q ∈ rosAtIdx,
    Q (take (idx + 1) σ)
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

Lemma prepare_read Q γ γlog γreads idx σ :
  idx < length σ →
  preread_inv γ γlog γreads -∗
  □(|={⊤,∅}=> ∃ σ, own_log γlog σ ∗ (own_log γlog σ ={∅,⊤}=∗ □ Q σ)) -∗
  own_log γlog σ
  ={↑prereadN}=∗
  is_proposed_read γreads idx Q ∗ own_log γlog σ
.
Proof.
Admitted.

End pb_lease_protocol.
