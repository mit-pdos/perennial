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
Implicit Types ros:gmap nat (gset (list EntryType → iProp Σ)).

Definition own_proposed_reads (γ:gname) (ros:gmap nat (gset (list EntryType → iProp Σ))) : iProp Σ.
Admitted.

Definition is_proposed_read (γ:gname) (idx:nat) (Q:(list EntryType → iProp Σ)) : iProp Σ.
Admitted.

Instance is_proposed_read_pers γ idx Q : Persistent (is_proposed_read γ idx Q).
Admitted.

(* This is a 1/2 fraction *)
Definition own_log (γlog:gname) (σ:list EntryType) : iProp Σ :=
  own γlog (●ML{#1/2} (σ : list (leibnizO EntryType))).

Definition is_log_lb (γlog:gname) (σ:list EntryType) : iProp Σ.
Admitted.

(* Maybe make the fupds non-persistent, and track things more carefully in the
   proof. *)
Definition have_proposed_reads_fupds γlog ros : iProp Σ :=
  [∗ map] idx ↦ rosAtIdx ∈ ros, [∗ set] Q ∈ rosAtIdx,
    □(|={⊤,∅}=> ∃ σ, own_log γlog σ ∗ (own_log γlog σ ={∅,⊤}=∗ □ Q σ))
.

(* Maybe make Q not persistent, and escrow it back to the caller *)
Definition have_completed_reads_Qs ros σ : iProp Σ :=
  [∗ map] idx ↦ rosAtIdx ∈ (filter (λ '(idx, _), idx < length σ) ros), [∗ set] Q ∈ rosAtIdx,
    □ Q (take idx σ)
.

Definition prereadN := nroot .@ "preread".

Definition preread_inv γ γlog γreads : iProp Σ :=
  inv prereadN (
  ∃ σ ros,
  "HpbLog" ∷ own_ghost γ σ ∗
  "Hlog" ∷ own_log γlog σ ∗
  (* For all i < length(σ), the read-op fupds for
   *)
  "HownRos" ∷ own_proposed_reads γreads ros ∗
  "#HreadUpds" ∷ have_proposed_reads_fupds γlog ros ∗
  "#HcompletedRead" ∷ have_completed_reads_Qs ros σ
  )
.

Lemma update_map_fmset idx Q ros γreads :
  own_proposed_reads γreads ros ==∗
  own_proposed_reads γreads (<[ idx := {[ Q ]} ∪ default ∅ (ros !! idx) ]> ros)
.
Proof.
Admitted.

Lemma map_fmset_get_elem idx Q ros γreads :
  Q ∈ default ∅ (ros !! idx) →
  own_proposed_reads γreads ros -∗
  is_proposed_read γreads idx Q
.
Proof.
Admitted.

Lemma own_log_agree γlog σ σ' :
  own_log γlog σ -∗
  own_log γlog σ' -∗
  ⌜σ = σ'⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
  iPureIntro.
  rewrite mono_list_auth_dfrac_op_valid_L in Hvalid.
  by destruct Hvalid as [_ ?].
Qed.

Lemma start_read_step Q γ γlog γreads idx σ :
  idx > length σ →
  £ 1 -∗
  preread_inv γ γlog γreads -∗
  □(|={⊤,∅}=> ∃ σ, own_log γlog σ ∗ (own_log γlog σ ={∅,⊤}=∗ □ Q σ)) -∗
  own_log γlog σ
  ={↑prereadN}=∗
  is_proposed_read γreads idx Q ∗ own_log γlog σ
.
Proof.
  intros Hidx.
  iIntros "Hlc #Hinv #Hupd Hlog_in".
  iInv "Hinv" as "Hown" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hown") as "Hown".
  iNamed "Hown".
  iDestruct (own_log_agree with "Hlog_in Hlog") as %?.
  subst.
  iFrame "Hlog_in".
  iMod (update_map_fmset idx Q with "HownRos") as "HownRos".
  iDestruct (map_fmset_get_elem idx Q with "HownRos") as "#His_read".
  { rewrite lookup_insert. set_solver. }
  iMod ("Hclose" with "[-]"); last done.
  iNext.
  iExists _, _.
  iFrame.
  iSplit.
  {
    iApply (big_sepM_insert_2 with "[] HreadUpds").
    Search "big_sepS_insert".
    iApply (big_sepS_insert_2 with "[] []").
    { done. }
    (* the rest of these fupds follow straightforwardly old have_proposed_reads_fupds *)
    destruct (ros !! idx) as [] eqn:Hlookup.
    {
      iDestruct (big_sepM_lookup with "HreadUpds") as "Hupds".
      { done. }
      iFrame "Hupds".
    }
    by iApply big_sepS_empty.
  }
  (* FIXME: there's no point in using filter... *)
  iApply big_sepM_filter.
  iDestruct (big_sepM_filter with "HcompletedRead") as "HcompletedRead2".
  simpl.
  iApply (big_sepM_insert_2 with "[] HcompletedRead2").
  iIntros (?).
  exfalso.
  lia.
Qed.

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
