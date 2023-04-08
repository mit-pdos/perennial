From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import auth dfrac_agree mono_list csum gset gmap_view.
From Perennial.program_proof.simplepb Require Import pb_protocol.
From Perennial.Helpers Require Import ListSolver.
From Perennial.base_logic Require Import lib.saved_prop.

Section pb_preread_protocol.

Context `{EntryType:Type}.

Class pb_prereadG Σ :=
  {
    preread_pb_ghostG :> pb_ghostG (EntryType:=EntryType) Σ ;
    preread_gnameMapG :> inG Σ (authR (gmapUR nat (mono_listR (leibnizO gname)))) ;
    preread_savedG :> savedPredG Σ (list EntryType)
  }.

Context `{invGS Σ}.
Context `{pb_prereadG Σ}.

(* This is the key ghost state, keeping track of RO ops that have been
   pre-applied before state is committed. *)
(* XXX: the "list" of (list EntryType → iProp Σ) is really meant to be a gset,
   but can't have a gset of iProp Σ. *)
Implicit Types ros:gmap nat (list (list EntryType → iProp Σ)).

Definition own_proposed_reads (γ:gname) (ros:gmap nat (list (list EntryType → iProp Σ))) : iProp Σ :=
  ∃ (rosγ:gmap nat (list gname)),
  own γ (●((λ rosγAtIdx, ●ML rosγAtIdx) <$> rosγ) : auth (gmap nat (mono_listR (leibnizO gname)))) ∗
  ([∗ map] idx ↦ rosAtIdx ; rosγAtIdx ∈ ros ; rosγ,
    [∗ list] _ ↦ γprop ; Q ∈ rosγAtIdx ; rosAtIdx, saved_pred_own γprop DfracDiscarded Q)
.

Definition is_proposed_read (γ:gname) (idx:nat) (Q:(list EntryType → iProp Σ)) : iProp Σ :=
  ∃ rosγAtIdx γprop,
  own γ (◯{[ idx := ◯ML rosγAtIdx ]}) ∗
  ⌜γprop ∈ rosγAtIdx⌝ ∗
  saved_pred_own γprop DfracDiscarded Q
.

Instance is_proposed_read_pers γ idx Q : Persistent (is_proposed_read γ idx Q).
Proof. apply _. Qed.

(* This is a 1/2 fraction *)
Definition own_log (γlog:gname) (σ:list EntryType) : iProp Σ :=
  own γlog (●ML{#1/2} (σ : list (leibnizO EntryType))).

Definition is_log_lb (γlog:gname) (σ:list EntryType) : iProp Σ :=
  own γlog (◯ML (σ : list (leibnizO EntryType))).

(* Maybe make the fupds non-persistent, and track things more carefully in the
   proof. *)

Definition prereadN := nroot .@ "preread".

Definition have_proposed_reads_fupds γlog ros : iProp Σ :=
  [∗ map] idx ↦ rosAtIdx ∈ ros, [∗ list] Q ∈ rosAtIdx,
    □(|={⊤∖↑prereadN,∅}=> ∃ σ, own_log γlog σ ∗ (own_log γlog σ ={∅,⊤∖↑prereadN}=∗ □ Q σ))
.

(* Maybe make Q not persistent, and escrow it back to the caller *)
Definition have_completed_reads_Qs ros σ : iProp Σ :=
  [∗ map] idx ↦ rosAtIdx ∈ ros, ⌜idx <= length σ⌝ → [∗ list] Q ∈ rosAtIdx,
    □ Q (take idx σ)
.

Definition preread_inv γ γlog γreads : iProp Σ :=
  inv prereadN (
  ∃ σ ros,
  "HpbLog" ∷ own_ghost γ σ ∗
  "Hlog" ∷ own_log γlog σ ∗
  (* For all i < length(σ), the read-op fupds for *)
  "HownRos" ∷ own_proposed_reads γreads ros ∗
  "#HreadUpds" ∷ have_proposed_reads_fupds γlog ros ∗
  "#HcompletedRead" ∷ have_completed_reads_Qs ros σ
  )
.

Lemma update_map_mset_ipred idx Q ros γreads :
  own_proposed_reads γreads ros ==∗
  own_proposed_reads γreads (<[ idx := (default [] (ros !! idx)) ++ [Q] ]> ros)
.
Proof.
  iIntros "Hown".
  iDestruct "Hown" as (?) "[Hown Hrest]".
  iMod (saved_pred_alloc Q DfracDiscarded) as (γpred) "#Hpred".
  { done. }
  iExists _.
  iMod (own_update with "Hown") as "$".
  {
    instantiate (1:=<[idx:=default [] (ros !! idx) ++ [γpred]]> rosγ ).
    rewrite fmap_insert.
    About auth_update.

    (* FIXME *)
    Need to fix the resource algebra monotonic map of sets of iPredicates.
    Maybe take inspiration from how mono_listR works, by using auth but
    making the mono_list_auth contain an auth and a frag.
    (* ***** *)

    apply auth_update.
    Search gmap_view_auth.
    Search gmapR.
    apply insert_update.
  }
Qed.

Lemma map_fmset_get_elem idx Q ros γreads :
  Q ∈ default ∅ (ros !! idx) →
  own_proposed_reads γreads ros -∗
  is_proposed_read γreads idx Q
.
Proof.
Admitted.

Lemma map_fmset_elem_lookup idx Q ros γreads :
  own_proposed_reads γreads ros -∗
  is_proposed_read γreads idx Q -∗
  ⌜Q ∈ default ∅ (ros !! idx)⌝
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

Lemma own_log_lb_ineq γlog σ σ' :
  own_log γlog σ' -∗
  is_log_lb γlog σ -∗
  ⌜prefix σ σ'⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
  iPureIntro.
  rewrite mono_list_both_dfrac_valid_L in Hvalid.
  by destruct Hvalid as [_ ?].
Qed.

Lemma start_read_step Q γ γlog γreads idx σ :
  idx >= length σ →
  £ 1 -∗
  preread_inv γ γlog γreads -∗
  □(|={⊤∖↑prereadN,∅}=> ∃ σ, own_log γlog σ ∗ (own_log γlog σ ={∅,⊤∖↑prereadN}=∗ □ Q σ)) -∗
  own_commit γ σ
  ={⊤}=∗
  is_proposed_read γreads idx Q ∗ own_commit γ σ
.
Proof.
  intros Hidx.
  iIntros "Hlc #Hinv #Hupd Hlog_in".
  iInv "Hinv" as "Hown" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hown") as "Hown".
  iNamed "Hown".
  iDestruct (own_log_agree with "Hlog_in HpbLog") as %?.
  subst.
  iFrame "Hlog_in".

  (* we'll fire the fupd here for the case that idx = length σ, and later might
     decide to throw away the Q *)
  iAssert (_) with "Hupd" as "Hupd2".
  iMod "Hupd2" as (?) "[Hlog2 Hupd2]".
  iDestruct (own_log_agree with "Hlog2 Hlog") as %?.
  subst.
  iMod ("Hupd2" with "Hlog2") as "#?".

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
    iApply (big_sepS_insert_2 with "[] []").
    { done. }
    (* the rest of these fupds follow straightforwardly from old have_proposed_reads_fupds *)
    destruct (ros !! idx) as [] eqn:Hlookup.
    {
      iDestruct (big_sepM_lookup with "HreadUpds") as "Hupds".
      { done. }
      iFrame "Hupds".
    }
    { by iApply big_sepS_empty. }
  }
  simpl.
  iApply (big_sepM_insert_2 with "[] HcompletedRead").
  iIntros (?).
  destruct (decide (idx = length σ0)).
  {
    subst.
    iApply big_sepS_union_2.
    {
      iApply big_sepS_singleton.
      iModIntro.
      by rewrite firstn_all.
    }
    (* again, the rest of these follow from the previous Q's. *)
    destruct (ros !! (length σ0)) as [] eqn:Hlookup.
    {
      iDestruct (big_sepM_lookup with "HcompletedRead") as "Hupds".
      { done. }
      by iApply "Hupds".
    }
    by iApply big_sepS_empty.
  }
  exfalso.
  lia.
Qed.

Lemma finish_read_step Q γ γlog γreads idx σ :
  length σ = idx →
  £ 1 -∗
  preread_inv γ γlog γreads -∗
  is_log_lb γlog σ -∗
  is_proposed_read γreads idx Q
  ={↑prereadN}=∗
  □ Q σ
.
Proof.
  iIntros (Hlen) "Hlc #Hinv #Hlb #Hro".
  iInv "Hinv" as "Hown" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hown") as "Hown".
  iNamed "Hown".
  iDestruct (own_log_lb_ineq with "Hlog Hlb")as %Hprefix.
  iDestruct (map_fmset_elem_lookup with "HownRos Hro") as %HQelem.
  destruct (ros !! idx) as [] eqn:Hlookup; last by exfalso.
  simpl in HQelem.
  iDestruct (big_sepM_lookup with "HcompletedRead") as "H".
  { done. }
  iSpecialize ("H" with "[%]").
  { subst. by apply prefix_length. }
  iDestruct (big_sepS_elem_of with "H") as "H2".
  { done. }
  iMod ("Hclose" with "[-]").
  { iExists _, _; iFrame "∗#". }
  iModIntro.
  iExactEq "H2".
  repeat f_equal.
  (* TODO: list_solver *)
  subst.
  destruct Hprefix as []; subst.
  apply take_app.
Qed.

(*
Lemma propose_rw_op_valid op γ γlog γreads :
  £ 1 -∗
  preread_inv γ γlog γreads -∗
  □(|={⊤∖↑prereadN,∅}=> ∃ σ, own_log γlog σ ∗ (own_log γlog (σ ++ [op]) ={∅,⊤∖↑prereadN}=∗ True))
  ={↑prereadN}=∗
  (|={⊤∖↑ghostN,∅}=> ∃ someσ, own_ghost γ someσ ∗ (⌜someσ = σ⌝ -∗ own_ghost γ (someσ ++ [op]) ={∅,⊤∖↑ghostN}=∗ True))
.
Proof. *)

End pb_preread_protocol.
