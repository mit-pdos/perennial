From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import auth dfrac_agree mono_list csum gset gmap_view.
From Perennial.program_proof.simplepb Require Import pb_protocol.
From Perennial.Helpers Require Import ListSolver.
From Perennial.base_logic Require Import lib.saved_prop.

Section pb_preread_protocol.

Class pb_prereadG `{EntryType:Type} Σ :=
  {
    preread_pb_ghostG :> pb_ghostG (EntryType:=EntryType) Σ ;
    preread_gnameMapG :> inG Σ (authR (gmapUR nat (mono_listR (leibnizO gname)))) ;
    preread_savedG :> savedPredG Σ (list EntryType)
  }.

Context `{!gooseGlobalGS Σ}.
Context `{pb_prereadG EntryType Σ}.

(* This is the key ghost state, keeping track of RO ops that have been
   pre-applied before state is committed. *)
(* XXX: the "list" of (list EntryType → iProp Σ) is really meant to be a gset,
   but can't have a gset of iProp Σ. *)
Implicit Types ros:gmap nat (list (list EntryType → iProp Σ)).

Definition own_proposed_reads (γ:gname) (ros:gmap nat (list (list EntryType → iProp Σ))) : iProp Σ :=
  ∃ (rosγ:gmap nat (list gname)),
  own γ (●((λ (rosγAtIdx:list gname), ●ML rosγAtIdx) <$> rosγ) : auth (gmap nat (_))) ∗
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
Definition own_pre_log (γlog:gname) (σ:list EntryType) : iProp Σ :=
  own γlog (●ML{#1/2} (σ : list (leibnizO EntryType))).

Definition is_pre_log_lb (γlog:gname) (σ:list EntryType) : iProp Σ :=
  own γlog (◯ML (σ : list (leibnizO EntryType))).

(* Maybe make the fupds non-persistent, and track things more carefully in the
   proof. *)

Definition prereadN := pbN .@ "preread".

(*
Definition have_proposed_reads_fupds γlog ros : iProp Σ :=
  [∗ map] idx ↦ rosAtIdx ∈ ros, [∗ list] Q ∈ rosAtIdx,
    □(|={⊤∖↑prereadN,∅}=> ∃ σ, own_pre_log γlog σ ∗ (own_pre_log γlog σ ={∅,⊤∖↑prereadN}=∗ □ Q σ))
. *)

Definition have_proposed_reads_fupds_parallel γlog ros : iProp Σ :=
  (* rather than having a set of fupds at each readIndex (one for each read done
     at that index), this has one big fupds that does all the reads at once.
     Intended to be a bit more convenient in the proof. *)
  [∗ map] idx ↦ rosAtIdx ∈ ros,
    □(∀ σ, own_pre_log γlog σ ={⊤∖↑prereadN∖↑ghostN}=∗ own_pre_log γlog σ ∗ [∗ list] Q ∈ rosAtIdx, □ Q σ)
.

(* Maybe make Q not persistent, and escrow it back to the caller *)
Definition have_completed_reads_Qs ros σ : iProp Σ :=
  [∗ map] idx ↦ rosAtIdx ∈ ros, ⌜idx <= length σ⌝ → [∗ list] Q ∈ rosAtIdx,
    □ Q (take idx σ)
.

Definition preread_inv γ γlog γreads : iProp Σ :=
  inv prereadN (
  ∃ σ ros,
  "HpbLog" ∷ own_pb_log γ σ ∗
  "Hlog" ∷ own_pre_log γlog σ ∗
  (* For all i < length(σ), the read-op fupds for *)
  "HownRos" ∷ own_proposed_reads γreads ros ∗
  "#HreadUpds" ∷ have_proposed_reads_fupds_parallel γlog ros ∗
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
    eapply auth_update_auth.

    destruct (rosγ !! idx) as [] eqn:Hlookup.
    {
      eapply insert_alloc_local_update.
      { rewrite lookup_fmap /=.
        by rewrite Hlookup.
      }
      { done. }
      intros ?. intros.
      simpl in *.
      split.
      { apply mono_list_auth_validN. }
      edestruct ((ros:gmap _ _) !! idx) as [] eqn:Hlookup2.
      { simpl.
        (* This is too deep a rabbit hole. If this is the only way to do this
           using the resources set up, will switch to another gname indirection
           instead. *)
Admitted.

Lemma map_fmset_get_elem idx Q ros γreads :
  Q ∈ default [] (ros !! idx) →
  own_proposed_reads γreads ros -∗
  is_proposed_read γreads idx Q
.
Proof.
Admitted.

Lemma map_fmset_elem_lookup idx Q ros γreads :
  own_proposed_reads γreads ros -∗
  is_proposed_read γreads idx Q -∗
  ⌜Q ∈ default [] (ros !! idx)⌝
.
Proof.
Admitted.

Lemma own_log_agree γlog σ σ' :
  own_pre_log γlog σ -∗
  own_pre_log γlog σ' -∗
  ⌜σ = σ'⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
  iPureIntro.
  rewrite mono_list_auth_dfrac_op_valid_L in Hvalid.
  by destruct Hvalid as [_ ?].
Qed.

Lemma own_log_update_2 γlog σ σ' :
  prefix σ σ' →
  own_pre_log γlog σ -∗
  own_pre_log γlog σ ==∗
  own_pre_log γlog σ' ∗
  own_pre_log γlog σ'
.
Proof.
  iIntros (?) "H1 H2".
  iCombine "H1 H2" as "H".
  iMod (own_update with "H") as "H".
  {
    apply mono_list_update.
    done.
  }
  by iDestruct "H" as "[$ $]".
Qed.

Lemma own_log_lb_ineq γlog σ σ' :
  own_pre_log γlog σ' -∗
  is_pre_log_lb γlog σ -∗
  ⌜prefix σ σ'⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
  iPureIntro.
  rewrite mono_list_both_dfrac_valid_L in Hvalid.
  by destruct Hvalid as [_ ?].
Qed.

Lemma start_read_step Q γ γlog γreads idx σ E :
  ↑prereadN ⊆ E →
  idx >= length σ →
  £ 1 -∗
  preread_inv γ γlog γreads -∗
  □(|={E∖↑prereadN∖↑ghostN,∅}=> ∃ σ, own_pre_log γlog σ ∗ (own_pre_log γlog σ ={∅,E∖↑prereadN∖↑ghostN}=∗ □ Q σ)) -∗
  own_pb_log γ σ
  ={E}=∗
  is_proposed_read γreads idx Q ∗ own_pb_log γ σ
.
Proof.
  intros ? Hidx.
  iIntros "Hlc #Hinv #Hupd Hlog_in".
  iInv "Hinv" as "Hown" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hown") as "Hown".
  iNamed "Hown".
  iDestruct (own_log_agree with "Hlog_in HpbLog") as %?.
  subst.
  iFrame "Hlog_in".

  (* we'll fire the fupd here for the case that idx = length σ, and later might
     decide to throw away the Q *)
  iMod (fupd_mask_subseteq _) as "Hmask".
  { shelve. }
  iAssert (_) with "Hupd" as "Hupd2".
  iMod "Hupd2" as (?) "[Hlog2 Hupd2]".
  iDestruct (own_log_agree with "Hlog2 Hlog") as %?.
  subst.
  iMod ("Hupd2" with "Hlog2") as "#?".
  iMod "Hmask".
  Unshelve. 2: solve_ndisj.

  iMod (update_map_mset_ipred idx Q with "HownRos") as "HownRos".
  iDestruct (map_fmset_get_elem idx Q with "HownRos") as "#His_read".
  { rewrite lookup_insert. set_solver. }
  iMod ("Hclose" with "[-]"); last done.
  iNext.
  iExists _, _.
  iFrame.
  iSplit.
  {
    iApply (big_sepM_insert_2 with "[] HreadUpds").
    iModIntro.

    iIntros (?) "Hlog".

    (* fire the new fupd *)
    iMod (fupd_mask_subseteq (E∖↑prereadN∖↑ghostN)) as "Hmask".
    { solve_ndisj. }
    iMod "Hupd" as (?) "[Hlog2 Hupd]".
    iDestruct (own_log_agree with "Hlog Hlog2") as %?; subst.
    iMod ("Hupd" with "Hlog2") as "#HQ".
    iMod "Hmask" as "_".
    destruct (ros !! idx) as [] eqn:Hlookup.
    { (* have some previous fupds *)
      iDestruct (big_sepM_lookup with "HreadUpds") as "#Hupds".
      { done. }

      (* fire the old fupds *)
      iMod ("Hupds" with "Hlog") as "[Hlog #HQs]".
      iModIntro.
      iFrame.
      simpl.
      iSplitL.
      { iFrame "#". }
      { by iFrame "#". }
    }
    { iModIntro; simpl; iFrame "∗#". }
  }
  simpl.
  iApply (big_sepM_insert_2 with "[] HcompletedRead").
  iIntros (?).
  destruct (decide (idx = length σ0)).
  {
    subst.
    iApply big_sepL_app.
    iSplit.
    2: {
      iApply big_sepL_singleton.
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
    by iApply big_sepL_nil.
  }
  exfalso.
  lia.
Qed.

Lemma finish_read_step Q γ γlog γreads idx σ :
  length σ = idx →
  £ 1 -∗
  preread_inv γ γlog γreads -∗
  is_pb_log_lb γ σ -∗
  is_proposed_read γreads idx Q
  ={↑prereadN}=∗
  □ Q σ
.
Proof.
  iIntros (Hlen) "Hlc #Hinv #Hlb #Hro".
  iInv "Hinv" as "Hown" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hown") as "Hown".
  iNamed "Hown".
  iDestruct (own_log_lb_ineq with "HpbLog Hlb")as %Hprefix.
  iDestruct (map_fmset_elem_lookup with "HownRos Hro") as %HQelem.
  destruct (ros !! idx) as [] eqn:Hlookup.
  2:{ exfalso. by apply elem_of_nil in HQelem. }
  simpl in HQelem.
  iDestruct (big_sepM_lookup with "HcompletedRead") as "H".
  { done. }
  iSpecialize ("H" with "[%]").
  { subst. by apply prefix_length. }
  iDestruct (big_sepL_elem_of with "H") as "H2".
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

(* XXX: for this lemma, want prereadN ∩ pbN = ∅ *)
Lemma propose_rw_op_valid op γ γlog γreads :
  £ 1 -∗
  preread_inv γ γlog γreads -∗
  (|={⊤∖↑ghostN∖↑prereadN,∅}=> ∃ σ, own_pre_log γlog σ ∗ (own_pre_log γlog (σ ++ [op]) ={∅,⊤∖↑ghostN∖↑prereadN}=∗ True))
  -∗
  (|={⊤∖↑ghostN,∅}=> ∃ someσ, own_pb_log γ someσ ∗ (own_pb_log γ (someσ ++ [op]) ={∅,⊤∖↑ghostN}=∗ True))
.
Proof.
  iIntros "Hlc #Hinv Hupd".
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
  iMod "Hupd" as (?) "[Hlog2 Hupd]".
  iDestruct (own_log_agree with "Hlog Hlog2") as "%".
  subst.
  iModIntro.
  iExists _.
  iFrame.
  iIntros "HpbLog".
  iMod (own_log_update_2 _ _ (σ0++[op]) with "Hlog Hlog2") as "[Hlog Hlog2]".
  { by apply prefix_app_r. }

  iMod ("Hupd" with "Hlog2").

  destruct (ros !! (length σ0 + 1)) as [] eqn:Hlookup.
  {
    iDestruct (big_sepM_lookup with "HreadUpds") as "#Hupds".
    { done. }
    iMod (fupd_mask_subseteq _) as "Hmask".
    { shelve. }
    iMod ("Hupds" with "Hlog") as "[Hlog #HQ]".
    iMod "Hmask" as "_".
    Unshelve. 2: solve_ndisj.

    iMod ("Hclose" with "[-]"); last done.
    repeat iExists _; iFrame "∗#%".
    iNext.
    iApply (big_sepM_impl with "HcompletedRead").
    iModIntro. iIntros (???) "H %".
    rewrite app_length /= in H1.
    destruct (decide (k = length σ0 + 1)).
    {
      subst.
      replace (length σ0 + 1) with (length (σ0 ++ [op])).
      2: by rewrite app_length.
      rewrite firstn_all.
      rewrite Hlookup in H0.
      injection H0 as ->.
      iFrame "#".
    }
    rewrite take_app_le; last word.
    iApply "H".
    iPureIntro. word.
  }
  {
    iMod ("Hclose" with "[-]"); last done.
    repeat iExists _; iFrame "∗#%".
    iNext.
    iApply (big_sepM_impl with "HcompletedRead").
    iModIntro. iIntros (???) "H %".
    rewrite app_length /= in H1.
    destruct (decide (k = length σ0 + 1)).
    { exfalso. subst. by rewrite Hlookup in H0. }
    rewrite take_app_le; last word.
    iApply "H".
    iPureIntro. word.
  }
Qed.

Lemma own_pre_log_get_ineq γ γlog γreads σ σ' E :
  ↑prereadN ⊆ E →
  preread_inv γ γlog γreads -∗
  own_pre_log γlog σ -∗
  is_pb_log_lb γ σ' ={E}=∗
  own_pre_log γlog σ ∗
  ⌜prefix σ' σ⌝.
Proof.
  iIntros (?) "#Hinv Hlog #Hlb".
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (??) "(>HpbLog & >Hlog2 & Hi)".
  iDestruct (own_log_agree with "Hlog Hlog2") as "%"; subst.
  iDestruct (own_valid_2 with "HpbLog Hlb") as "%Hvalid".
  rewrite mono_list_both_dfrac_valid_L in Hvalid.
  destruct Hvalid as [_ Hvalid].
  iFrame "∗%".
  iMod ("Hclose" with "[-]"); last done.
  repeat iExists _; iFrame.
Qed.

End pb_preread_protocol.
