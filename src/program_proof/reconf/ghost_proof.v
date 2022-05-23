From Perennial.program_proof Require Import grove_prelude.
From iris.bi.lib Require Import fractional.
From iris.algebra Require Import gmap cmra dfrac_agree.
From iris.algebra Require Import mono_list.
From iris.base_logic Require Import mono_nat.
From iris.proofmode Require Import proofmode.

Section ghost_proof.

(* A configuration is known by its write quorums *)
Record ConfigC :=
{
  is_quorum : (gset chan) → Prop
}.

Record LogEntry :=
{
  config:ConfigC ;
  val:list u8 ;
}.

Class reconfG Σ :=
{
  acc_inG:> inG Σ (gmapR (u64 * u64) (mono_listR (leibnizO LogEntry)));
  commit_inG:> inG Σ (mono_listR (leibnizO LogEntry));
  proposal_inG:> inG Σ (gmapR u64 (mono_listR (leibnizO LogEntry)));
}.

Record reconf_names :=
{
  acc_gn:gname ;
  commit_gn:gname ;
  prop_gn:gname ;
}.

Implicit Type γ:reconf_names.
Implicit Type srv:u64.

Context `{!heapGS Σ}.
Context `{!reconfG Σ}.

Definition conf_eq (config1 config2:ConfigC) :=
  ∀ W, config1.(is_quorum) W ↔ config2.(is_quorum) W.

Implicit Type mval : (list (leibnizO LogEntry)).

Definition mval_le mval mval' := prefix mval mval'.

Definition mval_lt mval mval' := prefix mval mval' ∧ mval ≠ mval'.

Implicit Type term:u64.

(* This is just ownership of raw ghost resources. *)

Definition def_config : ConfigC.
Admitted.

Definition get_config mval : ConfigC :=
  match (last mval) with
  | Some e => e.(config)
  | _ => def_config
end
.

Definition accepted γ srv term mval : iProp Σ :=
  own γ.(acc_gn) {[ (term,srv) := ●ML mval ]}.

Definition accepted_ro γ srv term mval : iProp Σ :=
  own γ.(acc_gn) {[ (term,srv) := ●ML□ mval ]}.

Definition accepted_ro_none γ srv term : iProp Σ :=
  own γ.(acc_gn) {[ (term,srv) := ●ML□ [] ]}. (* XXX: not sure if empty list is good enough here*)

Definition accepted_lb γ srv term mval : iProp Σ :=
  own γ.(acc_gn) {[ (term,srv) := ◯ML mval ]}.

Definition commit γ mval : iProp Σ :=
  own γ.(commit_gn) (●ML mval).

Definition commit_lb γ mval : iProp Σ :=
  own γ.(commit_gn) (◯ML mval).

Definition proposed γ term mval : iProp Σ :=
  own γ.(acc_gn) {[ term := ●ML mval ]}.

Definition proposed_lb γ term mval : iProp Σ :=
  own γ.(acc_gn) {[ term := ◯ML mval ]}.


(* This is more complicated stuff, beyond raw ghost resource ownership. *)

Definition committed_at_term γ term mval: iProp Σ :=
  ∃ W, ⌜(get_config mval).(is_quorum) W⌝ ∗
  ([∗ set] srv ∈ W, accepted_lb γ srv term mval)
.

Definition overlapping_quorums (config1 config2:ConfigC) :=
  ∀ W1 W2, (config1.(is_quorum) W1) → (config2.(is_quorum) W2) → W1 ∩ W2 ≠ ∅.

(* Maybe this should say
   either the config of mval' intersects with the config of mval OR
   every quorum in mval' contains a server that accepted something bigger than
   mval'.
*)
(*
  FIXME: should we take term'' = term here?
  If we do, then it's not clear how to prove (old_conf_max γ term mval -∗
  old_conf_max γ (term + 1) mval) anymore.
  If we don't, then when we want to use old_conf_max, it's possible that term''
  < term, in which case we would want to use old_term_max, but we can't use
  old_term_max, because it requires old_conf_max.

  There isn't a real circularity, it's just that we want to recursive invoke
  old_conf and old_term. But, that'll result in later problems.
 *)
From iris.bi.lib Require Import fixpoint.

Print fixpoint.

Definition old_conf_max_pre (Φ:(reconf_names -d> u64 -d> (list (leibnizO LogEntry)) -d> iPropO Σ)): (reconf_names -d> u64 -d> (list (leibnizO LogEntry)) -d> iPropO Σ) :=
  λ γ term mval,
    (∀ mval', ⌜mval_lt mval' mval⌝ → □(
        (⌜overlapping_quorums (get_config mval') (get_config mval)⌝ ∨
         (∃ mval'' term'',
             ⌜mval_lt mval mval''⌝ ∗
             ⌜mval_le mval'' mval'⌝ ∗
             ⌜int.nat term'' ≤ int.nat term⌝ ∗
             committed_at_term γ term'' mval'' ∗
             Φ γ term mval'' ∗
             ⌜overlapping_quorums (get_config mval') (get_config mval'')⌝
         )
        )
     ))%I
.

Definition old_conf_max_pre_least γ term Φ mval: iProp Σ :=
  ∀ mval', ⌜mval_lt mval' mval⌝ → □(
        (⌜overlapping_quorums (get_config mval') (get_config mval)⌝ ∨
         (∃ mval'' term'',
             ⌜mval_lt mval mval''⌝ ∗
             ⌜int.nat term'' ≤ int.nat term⌝ ∗
             committed_at_term γ term'' mval'' ∗
             Φ mval'' ∗
             ⌜overlapping_quorums (get_config mval') (get_config mval'')⌝
         )
        )
     )
.


Definition old_conf_max γ term mval : iProp Σ := (bi_least_fixpoint (old_conf_max_pre_least γ term) mval).

Instance old_conf_max_pre_contr : Contractive old_conf_max_pre.
Admitted.

Program Definition old_conf_max_2 γ term mval : iProp Σ := □ (fixpoint (old_conf_max_pre) γ term mval).

Definition old_conf_max_orig γ term mval: iProp Σ :=
  ∀ mval', ⌜mval_lt mval' mval⌝ → □(
        (⌜overlapping_quorums (get_config mval') (get_config mval)⌝ ∨
         (∃ mval'' term'',
             ⌜mval_lt mval mval''⌝ ∗
             ⌜int.nat term'' ≤ int.nat term⌝ ∗
             committed_at_term γ term'' mval'' ∗
             (* FIXME: want to be able to put another old_conf_max here *)
             ⌜overlapping_quorums (get_config mval') (get_config mval'')⌝
         )
        )
     )
.

Definition old_term_max γ term mval : iProp Σ :=
  ∀ term' mval', □(⌜int.nat term' < int.nat term⌝ →
  proposed_lb γ term' mval' -∗
  committed_at_term γ term' mval' -∗
  old_conf_max γ term' mval' -∗
  ⌜mval_le mval' mval⌝
  )
.

Definition sysN := nroot .@ "sys".

Definition sys_inv γ : iProp Σ :=
  inv sysN (
        ∃ term mval,
          commit γ mval ∗
          (committed_at_term γ term mval) ∗
          proposed_lb γ term mval ∗
          old_term_max γ term mval ∗ (* XXX: could make a accepted_lb_fancy, and put this
                              in there, and add requirement that quorum is
                              non-empty. *)
          old_conf_max γ term mval
  ).

Definition no_concurrent_reconfigs_and_overlapping_quorums γ term mval : iProp Σ :=
  ∃ mval',
    commit_lb γ mval' ∗ □(
      ∀ mval'', ⌜mval_lt mval'' mval⌝ →
                ⌜mval_le mval' mval''⌝ →
                proposed_lb γ term mval'' →
                ⌜conf_eq (get_config mval') (get_config mval'')⌝
    ) ∗
    ⌜overlapping_quorums (get_config mval) (get_config mval')⌝
.

Definition proposed_lb_fancy γ term mval : iProp Σ :=
  proposed_lb γ term mval ∗
  no_concurrent_reconfigs_and_overlapping_quorums γ term mval
.

Lemma mono_list_included': ∀ (A : ofe) (dq : dfrac) (l l': list A),
    l `prefix_of` l' →
    ◯ML l ≼ ●ML{dq} l'.
Proof.
  intros.
  assert (◯ML l' ≼ ●ML{dq} l').
  { apply mono_list_included. }
  assert (◯ML l ≼ ◯ML l').
  { apply mono_list_lb_mono. done. }
  apply (transitivity H1 H0).
Qed.

Instance test γ term: BiMonoPred (old_conf_max_pre_least γ term).
Proof.
  apply Build_BiMonoPred.
  {
    iIntros (????) "#Hwand".
    iIntros (?) "#H".
    iIntros (??) "!#".
    iSpecialize ("H" $! mval' H1 with "").
    iDestruct "H" as "[H|H]".
    {
      iLeft.
      done.
    }
    {
      iRight.
      iDestruct "H" as (??) "H".
      iExists _, _; iFrame "#".
      admit.
    }
  }
  {
    admit.
  }
Admitted.

Lemma ghost_commit γ term mval :
  sys_inv γ -∗
  committed_at_term γ term mval -∗
  proposed_lb γ term mval -∗
  old_term_max γ term mval -∗ (* XXX: could make a accepted_lb_fancy, and put this
                              in there, and add requirement that quorum is
                              non-empty. *)
  old_conf_max γ term mval
  ={↑sysN}=∗
  commit_lb γ mval
.
Proof.
  iIntros "#Hinv #HcommitAt #Hproposed #Hold Hconf".
  unfold old_conf_max.
  rewrite least_fixpoint_unfold.
  iDestruct "Hconf" as "#Hconf".
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (commitTerm commitVal) "Hi".
  iEval (unfold old_conf_max) in "Hi".
  rewrite least_fixpoint_unfold.
  iDestruct "Hi" as "(>Hcommit & #>HcommitAcc & #>HproposedCommit & #>HoldCommit & #HconfCommit)".
  iAssert (⌜mval_le mval commitVal ∨ mval_le commitVal mval⌝)%I as "%Hcomparable".
  {
    destruct (decide (int.nat term < int.nat commitTerm)).
    { (* case: term < commitTerm *)
      iDestruct ("HoldCommit" with "[] Hproposed HcommitAt [Hconf]") as "%HvalLe".
      { done. }
      {
        unfold old_conf_max.
        rewrite least_fixpoint_unfold.
        iFrame "Hconf".
      }
      eauto.
    }
    destruct (decide (int.nat term = int.nat commitTerm)).
    { (* case: term == commitTerm *)
      replace (commitTerm) with (term) by word.
      iDestruct (own_valid_2 with "Hproposed HproposedCommit") as %Hvalid.
      rewrite singleton_op in Hvalid.
      apply singleton_valid in Hvalid.
      apply mono_list_lb_op_valid_1_L in Hvalid.
      done.
    }
    (* case: term > commitTerm *)
    assert (int.nat term > int.nat commitTerm) by word.
    iDestruct ("Hold" with "[] HproposedCommit HcommitAcc [HconfCommit]") as "%HvalLe".
    { done. }
    {
      iIntros.
      unfold old_conf_max.
      rewrite least_fixpoint_unfold.
      iFrame "HconfCommit".
    }
    eauto.
  }

  destruct Hcomparable.
  { (* committed value is bigger than mval *)
    iDestruct (own_mono _ _ (◯ML mval) with "Hcommit") as "#HH".
    {
      by apply mono_list_included'.
    }
    iFrame "#".
    iMod ("Hclose" with "[Hcommit]").
    {
      iNext.
      iExists _, _; iFrame.
      iFrame "#".
    }
    done.
  }
  { (* mval is bigger than committed value; in this case, we commit something new *)
    iMod (own_update with "Hcommit") as "Hcommit".
    {
      apply mono_list_update.
      exact H.
    }
    iDestruct (own_mono _ _ (◯ML mval) with "Hcommit") as "#HH".
    {
      apply mono_list_included.
    }
    iFrame "#".
    iMod ("Hclose" with "[Hcommit]").
    {
      iNext.
      iExists _, _; iFrame.
      iFrame "HcommitAt #".
    }
    done.
  }
Qed.

Lemma become_leader γ term highestVal :
  ∀ highestTerm W,
    int.nat highestTerm < int.nat term →
    (get_config highestVal).(is_quorum) W →
    sys_inv γ -∗
    proposed_lb_fancy γ highestTerm highestVal -∗
    old_term_max γ highestTerm highestVal -∗
    old_conf_max γ highestTerm highestVal -∗
    □(
      [∗ set] srv ∈ W,
        (∃ srvVal, ⌜mval_le srvVal highestVal⌝ ∗ accepted_ro γ srv highestTerm srvVal) ∗
        (∀ term', ⌜int.nat highestTerm < int.nat term'⌝ → ⌜int.nat term' < int.nat term⌝ → accepted_ro_none γ srv term')
    ) -∗
    old_term_max γ term highestVal.
Proof.
  intros ? ? HtermIneq Hquorum.
  iIntros "#Hsys #Hproposed #Hold #Hconf #HoldInfo".
  iIntros (term' mval').
  iModIntro.
  iIntros "%Hterm'Ineq".
  iIntros "#Hproposed'".
  iIntros "#Hcommit' #Hconf'".
  destruct (decide (int.nat term' < int.nat highestTerm)).
  { (* term' < highestTerm, so we can just use the old_term_max of (highestTerm,highestVal) *)
    by iApply "Hold".
  }
  destruct (decide (int.nat term' = int.nat highestTerm)).
  { (* for term' == highestTerm, we have the first part of "oldInfo" *)
    replace (term') with (highestTerm); last first.
    { (* FIXME: why doesn't word work? *)
      clear -e.
      Search Z.to_nat.
      rewrite Z2Nat.inj_iff in e; first last.
      { word. }
      { word. }
      {
        Search word.unsigned.
        apply word.unsigned_inj in e.
        done.
      }
    }
    iDestruct "Hproposed" as "[Hproposed Hfancy]".
    iDestruct (own_valid_2 with "Hproposed' Hproposed") as %Hvalid.
    rewrite singleton_op in Hvalid.
    rewrite singleton_valid in Hvalid.
    apply mono_list_lb_op_valid_1_L in Hvalid.
    destruct Hvalid as [Hdone|HlogLe].
    { done. }
    destruct (decide (length mval' = length highestVal)).
    { (* If the two are equal, then no problem *)
      assert (mval' = highestVal).
      {
        symmetry.
        apply list_prefix_eq.
        {
          done.
        }
        word.
      }
      rewrite H.
      done.
    }
    (* case: mval_lt highestVal mval'. Here, we're gonna derive a contradiction. *)
    iExFalso.
    (* now, apply old_conf_max highestTerm mval'' *)
    iDestruct ("Hconf'" $! highestVal) as "#Hconf2".
    iSpecialize ("Hconf2" with "[]").
    {
      iPureIntro.
      split; naive_solver.
    }
    iDestruct "Hconf2" as "[Hoverlap|Hstale]".
    { (* In this case, the quorums of mval' overlap with the quorums of highestVal.
         This gives a contradiction between Hcommit' and HoldInfo.
       *)
      admit.
    }
    { (* In this case, some highest value mval'' was committed, and has
         overlapping quorums with highestVal. *)
      iDestruct "Hstale" as (mval'' term'') "(%Hmval''lt & %Hterm''Ineq & Hcommit'' & %Hoverlap)".
      (* if term'' < highestTerm, then (old_term_max highestTerm highestVal) takes care of it *)
      destruct (decide (int.nat term'' < int.nat highestTerm)).
      {
        iSpecialize ("Hold" $! term'' mval'' with "[] [] Hcommit''").
        { done. }
        {  admit. } (* TODO: add this to old_conf_max. *)
        (* FIXME: we need old_conf_max to finish instantiating the old_term_max.
           But, we need old_conf_max for the term'' and mval'' that we
           destructed from a different old_conf_max.
         *)
      }
      assert (term'' = highestTerm) as -> by word.
      admit. (* TODO: need to know that mval'' > highestVal to get contradiction *)
    }

  }


End ghost_proof.
