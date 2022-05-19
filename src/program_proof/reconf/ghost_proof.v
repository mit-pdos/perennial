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

Definition old_conf_max γ term mval : iProp Σ :=
  □(∀ term' mval', ⌜int.nat term' < int.nat term⌝ →
  (committed_at_term γ term' mval') -∗
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
          old_conf_max γ term mval (* XXX: could make a accepted_lb_fancy, and put this
                              in there, and add requirement that quorum is
                              non-empty. *)
  ).

Definition overlapping_quorums (config1 config2:ConfigC) :=
  ∀ W1 W2, (config1.(is_quorum) W1) → (config2.(is_quorum) W2) → W1 ∩ W2 ≠ ∅.

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

Lemma ghost_commit γ term mval :
  sys_inv γ -∗
  committed_at_term γ term mval -∗
  proposed_lb γ term mval -∗
  old_conf_max γ term mval (* XXX: could make a accepted_lb_fancy, and put this
                              in there, and add requirement that quorum is
                              non-empty. *)
  ={↑sysN}=∗
  commit_lb γ mval
.
Proof.
  iIntros "#Hinv #HcommitAt #Hproposed #Hold".
  iInv "Hinv" as ">Hi" "Hclose".
  iDestruct "Hi" as (commitTerm commitVal) "(Hcommit & #HcommitAcc & #HproposedCommit & #HoldCommit)".
  iAssert (⌜mval_le mval commitVal ∨ mval_le commitVal mval⌝)%I as "%Hcomparable".
  {
    destruct (decide (int.nat term < int.nat commitTerm)).
    { (* case: term < commitTerm *)
      iDestruct ("HoldCommit" with "[] HcommitAt") as "%HvalLe".
      { done. }
      eauto.
    }
    destruct (decide (int.nat term = int.nat commitTerm)).
    { (* case: term == commitTerm *)
      replace (commitTerm) with (term) by word.
      (* TODO: put together the proposed_lb's to know that one of them is bigger
       than the other. *)
      iDestruct (own_valid_2 with "Hproposed HproposedCommit") as %Hvalid.
      rewrite singleton_op in Hvalid.
      apply singleton_valid in Hvalid.
      apply mono_list_lb_op_valid_1_L in Hvalid.
      done.
    }
    (* case: term > commitTerm *)
    assert (int.nat term > int.nat commitTerm) by word.
    iDestruct ("Hold" with "[] HcommitAcc") as "%HvalLe".
    { done. }
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
      iFrame "#".
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
    □(
      [∗ set] srv ∈ W,
        (∃ srvVal, ⌜mval_le srvVal highestVal⌝ ∗ accepted_ro γ srv highestTerm srvVal) ∗
        (∀ term', ⌜int.nat highestTerm < int.nat term'⌝ → ⌜int.nat term' < int.nat term⌝ → accepted_ro_none γ srv term')
    ) ={↑sysN}=∗
    old_conf_max γ term highestVal.
Proof.
Admitted.

End ghost_proof.
