From Perennial.program_proof Require Import grove_prelude.
From iris.bi.lib Require Import fractional.
From iris.algebra Require Import gmap cmra dfrac_agree.
From iris.algebra Require Import sts.
From iris.base_logic Require Import mono_nat.
From iris.proofmode Require Import proofmode.

Section poset_cmra.
(*
  Given poset (⪯, S), we want a cmra such that
  x ~~> y iff x ⪯ y.

  Carrier is (option S).
  x ⋅ y = None, if x ⪯̸ y ∧ y ⪯̸ x
  x ⋅ y = x if y ⪯ x
 *)

Context `{T:Type}.
Context `{R:relation T}.
Context `{!PartialOrder R}.
Context `{H: ∀ (x y:T), Decision (R x y)}.

Definition poset_cmra_car := leibnizO (option T).

Local Instance poset_op_instance : Op poset_cmra_car :=
  λ ox oy,
    x ← ox ;
    y ← oy ;
    if (decide (R x y)) then
      Some y
    else
    if (decide (R y x)) then
      Some x
    else
      None
.

Local Instance poset_pcore_instance : PCore poset_cmra_car := λ x, Some x.
Local Instance poset_valid_instance : Valid poset_cmra_car := λ ox, is_Some ox.
Local Instance poset_validN_instance : ValidN poset_cmra_car := λ _ ox, is_Some ox.

Lemma poset_ra_mixin : RAMixin poset_cmra_car.
Proof.
  apply ra_total_mixin; try naive_solver.
  - intros. intros z w. intros. destruct z, w; naive_solver.
  - intros z w H1. eauto.
  - intros z w. intros.
    unfold impl.
    intros.
    unfold validN.
    unfold poset_validN_instance.
    naive_solver.
  - intros x y z.
    admit.
Admitted.

Canonical Structure posetR := Cmra (poset_cmra_car) (discrete_cmra_mixin _ poset_ra_mixin).

End poset_cmra.

Section ghost_proof.

Record reconf_names :=
{
  acc_gn:gname
}.

Implicit Type γ:reconf_names.
Implicit Type srv:u64.

Context `{!heapGS Σ}.

(* A configuration is known by its write quorums *)
Record ConfigC :=
{
  is_quorum : (gset chan) → Prop
}.

Definition conf_eq (config1 config2:ConfigC) :=
  ∀ W, config1.(is_quorum) W ↔ config2.(is_quorum) W.

Record MonotonicValueC :=
{
  version:u64 ;
  config:ConfigC ;
  val:list u8 ;
}.

Definition mval_le mval mval' := int.nat mval.(version) ≤ int.nat mval'.(version)
                                    ∧ (mval.(version) = mval'.(version) → mval = mval')
.

Definition mval_lt mval mval' := int.nat mval.(version) < int.nat mval'.(version).

Implicit Type mval:MonotonicValueC.
Implicit Type term:u64.

(* This is just ownership of raw ghost resources. *)

Definition accepted γ srv term mval : iProp Σ.
Admitted.

Definition accepted_ro γ srv term mval : iProp Σ.
Admitted.

Definition accepted_ro_none γ srv term : iProp Σ.
Admitted.

Definition accepted_lb γ srv term mval : iProp Σ.
Admitted.

Definition commit γ mval : iProp Σ.
Admitted.

Definition commit_lb γ mval : iProp Σ.
Admitted.

Definition proposed γ term mval : iProp Σ.
Admitted.

Definition proposed_lb γ term mval : iProp Σ.
Admitted.

Instance commit_timeless γ mval : Timeless (commit γ mval).
Admitted.

Instance accepted_lb_timeless γ srv term mval : Timeless (accepted_lb γ srv term mval).
Admitted.

Instance commit_lb_pers γ mval : Persistent (commit_lb γ mval).
Admitted.

Instance proposed_lb_pers γ term mval : Persistent (proposed_lb γ term mval).
Admitted.


Instance accepted_ro_pers γ srv term mval : Persistent (accepted_ro γ srv term mval).
Admitted.

Instance accepted_lb_pers γ srv term mval : Persistent (accepted_lb γ srv term mval).
Admitted.

(* This is more complicated stuff, beyond raw ghost resource ownership. *)

Definition committed_at_term γ term mval: iProp Σ :=
  ∃ W, ⌜mval.(config).(is_quorum) W⌝ ∗
  ([∗ set] srv ∈ W, accepted_lb γ srv term mval)
.

Definition old_conf_max γ term mval : iProp Σ :=
  ∀ term', ⌜int.nat term' < int.nat term⌝ →
  (∀ mval', (committed_at_term γ term' mval') →
            ⌜mval_le mval' mval⌝
  )
.

Definition sysN := nroot .@ "sys".

Definition sys_inv γ : iProp Σ :=
  inv sysN (
        ∃ term mval,
          commit γ mval ∗
          (committed_at_term γ term mval)
  ).

Definition overlapping_quorums (config1 config2:ConfigC) :=
  ∀ W1 W2, (config1.(is_quorum) W1) → (config2.(is_quorum) W2) → W1 ∩ W2 ≠ ∅.

Definition no_concurrent_reconfigs_and_overlapping_quorums γ term mval : iProp Σ :=
  ∃ mval',
    commit_lb γ mval' ∗ □(
      ∀ mval'', ⌜mval_lt mval'' mval⌝ →
                ⌜mval_le mval' mval''⌝ →
                proposed_lb γ term mval'' →
                ⌜conf_eq mval'.(config) mval''.(config)⌝
    ) ∗
    ⌜overlapping_quorums mval.(config) mval'.(config)⌝
.

Definition proposed_lb_fancy γ term mval : iProp Σ :=
  proposed_lb γ term mval ∗
  no_concurrent_reconfigs_and_overlapping_quorums γ term mval
.

Lemma ghost_commit γ term mval :
  sys_inv γ -∗
  committed_at_term γ term mval ={↑sysN}=∗
  commit_lb γ mval
.
Proof.
  iIntros "#Hinv #Hcommit".
  iDestruct "Hcommit" as (W) "[%Hquorum Hacc]".
  iInv "Hinv" as ">Hi" "Hclose".
  iDestruct "Hi" as (commitTerm commitVal) "[Hcommit HcommitAcc]".
  iDestruct "HcommitAcc" as (Wcom) "[%Hcom_quorum HcommitAcc]".
Admitted.

Lemma become_leader γ term highestVal :
  ∀ highestTerm W,
    int.nat highestTerm < int.nat term →
    highestVal.(config).(is_quorum) W →
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
