From Perennial.program_proof Require Import grove_prelude.
From iris.bi.lib Require Import fractional.
From iris.algebra Require Import gmap cmra dfrac_agree.
From iris.base_logic Require Import mono_nat.
From iris.proofmode Require Import proofmode.

Section ghost_proof.

Class mapG Σ K V `{Countable K} :=
  { map_inG:> inG Σ (gmapR K (dfrac_agreeR (leibnizO V)))} .

Record reconf_names :=
{
  accepted_gn:gname
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

(* This is more complicated stuff, beyond raw ghost resource ownership. *)

Definition committed_at_term γ term mval: iProp Σ :=
  ∃ W, ⌜mval.(config).(is_quorum) W⌝ ∗
  ([∗ set] srv ∈ W, accepted γ srv term mval)
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
  commit_lb γ mval.
Proof.
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
