From iris.algebra Require Import gmap_view.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip Require Import base.

Section res.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  Definition is_terminal γ (gid : u64) (t : chan) : iProp Σ :=
    own γ.(group_trmlm) {[ gid := gmap_view_frag t DfracDiscarded tt ]}.

  Definition own_terminals_auth γ (gid : u64) (ts : gset chan) : iProp Σ :=
    own γ.(group_trmlm) {[ gid := gmap_view_auth (DfracOwn 1) (gset_to_gmap tt ts) ]}.

  Definition own_terminals γ (gid : u64) (ts : gset chan) : iProp Σ :=
    own_terminals_auth γ gid ts ∗ ([∗ set] t ∈ ts, is_terminal γ gid t).

  #[global]
  Instance is_terminal_persistent γ gid t :
    Persistent (is_terminal γ gid t).
  Proof. apply _. Defined.

  Lemma terminal_update {γ gid ts} t :
    own_terminals γ gid ts ==∗
    own_terminals γ gid ({[t]} ∪ ts) ∗ is_terminal γ gid t.
  Proof.
    iIntros "[Hauth #Hfrags]".
    destruct (decide (t ∈ ts)) as [Hin | Hnotin].
    { replace (_ ∪ _) with ts by set_solver.
      iDestruct (big_sepS_elem_of with "Hfrags") as "#Hfrag".
      { apply Hin. }
      by iFrame "∗ #".
    }
    set ts' := _ ∪ _.
    iAssert (own_terminals_auth γ gid ts' ∗
             is_terminal γ gid t)%I
      with "[> Hauth]" as "[Hauth #Hfrag]".
    { iRevert "Hauth".
      rewrite -own_op.
      iApply own_update.
      rewrite singleton_op.
      apply singleton_update.
      rewrite gset_to_gmap_union_singleton.
      apply: gmap_view_alloc; last done; last done.
      by rewrite lookup_gset_to_gmap_None.
    }
    iFrame "∗ #".
    by iApply big_sepS_insert_2.
  Qed.

  Lemma terminal_lookup γ gid ts t :
    is_terminal γ gid t -∗
    own_terminals γ gid ts -∗
    ⌜t ∈ ts⌝.
  Proof.
    iIntros "#Hfrag [Hauth _]".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
    rewrite singleton_op singleton_valid in Hvalid.
    apply gmap_view_both_dfrac_valid_discrete_total in Hvalid.
    destruct Hvalid as (v' & _ & _ & Hlookup & _ & _).
    apply elem_of_dom_2 in Hlookup.
    by rewrite dom_gset_to_gmap in Hlookup.
  Qed.

End res.
