From Perennial.base_logic Require Import ghost_map.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip.paxos Require Import base.

Section res_network.
  Context `{!paxos_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : paxos_names).

  Definition is_terminal γ (t : chan) : iProp Σ :=
    ghost_map_elem γ.(trmlm) t DfracDiscarded tt.

  Definition own_terminals_auth γ (ts : gset chan) : iProp Σ :=
    ghost_map_auth γ.(trmlm) 1 (gset_to_gmap tt ts).

  Definition own_terminals γ (ts : gset chan) : iProp Σ :=
    own_terminals_auth γ ts ∗ [∗ set] t ∈ ts, is_terminal γ t.

  #[global]
  Instance is_terminal_persistent γ t :
    Persistent (is_terminal γ t).
  Proof. apply _. Defined.

  Lemma terminal_update {γ ts} t :
    own_terminals γ ts ==∗
    own_terminals γ ({[t]} ∪ ts) ∗ is_terminal γ t.
  Proof.
    iIntros "[Hauth #Hfrags]".
    destruct (decide (t ∈ ts)) as [Hin | Hnotin].
    { iDestruct (big_sepS_elem_of with "Hfrags") as "Hfrag".
      { apply Hin. }
      replace (_ ∪ _) with ts by set_solver.
      by iFrame "∗ #".
    }
    iMod (ghost_map_insert t tt with "Hauth") as "[Hauth Hfrag]".
    { by rewrite lookup_gset_to_gmap_None. }
    rewrite -gset_to_gmap_union_singleton.
    iMod (ghost_map_elem_persist with "Hfrag") as "#Hfrag".
    iFrame "∗ #".
    by iApply big_sepS_insert_2.
  Qed.

  Lemma terminal_lookup γ ts t :
    is_terminal γ t -∗
    own_terminals γ ts -∗
    ⌜t ∈ ts⌝.
  Proof.
    iIntros "Hfrag [Hauth _]".
    iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hlookup.
    by apply lookup_gset_to_gmap_Some in Hlookup as [? _].
  Qed.

End res_network.
