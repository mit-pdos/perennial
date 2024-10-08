From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip.paxos Require Import base.

Section res_network.
  Context `{!paxos_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : paxos_names).

  Definition own_terminals γ (ts : gset chan) : iProp Σ.
  Admitted.

  Definition is_terminal γ (t : chan) : iProp Σ.
  Admitted.

  #[global]
  Instance is_terminal_persistent γ t :
    Persistent (is_terminal γ t).
  Admitted.

  Lemma terminal_update {γ ts} t :
    own_terminals γ ts ==∗
    own_terminals γ ({[t]} ∪ ts) ∗ is_terminal γ t.
  Admitted.

  Lemma terminal_lookup γ ts t :
    is_terminal γ t -∗
    own_terminals γ ts -∗
    ⌜t ∈ ts⌝.
  Admitted.

End res_network.
