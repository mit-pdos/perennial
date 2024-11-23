From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip Require Import base.

Section res.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  Definition own_terminals γ (gid : u64) (ts : gset chan) : iProp Σ.
  Admitted.

  Definition is_terminal γ (gid : u64) (t : chan) : iProp Σ.
  Admitted.

  #[global]
  Instance is_terminal_persistent γ gid t :
    Persistent (is_terminal γ gid t).
  Admitted.

  Lemma terminal_update {γ gid ts} t :
    own_terminals γ gid ts ==∗
    own_terminals γ gid ({[t]} ∪ ts) ∗ is_terminal γ gid t.
  Admitted.

  Lemma terminal_lookup γ gid ts t :
    is_terminal γ gid t -∗
    own_terminals γ gid ts -∗
    ⌜t ∈ ts⌝.
  Admitted.

End res.
