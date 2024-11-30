From Perennial.program_proof.tulip.program Require Import prelude.

Section res.
  Context `{!tulip_ghostG Σ}.
  Implicit Type (α : replica_names).

  Definition own_phys_hist_half α (key : string) (hist : dbhist) : iProp Σ.
  Admitted.

  Lemma phys_hist_update {α k h1 h2} h :
    own_phys_hist_half α k h1 -∗
    own_phys_hist_half α k h2 ==∗
    own_phys_hist_half α k h ∗
    own_phys_hist_half α k h.
  Admitted.

  Lemma phys_hist_agree α k h1 h2 :
    own_phys_hist_half α k h1 -∗
    own_phys_hist_half α k h2 -∗
    ⌜h2 = h1⌝.
  Admitted.

  Lemma phys_hist_alloc :
    ⊢ |==> ∃ α, ([∗ set] k ∈ keys_all, own_phys_hist_half α k [None]) ∗
                ([∗ set] k ∈ keys_all, own_phys_hist_half α k [None]).
  Admitted.

End res.
