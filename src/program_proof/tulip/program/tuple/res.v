From Perennial.program_proof.tulip.program Require Import prelude.

Section res.
  Context `{!tulip_ghostG Σ}.
  Implicit Type (α : replica_names).

  Definition own_phys_hist_half α (key : string) (hist : dbhist) : iProp Σ.
  Admitted.
End res.
