From Perennial.program_proof Require Import grove_prelude.

Section inv.
Context `{!heapGS Σ}.
Definition serv_sigpred (γ : gname) : (list w8 → iProp Σ) :=
  (* TODO: fill in. *)
  λ data, True%I.
End inv.
