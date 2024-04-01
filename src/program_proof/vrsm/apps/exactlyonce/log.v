From Perennial.program_proof Require Import grove_prelude.
From iris.algebra Require Export mono_list.
Section log_defn.

Context `{!inG Σ (mono_listR (leibnizO A))}.
Definition own_log γ l := own γ (●ML{#1/2} l).

End log_defn.
