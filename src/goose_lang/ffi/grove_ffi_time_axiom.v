From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.grove_prelude.
From Perennial.base_logic Require Import mono_nat.
From Perennial.program_proof Require Import proof_prelude.


Section time_axiom.

Context `{!heapGS Σ}.

Definition is_time_lb γ (t:u64) := mono_nat_lb_own γ (int.nat t).
Definition own_time γ (t:u64) := mono_nat_auth_own γ 1 (int.nat t).

Lemma wp_GetTimeRange γ :
  ∀ (Φ:goose_lang.val → iProp Σ),
  (∀ (l h t:u64), ⌜int.nat t < int.nat h⌝ -∗ ⌜int.nat l < int.nat t⌝ -∗
                  own_time γ t -∗ (own_time γ t ∗ Φ (#l, #h)%V)) -∗
  WP GetTimeRange #() {{ Φ }}
.
Admitted.

End time_axiom.
