From New.ghost Require Import all.
From iris.algebra.lib Require Import frac_auth.

Section iprop.
Context {Σ} `{allG Σ}.

Definition frac_auth_own γ (x: Z) : iProp Σ :=
  own γ (●F x) ∗ own γ (◯F x).

End iprop.
