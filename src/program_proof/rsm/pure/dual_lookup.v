From iris.proofmode Require Import proofmode.

Definition dual_lookup `{Countable K1} `{Countable K2} {V}
  (m : gmap K1 (gmap K2 V)) (k1 : K1) (k2 : K2) :=
  match m !! k1 with
  | Some im => im !! k2
  | None => None
  end.

Definition dual_lookup_consistent `{Countable K1} `{Countable K2} {V}
  (m1 : gmap K1 (gmap K2 V)) (m2 : gmap K2 (gmap K1 V)) :=
  ∀ k1 k2, dual_lookup m1 k1 k2 = dual_lookup m2 k2 k1.

Section props.
  Context `{Countable K1} `{Countable K2} {V  : Type}.


End props.
