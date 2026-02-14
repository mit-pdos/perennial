From stdpp Require Import base sets gmap.
Set Default Proof Using "Type".

Section s.

Context {Hunused : True}.

Lemma test (s : gset nat) (H : ∀ x, x ∉ s) :
  s = ∅.
Proof.
  set_solver. (* [set_unfold] in applies [set_unfold_1] on Hunused. *)
Fail Qed.
Abort.

End s.
