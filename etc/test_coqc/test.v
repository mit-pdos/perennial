Require Import Utf8.
Definition σ : forall (x:nat), x + 1000 = x + 1000 :=
  fun x => eq_refl (x + (500+500)).
Print σ.
Local Theorem thm : True.
Proof.
  idtac "some output".
  exact I.
Qed.

Lemma helpful : True.
Proof.
  pose proof (eq_refl : 600 + 600 = 1200).
  debug auto.
Qed.

Global Theorem thm' : True.
Proof.
  auto.
Qed.
