From iris.proofmode Require Import proofmode.

Lemma set_Forall_Forall_subsume `{Countable A} (l : list A) (s : gset A) P :
  set_Forall P s ->
  Forall (λ x, x ∈ s) l ->
  Forall P l.
Proof. do 2 rewrite Forall_forall. intros HP Hl x Hin. by auto. Qed.
