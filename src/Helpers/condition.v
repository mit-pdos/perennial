From iris.proofmode Require Import proofmode.

Section condition.
Context {PROP : bi}.

(* condition proof pattern:
condition resources [P] and [Q] on bool [b].
[P] and [Q] should be filled by [iAccu].
this removes proof duplication for code that takes in different ownership
depending on a condition.

e.g., binary tree code recursively traverses down a child corresponding
to the current path bit [b].
given ownership for child 0 [Q] and 1 [P], a standard proof would split
on [b] and duplicate the recursive call reasoning for [b=true] and [b=false].
instead, the proof can [condition_bool (P:=P) (Q:=Q) b] and pass only the
"positive condition" (i.e., ownership corresponding to b)
into the recursive call.

see the Pav Merkle-tree proof for more details. *)
Lemma condition_bool {P Q : PROP} (b : bool) :
  P -∗
  Q -∗
  (if b then P else Q) ∗ (if b then Q else P).
Proof. iIntros "**". case_match; iFrame. Qed.

Lemma condition_prop {P Q : PROP} {φ : Prop} (dec : Decision φ) :
  P -∗
  Q -∗
  (if dec then P else Q) ∗ (if dec then Q else P).
Proof. iIntros "**". case_match; iFrame. Qed.

End condition.
