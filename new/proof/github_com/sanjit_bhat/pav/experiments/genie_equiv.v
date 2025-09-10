From New.proof Require Import proof_prelude.

Section genie_equiv.
Context `{hg : heapGS Σ}.
(* nat represents some quantifiers. *)
Context (wish : nat → iProp Σ).
Context (post : nat → iProp Σ).
#[global] Instance wish_pers x : Persistent (wish x).
Proof. Admitted.
(* [Plain wish] is somewhat unfortunate.
if it doesn't hold with [is_hash], then spec0 strictly stronger than spec1.

that withstanding, prob won't need [Plain wish] outside this equiv file,
since can use [¬ wish] immediately, without needing to make it persistent. *)
#[global] Instance wish_plainly x : Plain (wish x).
Proof. Admitted.

Definition spec0 err : iProp Σ :=
  (⌜err = false⌝ ∗-∗ ∃ q, wish q) ∗
  (∀ q, wish q -∗ post q).

Definition spec1 err : iProp Σ :=
  match err with
  | true => ¬ ∃ q, wish q
  | false => ∃ q, wish q ∗ post q
  end.

Lemma dir0 err : spec0 err -∗ spec1 err.
Proof.
  iIntros "[H0 H1]".
  destruct err; simpl.
  - iIntros "H2".
    iDestruct "H0" as "[_ H0]".
    by iDestruct ("H0" with "H2") as %?.
  - iDestruct "H0" as "[H0 _]".
    iDestruct ("H0" with "[//]") as "[% #HW]".
    iDestruct ("H1" with "HW") as "H".
    iFrame "∗#".
Qed.

Lemma wish_det q0 q1 : wish q0 -∗ wish q1 -∗ ⌜q0 = q1⌝.
Proof. Admitted.

Lemma dir1 err : spec1 err -∗ spec0 err.
Proof.
  rewrite /spec0.
  destruct err; simpl in *.
  - (* [Plain wish] needed to make (¬ wish) Persistent. *)
    iIntros "#H0". iSplit.
    + iSplit. { by iIntros (?). }
      iIntros "HW".
      iDestruct ("H0" with "HW") as "[]".
    + iIntros "* HW".
      iExFalso. iApply "H0".
      iFrame.
  - iIntros "H". iDestruct "H" as (?) "[#HW HP]".
    iSplitR. { naive_solver. }
    iIntros (?) "#HW1".
    (* [wish_det] needed here due to spec0 [∀ q] structure.
    for spec1, strong caller needs it to unify their wish with err=false. *)
    by iDestruct (wish_det with "HW HW1") as %->.
Qed.
End genie_equiv.
