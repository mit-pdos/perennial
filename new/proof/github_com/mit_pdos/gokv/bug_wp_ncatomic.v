From stdpp Require Import prelude.

(** This illustrates why the grove_ffi proof now needs to manually apply
    [wp_ncatomic]. The difference compared to the old proof is that the old
    proofmode left the term [goose_generationGS.(iris_crashGS)] unsimplified,
    whereas the new proof mode probably does [simpl] somewhere which turns it
    into [goose_crashGS].

   To map this more minimal example to Perennial:
   One ↔ crashGS
   ContainsOne ↔ generationGS
   OtherContainsOne ↔ heapGS
   needs_one ↔ ncfupd
   needs_container ↔ wp
   failed [apply fact] ↔ failed [apply elim_modal_ncfupd_wp_atomic] during typeclass search for [ElimModal]
 *)

Class One.
Class ContainsOne := { contained :: One; }.
Axiom needs_one : ∀ {_ : One}, ().
Axiom needs_container : ∀ {_ : ContainsOne}, ().
Axiom fact : ∀ {H : ContainsOne}, needs_one = needs_container.
Class OtherContainsOne := { other_contained : One }.
Instance othercontainer_to_container `{!OtherContainsOne} : ContainsOne :=
  {| contained := other_contained |}.

Lemma test `{!OtherContainsOne} :
  needs_one = needs_container.
Proof.
  Set Printing All.
  progress simpl.
  Fail apply fact.
  Undo 2.
  apply fact.
  Unset Printing All.
Qed.

Fail Definition x := ltac:(eunify (Nat.pred ?[x], (S ?x)) (O, (S (S O)))).
Definition x : unit := ltac:(
  let A := open_constr:(Nat.pred ?[x]) in
  let B := open_constr:(S ?x) in
  let A' := open_constr:(O) in
  let B' := open_constr:(S (S O)) in
  first [
      (* This fails. *)
      (unify (A, B) (A', B'))  | idtac "first one failed";
      (* But this one doesn't: *)
      (unify B B'; unify A A'; refine tt)
    ];
  refine []
).
