From stdpp Require Import prelude.

Module simple.
(* Problem: Suppose A is a dependency-free package, B imports A, and C imports B and A.
   Suppose a typeclass is defined for each package (containing all the inGs for
   a real Perennial proof).
   Then, in the context of C, there are two non-equivalent instances of [A]'s
   typeclass: there's [C.A] and then there's [C.B.A]. This makes it impossible
   to prove code in [C] that connects stuff from [A] to stuff in [B]. Here's a
   minimal example:
 *)

(* package A defines some stuff, x, y, z *)
Section A.
Class A := { x : nat }.

Context `{!A}.

Definition y : Prop := x = 1.

End A.

(* package B imports A and provides some more stuff on top.
   This includes [fact], which converts a prop from the lower-level library A
   into a higher-level prop defined here in library B.

  This is like taking an [is_closeable_chan] and putting it inside of
 *)
Section B.
Class B := { B_a :: A }.

Context `{!B}.

Definition z : Prop := x > 0.

Lemma fact : y → z.
Proof. unfold z, y. intros ->. auto. Qed.

End B.

(* package C imports both A and B. It will establish a prop from A, then use library B
   to get a then get a prop from B. However, library B is expecting [y]
   to be with respect to the typeclass [B_a ?B], whereas [C] establishes it with
   respect to [C_a ?C].
 *)
Section C.
Class C :=
  {
    C_a :: A;
    C_b :: B;
  }.

Context `{!C}.
Lemma test :
  y → z.
Proof.
  intros Hy.
  Fail apply fact in Hy.
  (* Unable to apply lemma of type "y → z" on hypothesis of type "y". *)

  Set Printing All.
  Fail apply fact in Hy.
  (* Unable to apply lemma of type "forall _ : @y (@B_a ?H), @z ?H" on hypothesis of type "@y (@C_a H)". *)
Abort.
End C.

End simple.
(* The above could be fixed by removing [C_a] from [C]; this is a little
   unfortunately unsystematic since it requires looking transitively inside the
   definition of B, but it does work. *)

Module trickier.
(** Here's a tricker example:
    A is dependency-free
    B imports A and provides some extra stuff on top
    C imports A and provides some extra stuff on top
    D uses A, B, and C.
 *)

Section A.
Class A := { x : nat }.
Context `{!A}.
Definition a_prop : Prop := x > 1.
End A.

Section B.
Class B := { B_a :: A ; y : nat }.
Context `{!B}.
Definition b_prop : Prop := x = 3.
Lemma b_fact : b_prop → a_prop.
Proof. unfold b_prop, a_prop. lia. Qed.
End B.

Section C.
Class C := { C_a :: A ; z : nat }.
Context `{!C}.
Definition c_prop : Prop := x > 0.
Lemma c_fact : a_prop → c_prop.
Proof. unfold c_prop, a_prop. lia. Qed.
End C.

Section D.
Class D := {
    D_b :: B ;
    D_c :: C ;
  }.

Context `{!D}.
Definition d_prop : Prop := y = y ∧ z = z.
Lemma d_fact : b_prop → c_prop.
Proof.
  intros Hb. apply b_fact in Hb.
  Fail apply c_fact in Hb.
  (* Unable to apply lemma of type "a_prop → c_prop" on hypothesis of type "a_prop". *)
  Set Printing All.
  Fail apply c_fact in Hb.
  (* Unable to apply lemma of type "forall _ : @a_prop (@C_a ?H), @c_prop ?H" on hypothesis of type "@a_prop (@B_a (@D_b H))". *)
Abort.
End D.

End trickier.
