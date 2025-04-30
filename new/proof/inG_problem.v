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

Lemma fact : y -> z.
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
  y -> z.
Proof.
  intros Hy.
  Fail apply fact in Hy.
  (* Unable to apply lemma of type "y → z" on hypothesis of type "y". *)

  Set Printing All.
  Fail apply fact in Hy.
  (* Unable to apply lemma of type "forall _ : @y (@B_a ?H), @z ?H" on hypothesis of type "@y (@C_a H)". *)
Abort.
End C.
