From iris.algebra Require Import dfrac.

Declare Scope dfrac_scope.
Delimit Scope dfrac_scope with dfrac.
Bind Scope dfrac_scope with dfrac.

Notation "1" := (DfracOwn 1) : dfrac_scope.
(* users need (□) to de-conflict with the reserved persistent notation
in bi/notation.v, which takes in an extra arg. *)
Notation "□" := DfracDiscarded (at level 20) : dfrac_scope.
(* this currently conflicts with to_val notation.
maybe we need to restrict that notation's scope? *)
(* Notation "# q" := (DfracOwn q%Qp) (at level 50) : dfrac_scope. *)
