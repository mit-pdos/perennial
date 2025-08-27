From New Require Import notation.
From New.golang.defn Require Import typing.

Section goose_lang.
Context `{ffi_syntax}.

Definition error : go_type := interfaceT.

(* only defined for 2 inputs for now. *)
Definition minUint64 (n : nat) : val :=
  match n with
  | 2%nat => (λ: "x" "y", if: "x" < "y" then "x" else "y")%V
  | _ => LitV $ LitPoison
  end.

Definition maxUint64 (n : nat) : val :=
  match n with
  | 2%nat => (λ: "x" "y", if: "x" > "y" then "x" else "y")%V
  | _ => LitV $ LitPoison
  end.

(* TODO(tchajed): I don't believe it's possible to implement signed operations
in a width-independent way *)

Definition int_ge0 : val :=
  λ: "x", "x" < #(W64 (2^63)).

Definition int_lt : val :=
  λ: "x" "y", if: int_ge0 "x" then
                (if: int_ge0 "y" then "x" < "y"
                else #false)
              else (* sint.Z x < 0 *)
                (if: int_ge0 "y" then #true
                else "x" < "y").
Definition int_leq : val :=
  λ: "x" "y", ("x" = "y") || int_lt "x" "y".

Definition int_geq : val :=
  λ: "x" "y", int_leq "y" "x".
Definition int_gt : val :=
  λ: "x" "y", int_lt "y" "x".

Axiom int_quot : val.
Axiom int_negative: val.
Axiom recover : val.

(* method sets for primitive types are empty *)
Section mset.
Context `{ffi_syntax}.
Definition uint64' : (go_string * go_string) := ("", "uint64")%go.
Definition int' : (go_string * go_string) := ("", "int")%go.
Definition bool' : (go_string * go_string) := ("", "bool")%go.
Definition string' : (go_string * go_string) := ("", "string")%go.
Definition slice' : (go_string * go_string) := ("", "slice")%go.
Definition slice'ptr : (go_string * go_string) := ("", "slice'ptr")%go.
End mset.

End goose_lang.
