From New.golang.defn Require Import postlang.

Section goose_lang.
Context `{ffi_syntax}.

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

Axiom recover : val.

Definition float_placeholder : val := #().

Definition make_nondet (t : go.type) : val :=
  λ: <>,
     if decide (t = go.uint64) then
       ArbitraryInt
     else
       Panic "unsupported nondet".
(*
     match t with
     | go.uint64 => ArbitraryInt
     | uint32T => u_to_w32 ArbitraryInt
     | uint16T => u_to_w16 ArbitraryInt
     | _
     end. *)

End goose_lang.
