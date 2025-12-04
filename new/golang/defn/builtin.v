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

Definition int_ge0 : val :=
  λ: "x", s_to_w64 "x" < #(W64 (2^63)).

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

Definition float_placeholder : val := #().

Definition make_nondet (t : go_type) : val :=
  λ: <>,
     match t with
     | uint64T => ArbitraryInt
     | uint32T => u_to_w32 ArbitraryInt
     | uint16T => u_to_w16 ArbitraryInt
     | _ => Panic "unsupported nondet"
     end.

End goose_lang.

