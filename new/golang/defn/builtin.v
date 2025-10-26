From New.golang.defn Require Export postlang.

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
