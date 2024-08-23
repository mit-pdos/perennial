From New Require Export notation.
From New.golang.defn Require Export typing.

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

Axiom int_lt : val.
Axiom int_leq : val.
Axiom int_geq : val.
Axiom int_gt : val.

End goose_lang.
