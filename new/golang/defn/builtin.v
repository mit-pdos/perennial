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
Axiom int_quot : val.

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
