From New.golang.defn Require Import loop postlang.

Module chan.
Section defns.
Context `{ffi_syntax}.

(* takes type as first argument *)
Axiom make : ∀ (t : go.type), val.
Axiom receive : val.
Axiom send : val.
Axiom select : val.
Axiom close : val.
Axiom len : val.
Axiom cap : val.
Axiom for_range : val.

(* FIXME: seal these functions *)
Definition select_no_default : val :=
  InjLV #().

Definition select_default : val :=
  λ: "f", InjR "f".

Definition select_send : val :=
  λ: "v" "ch" "f", InjL ("v", "ch", "f").

Definition select_receive : val :=
  λ: "ch" "f", InjR ("ch", "f").

End defns.
End chan.
