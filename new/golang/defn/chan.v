From New.golang.defn Require Import mem loop typing.
From New.code.github_com.goose_lang.goose.model Require Import channel.

Module chan.
Section defns.
Context `{ffi_syntax}.

(* takes type as first argument *)
Definition make: val := channel.NewChannelRefⁱᵐᵖˡ.
Definition receive : val :=
  λ: "T" "c", channel.Channel__Receiveⁱᵐᵖˡ "c" "T" #().
Definition send : val :=
  λ: "T" "c" "v", channel.Channel__Sendⁱᵐᵖˡ "c" "T" "v".
Definition close : val :=
  λ: "T" "c", channel.Channel__Closeⁱᵐᵖˡ "c" "T" #().
Definition len : val :=
  λ: "T" "c", channel.Channel__Lenⁱᵐᵖˡ "c" "T" #().
Definition Cap : val :=
  λ: "T" "c", channel.Channel__Capⁱᵐᵖˡ "c" "T" #().

Axiom for_range : val.

Axiom select : val.

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
