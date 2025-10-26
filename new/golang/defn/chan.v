From New.golang.defn Require Import mem typing exception pkg type_id.
From New.code.github_com.goose_lang.goose.model Require Import channel.

Module chan.
Section defns.
Context `{ffi_syntax}.

(* takes type as first argument *)
Definition make: val := channel.NewChannelⁱᵐᵖˡ.
Definition receive : val :=
  λ: "T" "c", method_call #(ptrT.id channel.Channel.id) #"Receive" "c" "T" #().
Definition send : val :=
  λ: "T" "c" "v", method_call #(ptrT.id channel.Channel.id) #"Send" "c" "T" "v".
Definition close : val :=
  λ: "T" "c", method_call #(ptrT.id channel.Channel.id) #"Close" "c" "T" #().
Definition len : val :=
  λ: "T" "c", method_call #(ptrT.id channel.Channel.id) #"Len" "c" "T" #().
Definition cap : val :=
  λ: "T" "c", method_call #(ptrT.id channel.Channel.id) #"Cap" "c" "T" #().

Definition for_range : val :=
  λ: "T" "c" "body",
    (rec: "loop" <> := exception_do (
        let: "t" := receive "T" "c" in
        if: Snd "t" then
          (* received Fst "t" *)
          let: "b" := "body" (Fst "t") in
          if: Fst "b" = #"break" then (return: (do: #())) else (do: #()) ;;;
          if: (Fst "b" = #"continue") || (Fst "b" = #"execute")
              then (return: "loop" #())
              else do: #() ;;;
            (return: "b")
        else
          (* ok = false, channel is empty *)
          (return: #())
      )) #().

Definition select_send : val :=
  λ: "T" "ch" "v" "f", InjL ("T", "ch", "v", "f").

Definition select_receive : val :=
  λ: "T" "ch" "f", InjR ("T", "ch", "f").

Definition do_select_case : val :=
  λ: "c" "blocking",
    exception_do (match: "c" with
        InjL "data" =>
          let: ((("T", "ch"), "v"), "f") := "data" in
          let: "ok" := method_call #(ptrT.id channel.Channel.id) #"TrySend" "ch" "T" "v" "blocking" in
          if: "ok" then ("f" #();;; do: #true) else (do: #false)
      | InjR "data" =>
          let: (("T", "ch"), "f") := "data" in
          let: (("success", "v"), "ok") := method_call #(ptrT.id channel.Channel.id) #"TryReceive" "ch" "T" "blocking" in
          if: "success" then
            ("f" "v" "ok";;; do: #true)
          else do: #false
      end).

(** select_blocking models a select without a default case. It takes a list of
cases (select_send or select_receive). It starts from a random position, then
runs do_select_case with "blocking"=#false over each case until one until one
returns true. Loop this until success. *)
Axiom select_blocking : val.

(** select_nonblocking models a select with a default case. It takes a list of
cases (select_send or select_receive) and a default handler. It starts from a
random position, then runs do_select_case with "blocking"=#true over each case.
On failure, run the default handler. *)
Axiom select_nonblocking : val.

End defns.
End chan.

#[global] Opaque chan.make chan.receive chan.send chan.close
  chan.len chan.cap
  chan.for_range chan.select_nonblocking chan.select_blocking
.
