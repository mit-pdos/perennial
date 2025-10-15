From New.golang.defn Require Import mem typing exception.
From New.code.github_com.goose_lang.goose.model Require Import channel.

(* FIXME: seal these functions *)

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
Definition cap : val :=
  λ: "T" "c", channel.Channel__Capⁱᵐᵖˡ "c" "T" #().

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
          let: "ok" := channel.Channel__TrySendⁱᵐᵖˡ "ch" "T" "v" "blocking" in
          if: "ok" then ("f" #();;; do: #true) else (do: #false)
      | InjR "data" =>
          let: (("T", "ch"), "f") := "data" in
          let: (("success", "v"), "ok") := channel.Channel__TryReceiveⁱᵐᵖˡ "ch" "T" "blocking" in
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

(* TODO: won't use these as select cases *)

Definition select_no_default : val :=
  InjLV #().

Definition select_default : val :=
  λ: "f", InjR "f".

End defns.
End chan.

#[global] Opaque chan.make chan.receive chan.send chan.close
  chan.len chan.cap
  chan.for_range chan.select_nonblocking chan.select_blocking
.
