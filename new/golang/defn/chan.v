From New.golang.defn Require Export loop assume predeclared.
From New.code.github_com.goose_lang.goose.model Require Import channel.

Module chan.
Section defns.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition receive elem_type : val :=
  λ: "c", MethodResolve (channel.Channel elem_type) "Receive" "c" #().
Definition send elem_type : val :=
  λ: "c", MethodResolve (channel.Channel elem_type) "Send" "c" #().

Definition for_range elem_type : val :=
  λ: "c" "body",
    (for: (λ: <>, #true)%V; (λ: <>, Skip)%V := λ: <>,
       let: ("v", "ok") := receive elem_type "c" in
       if: "ok" then
         "body" "v"
       else
         (* channel is closed *)
         break: #()
    ).

Definition select_send : val :=
  λ: "T" "ch" "v" "f", InjL ("T", "ch", "v", "f").

Definition select_receive : val :=
  λ: "T" "ch" "f", InjR ("T", "ch", "f").

Definition try_select_case elem_type : val :=
  λ: "c" "blocking",
    (match: "c" with
       InjL "data" =>
         let: ((("T", "ch"), "v"), "handler") := "data" in
         let: "success" :=
           MethodResolve (channel.Channel elem_type) "TrySend" #() "ch" "v" "blocking" in
         if: "success" then ("handler" #(), #true)
         else (#(), #false)
     | InjR "data" =>
         let: (("T", "ch"), "handler") := "data" in
         let: (("success", "v"), "ok") :=
           MethodResolve (channel.Channel elem_type) "TryReceive" #() "ch" "blocking" in
         if: "success" then ("handler" ("v", "ok"), #true)
         else (#(), #false)
      end).

(** [try_select] is used as the core of both [select_blocking] and [select_nonblocking] *)
Definition try_select : val :=
  rec: "go" "cases" "blocking" :=
    list.Match "cases"
      (λ: <>, (#(), #false))
      (λ: "hd" "tl",
         let: ("v", "done") := try_select_case "hd" "blocking" in
         if: ~"done" then "go" "tl" "blocking"
         else ("v", #true)).

(** select_blocking models a select without a default case. It takes a list of
cases (select_send or select_receive). It starts from a random position, then
runs do_select_case with "blocking"=#false over each case until one until one
returns true. Loop this until success. *)

Definition select_blocking : val :=
  rec: "loop" "cases" :=
    let: ("v", "succeeded") := try_select (list.Shuffle "cases") #true in
    if: "succeeded" then "v"
    else "loop" "cases".

(** select_nonblocking models a select with a default case. It takes a list of
cases (select_send or select_receive) and a default handler. It starts from a
random position, then runs do_select_case with "blocking"=#true over each case.
On failure, run the default handler. *)
Definition select_nonblocking : val :=
  λ: "cases" "def",
    let: ("v", "succeeded") := try_select (list.Shuffle "cases") #false in
    if: "succeeded" then "v"
    else "def" #().

End defns.
End chan.


(* FIXME: assumption for make, close, len, cap functions. *)

#[global] Opaque chan.make chan.receive chan.send chan.close
  chan.len chan.cap
  chan.select_nonblocking chan.select_blocking
.
(* [chan.for_range] is intended to be verified by unfolding and using [wp_for] *)
