From iris.proofmode Require Import environments string_ident.
From New.proof Require Import proof_prelude.
From stdpp Require Import base.
Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 is_glob_identifier_char (x : char) : bool :=
  let n := Char.to_int x in
  let alpha_upper := Bool.and (Int.le n 90) (Int.le 65 n) in
  let alpha_lower := Bool.and (Int.le n 122) (Int.le 97 n) in
  let num := Bool.and (Int.le n 57) (Int.le 48 n) in
  if (Bool.or (Bool.or alpha_lower alpha_upper) num) then true
  else match (String.make 1 x) with
       | "_" => true | "'" => true | "*" => true | _ => false
       end.

Ltac2 is_glob_char (x : char) : bool := Int.equal 42 (Char.to_int x).

Ltac2 glob (handle_glob : string -> string -> string) (x : string) : string :=
  let word_start := Ref.ref 0 in
  let glob_pos : int option Ref.ref := Ref.ref None in

  let end_of_word i : string :=
    if (Int.lt (Ref.get word_start) i) then
      let gs := (String.sub x (Ref.get word_start) (Int.sub i (Ref.get word_start))) in
      match (Ref.get glob_pos) with
      | None => gs
      | Some p => (* and if it has a glob in it, then handle it. *)
          let gp := (Int.sub p (Ref.get word_start)) in
          let pref := (String.sub gs 0 gp) in
          let suff := (String.sub gs (Int.add gp 1) (Int.sub (String.length gs) (Int.add gp 1))) in
          handle_glob pref suff
      end
    else ""
  in

  let rec loop i :=
    if (Int.le (String.length x) i) then end_of_word i
    else (if is_glob_char (String.get x i) then (Ref.set glob_pos (Some i)) else ();
          if (is_glob_identifier_char (String.get x i)) then
            loop (Int.add i 1)
          else
            let s := end_of_word i in
            Ref.set word_start (Int.add i 1);
            Ref.set glob_pos None;
            String.app (String.app s (String.make 1 (String.get x i))) (loop (Int.add i 1)))
  in loop 0.

Ltac2 get_matching_hyps (check : string -> bool) : string list :=
  orelse (fun () =>
            lazy_match! goal with
            | [ |- envs_entails (Envs _ ?es _) _ ] =>
                let rec loop es :=
                  match! es with
                  | Esnoc ?es (base.ident.INamed ?n) _ =>
                      let s := StringToIdent.coq_string_to_string n in
                      if check s then s :: (loop es)
                      else loop es
                  | _ => []
                  end in
                loop es
            | [ |- _ ] => Control.backtrack_tactic_failure "get_matching_hyps: was not run with Iris context"
            end)
    (fun _ => Control.throw (Tactic_failure (Some (Message.of_string "get_matching_hyps: was not run with Iris context")))).

Module String.
Ltac2 is_prefix pref s :=
  if Int.lt (String.length pref) (String.length s) then
    let pref' := (String.sub s 0 (String.length pref)) in
    String.equal pref pref'
  else false.

Ltac2 is_suffix suff s :=
  if Int.lt (String.length suff) (String.length s) then
    let suff' := (String.sub s (Int.sub (String.length s) (String.length suff)) (String.length suff)) in
    String.equal suff suff'
  else false.

Ltac2 handle_ipm_glob pref suff :=
  let minlen := Int.add (String.length pref) (String.length suff) in
  String.concat " "
    (get_matching_hyps
       (fun s =>
          if (Int.ge (String.length s) minlen) then (* for overlapping [pref] and [suff] *)
            if is_prefix pref s then is_suffix suff s else false
          else false
    )).

Ltac2 glob_ipm s := IdentToString.string_to_coq_string (glob handle_ipm_glob s).

Section test.
Context `{PROP : bi}.
Lemma test (P Q : PROP) :
  P -∗ P -∗ P -∗ P -∗ Q.
Proof.
  iIntros "H1 H2 P1 P2".
  Ltac2 Eval glob_ipm "H*".
  Ltac2 Eval glob_ipm "*2".
Abort.
End test.
