From stdpp Require Export strings.
From iris.proofmode Require Import base tokens.
From iris.prelude Require Import options.

Import Ltac2.

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
  in
  loop 0.

Ltac2 Eval glob
  (fun pre post =>
     String.concat "" [pre; "GLOB"; post] )
  "[Hstruct_*] [//=] [$] [Hwg*_2]".

Ltac2 handle_iris_glob pref suff := String.concat "" [pref; "1"; suff; " "; pref; "2"; suff].
Ltac2 iris_glob x := glob handle_iris_glob x.

Ltac2 Eval iris_glob "[Hstruct_*] [//] [$] [Hwg*_2]".
