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

Definition is_alpha c :=
  (Ascii.leb "a" c && Ascii.leb c "z") || (Ascii.leb "A" c && Ascii.leb c "Z").

Definition is_num c := Ascii.leb "0" c && Ascii.leb c "9".
Definition is_id_char c := is_alpha c || is_num c || Ascii.eqb c "_" || Ascii.eqb c "'".

Definition err := sum string.
Notation throw := inl.
Notation ok := inr.

Definition glob (handle_glob : string -> string -> string) (x : string) : err string :=
  (fix loop out glob_prefix word_so_far x :=
     match x with
     | "" => match glob_prefix with
            | None => ok (out +:+ word_so_far)
            | Some pref => ok (out +:+ handle_glob pref word_so_far)
            end
     | String "*" x => match glob_prefix with
                      | Some _ => throw "two '*' characters in a single glob"
                      | None => loop out(Some word_so_far) "" x
                      end
     | String c x =>
         if (is_alpha c || is_num c || Ascii.eqb c "_" || Ascii.eqb c "'") then
           let word_so_far := (word_so_far +:+ (String c EmptyString)) in
           loop out glob_prefix word_so_far x
         else let out:= (match glob_prefix with
                         | None => (out +:+ word_so_far)
                         | Some pref => (out +:+ handle_glob pref word_so_far)
                         end) in
              loop (out +:+ (String c EmptyString)) None "" x
     end
  ) "" None "" x.

Definition handle_iris_glob pref suff := String.concat "" [pref; "1"; suff; " "; pref; "2"; suff].
Definition iris_glob := glob handle_iris_glob.
Time Eval compute in iris_glob "[Hstruct_*] [//] [$] [Hwg*_2]".
Time Eval vm_compute in iris_glob "[Hstruct_*] [//] [$] [Hwg*_2]".
Time Eval vm_compute in iris_glob "[Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2]".
Time Ltac2 Eval iris_glob "[Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2]".
Time Ltac2 Eval iris_glob "[Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2]".
Time Eval vm_compute in iris_glob "[Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2]".

(*
Module Slice.
#[abstract] Ltac2 Type 'a t := { a : 'a array; start : int; len : int }.
Ltac2 length (s : 'a t) := fst s.

Ltac2 from_array a : 'a t := (0, a).

Ltac2 slice_drop (s : 'a t) (num_to_drop : int) : 'a t :=
  if Int.lt (fst s) num_to_drop then
    Control.throw (Control.backtrack_tactic_failure "slice_drop fatal error: tried to drop too much")
  else (Int.sub (fst s) num_to_drop, snd s).

Ltac2 matchf (x : 'a t) (empty : unit -> 'b) (cons : 'a -> 'a t -> 'b) : 'b :=
  let (start, a) := x in
  if Int.ge start (Array.length a) then empty ()
  else cons (Array.get a start) (Int.add start 1, a).

End Slice. *)

Ltac2 for_range (limit : int) (body : int -> unit) :=
  let rec loop cur :=
     if (Int.lt cur limit) then (body cur; loop (Int.add 1 cur))
     else () in loop 0.

Module Slice.
#[abstract] Ltac2 Type 'a t := { a : 'a array; start : int; len : int }.

Ltac2 from_array a : 'a t := { a := a; start := 0; len := Array.length a }.

Ltac2 length s := s.(len).

Ltac2 nil := { a := Array.empty; start := 0; len := 0 }.

Ltac2 sub (s : 'a t) start e : 'a t :=
  Control.assert_bounds "Slice.sub failed: 0 ≤ start" (Int.le 0 start);
  Control.assert_bounds "Slice.sub failed: start ≤ s.(len)" (Int.le start (s.(len)));
  Control.assert_bounds "Slice.sub failed: start ≤ end " (Int.le start e);
  Control.assert_bounds "Slice.sub failed: end ≤ s.(len)" (Int.le e (s.(len)));
  { s with start := Int.add (s.(start)) start; len := (Int.sub e start) }.

Ltac2 get (s : 'a t) i : 'a :=
  Control.assert_bounds "Slice.get failed: 0 ≤ i" (Int.le 0 i);
  Control.assert_bounds "Slice.get failed: i < len" (Int.lt i (s.(len)));
  Array.get (s.(a)) (Int.add i (s.(start))).

End Slice.

Ltac2 for_slice (s : 'a Slice.t) (body : int -> 'a -> unit) :=
  let rec loop cur :=
    if (Int.lt cur (Slice.length s)) then (body cur (Slice.get s cur); loop (Int.add 1 cur))
    else ()
  in loop 0.

Ltac2 string_to_char_slice (s : string) : char Slice.t :=
  Slice.from_array (Array.init (String.length s) (fun i => String.get s i)).

Ltac2 char_slice_to_string (sl : char Slice.t) : string :=
  let s := String.make (Slice.length sl) (Char.of_int 0) in
  for_range (Slice.length sl) (fun i => String.set s i (Slice.get sl i));
  s.

Module StringBuilder.
#[abstract] Ltac2 Type t := { mutable data : char array; mutable pos : int }.

Ltac2 make () : t := { data := Array.make 8 (Char.of_int 0); pos := 0 }.

Ltac2 grow_to_cap x cap : unit :=
  let oldcap := (Array.length (x.(data))) in
  (if (Int.gt cap oldcap) then
     (* not enough space, so grow *)
     let doublecap := (Int.add oldcap oldcap) in
     let newcap := if (Int.lt doublecap cap) then cap else doublecap in
     let new_data := Array.make newcap (Char.of_int 0) in
     Array.lowlevel_blit (x.(data)) 0 new_data 0 (x.(pos));
     x.(data) := new_data
   else ()).

Ltac2 write_slice x (s : char Slice.t) : unit :=
  grow_to_cap x (Int.add (x.(pos)) (Slice.length s));
  for_slice s (fun _ c => Array.set (x.(data)) (x.(pos)) c; x.(pos) := Int.add 1 (x.(pos))).

Ltac2 write_string x (s : string) : unit :=
  grow_to_cap x (Int.add (x.(pos)) (String.length s));
  for_range (String.length s)
    (fun i => Array.set (x.(data)) (x.(pos)) (String.get s i); x.(pos) := Int.add 1 (x.(pos))).

Ltac2 put x (c : char) : unit :=
  grow_to_cap x (Int.add (x.(pos)) 1);
  Array.set (x.(data)) (x.(pos)) c;
  x.(pos) := Int.add 1 (x.(pos)).

Ltac2 get x : string :=
  let s := String.make (x.(pos)) (Char.of_int 0) in
  for_range (x.(pos)) (fun i => String.set s i (Array.get (x.(data)) i));
  s.

End StringBuilder.

Ltac2 glob' (handle_glob : string -> string -> string) (x : string) : string :=
  let x := string_to_char_slice x in
  let out := StringBuilder.make () in
  let glob_prefix := Ref.ref None in
  let word_start := Ref.ref 0 in

  let handle_word_end word_end :=
    let word := Slice.sub x (Ref.get word_start) word_end in
    match (Ref.get glob_prefix) with
    | None => StringBuilder.write_slice out word
    | Some g => StringBuilder.write_string out
                 (handle_glob (char_slice_to_string g) (char_slice_to_string word))
    end
  in
  for_slice x
    (fun pos c =>
       (if is_glob_char c then
          match (Ref.get glob_prefix) with
          | Some _ => Control.throw (Control.backtrack_tactic_failure "glob: two '*'s in one word")
          | None => ()
          end;
          Ref.set glob_prefix (Some (Slice.sub x (Ref.get word_start) pos));
          Ref.set word_start (Int.add pos 1)
        else ());
       if is_glob_identifier_char c then
         ()
       else
         (handle_word_end pos;
          StringBuilder.put out c;
          Ref.set glob_prefix None;
          Ref.set word_start (Int.add pos 1))
    );
  handle_word_end (Slice.length x);
  StringBuilder.get out.

Ltac2 iris_glob' x := glob' handle_iris_glob x.

Time Ltac2 Eval iris_glob "[Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2]".
Time Ltac2 Eval iris_glob' "[Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2]".
Time Eval vm_compute in iris_glob "[Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2] [Hstruct_*] [//] [$] [Hwg*_2]".

Ltac2 Eval glob'
  (fun pre post =>
     String.concat "" [pre; "GLOB"; post] )
  "[Hstruct_*] [//=] [$] [Hwg*_2]".
