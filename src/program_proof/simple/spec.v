From stdpp Require Import decidable countable gmap.
From Coq Require Import List String.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Perennial.Helpers Require Import Transitions Integers.
From Perennial.algebra Require Import log_heap.
Require Import Extraction.
Set Implicit Arguments.
Open Scope string_scope.

Module SimpleNFS.

Notation "x <- p1 ; p2" := (bind p1 (fun x => p2))
                            (at level 20, p1 at level 100, p2 at level 200, right associativity).

Existing Instance fallback_genBool | 99.

Definition fh := u64.

Inductive res T :=
| OK (v : T)
| Err
.

Arguments Err {T}.

Record fattr := {
  fattr_size : u64;
}.

Record sattr := {
  sattr_size : option u64;
}.

Definition buf := list u8.

Inductive stable :=
| UNSTABLE
| SYNC
.

Record write_ok := {
  write_ok_count : u32;
  write_ok_committed : stable;
}.

Definition State := gmap u64 buf.

Definition wrapper (f : fh) `(fn : buf -> transition State T) : transition State (res T) :=
  i <- reads (fun s => s !! f);
  match i with
  | None => ret Err
  | Some i =>
    err <- suchThatBool (fun (_: State) (_ : bool) => true);
    if err then
      ret Err
    else
      r <- fn i;
      ret (OK r)
  end.

Definition getattr (f : fh) (i : buf) : transition State fattr :=
  ret (Build_fattr (U64 (length i))).

Definition setattr (f : fh) (a : sattr) (i : buf) : transition State unit :=
  match (sattr_size a) with
  | None => ret tt
  | Some sz =>
    let i' := app (firstn (int.nat sz) i) (replicate (int.nat sz - length i) (U8 0)) in
    _ <- modify (fun s => insert f i' s);
    ret tt
  end.

Definition read (f : fh) (off : u64) (count : u32) (i : buf) : transition State (bool * buf) :=
  readcount <- suchThat (gen:=fun _ _ => None) (λ s readcount, readcount = 0 ∨ int.nat off + readcount ≤ length i);
  let resbuf := firstn readcount (skipn (int.nat off) i) in
  let reseof := if ge_dec (int.nat off + readcount) (length i) then true else false in
  ret (reseof, resbuf).

Definition write (f : fh) (off : u64) (stab : stable) (data : buf) (i : buf) : transition State write_ok :=
  let i' := app i (replicate ((int.nat off + length data) - length i) (U8 0)) in
  let i'' := app (firstn (int.nat off) i')
             (app data (skipn (int.nat off + length data) i')) in
  _ <- modify (fun s => insert f i'' s);
  ret (Build_write_ok (U32 (length data)) stab).

End SimpleNFS.
