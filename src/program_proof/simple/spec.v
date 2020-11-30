From stdpp Require Import decidable countable gmap.
From Coq Require Import List String.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Perennial.Helpers Require Import Transitions Integers.
From Perennial.algebra Require Import log_heap.
Require Import Extraction.
Set Implicit Arguments.


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

Definition State := gmap u64 buf.

Definition wrapper (f : fh) {T} (fn : buf -> transition State T) : transition State (res T) :=
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

Definition full_getattr (f : fh) : transition State (res fattr) :=
  if decide (f = U64 1) then
    r <- suchThat (gen:=fun _ _ => None) (λ _ _, True);
    ret (OK r)
  else
    wrapper f (getattr f).

Definition setattr (f : fh) (a : sattr) (i : buf) : transition State unit :=
  match (sattr_size a) with
  | None => ret tt
  | Some sz =>
    let i' := take (int.nat sz) i ++ replicate (int.nat sz - length i) (U8 0) in
    _ <- modify (fun s => insert f i' s);
    ret tt
  end.

Definition read (f : fh) (off : u64) (count : u32) (i : buf) : transition State (bool * buf) :=
  let off := int.nat off in
  readcount <- suchThat (gen:=fun _ _ => None) (λ s readcount, readcount = 0 ∨ off + readcount ≤ length i);
  let resbuf := take readcount (drop off i) in
  let reseof := if ge_dec (off + readcount) (length i) then true else false in
  ret (reseof, resbuf).

Definition write (f : fh) (off : u64) (data : buf) (i : buf) : transition State u32 :=
  let off := int.nat off in
  _ <- check (off ≤ length i);
  let i' := take off i ++ data ++ drop (off + length data) i in
  _ <- modify (fun s => insert f i' s);
  ret (U32 (length data)).

End SimpleNFS.
