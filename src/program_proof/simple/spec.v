From stdpp Require Import decidable countable gmap.
From Coq Require Import String List.
From RecordUpdate Require Import RecordUpdate.
From Perennial.Helpers Require Import Transitions Integers.
Set Implicit Arguments.

Coercion Z.of_nat : nat >-> Z.

Module SimpleNFS.

Notation "x <- p1 ; p2" := (bind p1 (fun x => p2))
                            (at level 20, p1 at level 100, p2 at level 200, right associativity).

#[global]
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
  ret (Build_fattr (W64 (length i))).

Definition full_getattr (f : fh) : transition State (res fattr) :=
  if decide (f = W64 1) then
    r <- suchThat (gen:=fun _ _ => None) (λ _ _, True);
    ret (OK r)
  else
    wrapper f (getattr f).

Declare Scope slice.
Delimit Scope slice with slice.
Notation "a [: n ]" := (take n a) (at level 20, n at level 50, format "a [: n ]") : slice.
Notation "a [ n :]" := (drop n a) (at level 10, n at level 50, format "a [ n :]") : slice.
Open Scope slice.

Definition setattr (f : fh) (a : sattr) (i : buf) : transition State unit :=
  match (sattr_size a) with
  | None => ret tt
  | Some sz =>
    let i' := i[:Z.to_nat $ uint.Z sz] ++ replicate (Z.to_nat (uint.Z sz - (Z.of_nat $ length i))) (W8 0) in
    _ <- modify (fun s => insert f i' s);
    ret tt
  end.

Definition read (f : fh) (off : u64) (count : u32) (i : buf) : transition State (bool * buf) :=
  let off := uint.Z off in
  readcount <- suchThat (gen:=fun _ _ => None) (λ s readcount, readcount = 0 ∨ (0 ≤ readcount ∧
                                                           off + readcount ≤ length i));
  let resbuf := take (Z.to_nat readcount) (drop (Z.to_nat off) i) in
  let reseof := if Z.ge_dec (off + readcount) (length i) then true else false in
  ret (reseof, resbuf).

Definition write (f : fh) (off : u64) (data : buf) (i : buf) : transition State u32 :=
  let off := uint.Z off in
  _ <- check (off ≤ Z.of_nat $ length i);
  let i' := i[:Z.to_nat off] ++ data ++ i[Z.to_nat (off + (Z.of_nat $ length data)) :] in
  _ <- modify (fun s => insert f i' s);
  ret (W32 (length data)).

End SimpleNFS.
