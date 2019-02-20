From Coq Require Import List.

Require Import AtomicPair.AtomicPairAPI.
Require Import ExMach.ExMachAPI.

(* On-Disk Addresses *)
Definition ptr_addr := 0.
Definition copy0_fst := 1.
Definition copy0_snd := 2.
Definition copy1_fst := 3.
Definition copy1_snd := 4.

(* Memory addresses *)
Definition lock_addr := 0.

Definition ptr_to_read_addrs (ptr_val: nat) : nat * nat :=
  match ptr_val with
  | O => (copy0_fst, copy0_snd)
  | _ => (copy1_fst, copy1_snd)
  end.

Definition ptr_to_write_addrs (ptr_val: nat) : nat * nat :=
  match ptr_val with
  | 1 => (copy0_fst, copy0_snd)
  | _ => (copy1_fst, copy1_snd)
  end.

Definition swap_ptr (ptr_val: nat) : nat :=
  match ptr_val with
  | O => 1
  | _ => O
  end.

Definition write (p: nat * nat) :=
  (_ <- lock lock_addr;
   ptr <- read_disk ptr_addr;
   let (fst_addr, snd_addr) := ptr_to_write_addrs ptr in
   _ <- write_disk fst_addr (fst p);
   _ <- write_disk snd_addr (snd p);
   _ <- write_disk ptr_addr (swap_ptr ptr);
   unlock lock_addr)%proc.

Definition read  :=
  (_ <- lock lock_addr;
   ptr <- read_disk ptr_addr;
   let (fst_addr, snd_addr) := ptr_to_read_addrs ptr in
   fst_val <- read_disk fst_addr;
   snd_val <- read_disk snd_addr;
   _ <- unlock lock_addr;
   Ret (fst_val, snd_val))%proc.