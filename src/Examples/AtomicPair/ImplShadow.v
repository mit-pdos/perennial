From Perennial.Examples Require Import AtomicPair.AtomicPairAPI.
From Perennial.Examples Require Import ExMach.ExMachAPI.

(* On-Disk Addresses *)
Definition ptr_addr := 0.
Definition copy0_fst := 1.
Definition copy0_snd := 2.
Definition copy1_fst := 3.
Definition copy1_snd := 4.

(* Memory addresses *)
Definition lock_addr := 0.

Definition read_addrs (ptr_val: nat) : nat * nat :=
  match ptr_val with
  | O => (copy0_fst, copy0_snd)
  | _ => (copy1_fst, copy1_snd)
  end.

Definition write_addrs (ptr_val: nat) : nat * nat :=
  match ptr_val with
  | 0 => (copy1_fst, copy1_snd)
  | _ => (copy0_fst, copy0_snd)
  end.

Definition swap_ptr (ptr_val: nat) : nat :=
  match ptr_val with
  | O => 1
  | _ => O
  end.

Definition write (p: nat * nat) :=
  (_ <- lock lock_addr;
   ptr <- read_disk ptr_addr;
   _ <- write_disk (fst (write_addrs ptr)) (fst p);
   _ <- write_disk (snd (write_addrs ptr)) (snd p);
   _ <- write_disk ptr_addr (swap_ptr ptr);
   unlock lock_addr)%proc.

Definition read  :=
  (_ <- lock lock_addr;
   ptr <- read_disk ptr_addr;
   fst_val <- read_disk (fst (read_addrs ptr));
   snd_val <- read_disk (snd (read_addrs ptr));
   _ <- unlock lock_addr;
   Ret (fst_val, snd_val))%proc.

Definition recv : proc ExMach.Op _ := Ret tt.

Definition impl : LayerImpl ExMach.Op AtomicPair.Op :=
  {| compile_op T (op: AtomicPair.Op T) :=
       match op with
       | AtomicPair.Write n => write n
       | AtomicPair.Read => read
       end;
     recover := Seq_Cons (recv) (Seq_Nil);
     (* init := Ret Initialized; *) |}.
