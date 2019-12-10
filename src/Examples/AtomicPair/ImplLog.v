From Perennial.Examples Require Import AtomicPair.AtomicPairAPI.
From Perennial.Examples Require Import ExMach.ExMachAPI.

(* On-Disk Addresses *)
Definition log_commit := 0.
Definition main_fst := 1.
Definition main_snd := 2.
Definition log_fst := 3.
Definition log_snd := 4.

(* Memory addresses *)
Definition main_lock := 0.
Definition log_lock := 1.

Definition write (p: nat * nat) :=
  (_ <- lock log_lock;
   _ <- write_disk log_fst (fst p);
   _ <- write_disk log_snd (snd p);
   _ <- write_disk log_commit 1;
   _ <- lock main_lock;
   _ <- write_disk main_fst (fst p);
   _ <- write_disk main_snd (snd p);
   _ <- write_disk log_commit 0;
   _ <- unlock log_lock;
   unlock main_lock)%proc.

Definition read :=
  (_ <- lock main_lock;
   fst_val <- read_disk main_fst;
   snd_val <- read_disk main_snd; 
   _ <- unlock main_lock;
   Ret (fst_val, snd_val))%proc.

Definition recv :=
  (is_commit <- read_disk log_commit;
   match is_commit with
   | O => Ret tt
   | _ => 
     fst_val <- read_disk log_fst;
     snd_val <- read_disk log_snd; 
     _ <- write_disk main_fst (fst_val);
     _ <- write_disk main_snd (snd_val);
     write_disk log_commit 0
   end)%proc.

Definition impl : LayerImpl ExMach.Op AtomicPair.Op :=
  {| compile_op T (op: AtomicPair.Op T) :=
       match op with
       | AtomicPair.Write n => write n
       | AtomicPair.Read => read
       end;
     recover := Seq_Cons (recv) (Seq_Nil);
     (* init := Ret Initialized; *) |}.
