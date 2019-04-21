From Coq Require Import List.

From stdpp Require Import gmap.
From RecoveryRefinement Require Export Lib.
From RecoveryRefinement Require Import TwoDiskAPI OneDiskAPI.
Import TwoDisk.

Definition write (addr: nat) (v: nat) :=
  (_ <- lock addr;
   _ <- write_disk d0 addr v;
   _ <- write_disk d1 addr v;
   unlock addr)%proc.

Definition read (addr: nat) :=
  (_ <- lock addr;
   v <- (rd0 <- read_disk d0 addr;
           match rd0 with
           | Some v => Ret v
           | None => rd1 <- read_disk d1 addr;
             match rd1 with
             | Some v => Ret v
             | None => Ret 0
             end
           end);
   _ <- unlock addr;
   Ret v)%proc.

Definition fixup (a: addr) : proc Op unit :=
  (rd0 <- read_disk d0 a;
   match rd0 with
   | None => Ret tt
   | Some v =>
     write_disk d1 a v
   end)%proc.

Fixpoint recover_at (a: addr) : proc Op unit :=
  (_ <- fixup a;
   match a with
   | 0 => Ret tt
   | S n => recover_at n
   end)%proc.

Definition recv := recover_at size.

Definition impl : LayerImpl TwoDisk.Op OneDisk.Op :=
  {| compile_op T (op: OneDisk.Op T) :=
       match op with
       | OneDisk.Write_Disk a v => write a v
       | OneDisk.Read_Disk a => read a
       end;
     recover := Seq_Cons (recv) (Seq_Nil); |}.