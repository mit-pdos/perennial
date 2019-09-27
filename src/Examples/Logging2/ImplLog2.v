Require Import Logging2.Log2API.
Require Import ExMach.ExMachAPI.

(* On-Disk Addresses *)
Definition log_commit := 0.
Definition log_start := 1.

(* Memory addresses *)
Definition log_lock := 0.

Definition log_data (pos : nat) :=
  log_start + pos.

Fixpoint write_blocks (l : list nat) (pos : nat) :=
  (
    match l with
    | nil =>
      Ret tt
    | b :: l' =>
      _ <- write_disk (log_data pos) b;
      write_blocks l' (pos+1)
    end
  )%proc.

Definition append (l : list nat) :=
  ( _ <- lock log_lock;
    len <- read_disk log_commit;
    if gt_dec (len + length l) log_size then
      _ <- unlock log_lock;
      Ret false
    else
      _ <- write_blocks l len;
      _ <- write_disk log_commit (len+length l);
      _ <- unlock log_lock;
      Ret true
  )%proc.

Fixpoint read_blocks (count : nat) (pos : nat) (res : list nat) :=
  (
    match count with
    | 0 => Ret res
    | S count' =>
      b <- read_disk (log_data pos);
      read_blocks count' (pos+1) (res ++ [b])
    end
  )%proc.

Definition read :=
  ( _ <- lock log_lock;
    len <- read_disk log_commit;
    res <- read_blocks len 0 nil;
    _ <- unlock log_lock;
    Ret res
  )%proc.

Definition recv : proc ExMach.Op _ := Ret tt.

Definition impl : LayerImpl ExMach.Op Log2.Op :=
  {| compile_op T (op: Log2.Op T) :=
       match op with
       | Log2.Append l => append l
       | Log2.Read => read
       end;
     recover := Seq_Cons (recv) (Seq_Nil);
     (* init := Ret Initialized; *) |}.
