Require Import Logging2.Log2API.
Require Import ExMach.ExMachAPI.

(* On-Disk Addresses *)
Definition log_commit := 0.
Definition log_start := 1.

(* Memory addresses *)
Definition log_lock := 0.
Definition mem_lock := 1.
Definition mem_count_in_memory := 2.
Definition mem_count_on_disk := 3.
Definition mem_start := 4.

Definition log_data (pos : nat) :=
  log_start + pos.

Definition mem_data (pos : nat) :=
  mem_start + pos.

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

Fixpoint write_mem_blocks (l : list nat) (pos : nat) :=
  (
    match l with
    | nil =>
      Ret tt
    | b :: l' =>
      _ <- write_mem (mem_data pos) b;
      write_mem_blocks l' (pos+1)
    end
  )%proc.

Fixpoint read_mem_blocks (count : nat) (pos : nat) (res : list nat) :=
  (
    match count with
    | 0 => Ret res
    | S count' =>
      b <- read_mem (mem_data pos);
      read_mem_blocks count' (pos+1) (res ++ [b])
    end
  )%proc.

Definition disk_append :=
  ( _ <- lock log_lock;

    _ <- lock mem_lock;
    memlen <- read_mem mem_count_in_memory;
    l <- read_mem_blocks memlen 0 nil;
    _ <- write_mem mem_count_in_memory 0;

    disklen <- read_mem mem_count_on_disk;
    _ <- write_mem mem_count_on_disk (disklen+memlen);
    _ <- unlock mem_lock;

    _ <- write_blocks l disklen;
    _ <- write_disk log_commit (disklen+memlen);

    _ <- unlock log_lock;
    Ret tt
  )%proc.

Definition mem_append (l : list nat) :=
  ( _ <- lock mem_lock;
    memlen <- read_mem mem_count_in_memory;
    disklen <- read_mem mem_count_on_disk;
    if gt_dec (disklen + memlen + length l) log_size then
      _ <- unlock log_lock;
      Ret false
    else
      _ <- write_mem_blocks l memlen;
      _ <- write_mem mem_count_in_memory (memlen + length l);
      _ <- unlock mem_lock;
      Ret true
  )%proc.

Definition append (l : list nat) :=
  (
    ok <- mem_append l;
    if ok then
      _ <- disk_append;
      Ret true
    else
      Ret false
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
