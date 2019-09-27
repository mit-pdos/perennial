Require Import Logging2.Log2API.
Require Import ExMach.ExMachAPI.

(* On-Disk Addresses *)
Definition log_commit := 0.
Definition log_fst := 1.
Definition log_snd := 2.

(* Memory addresses *)
Definition log_lock := 0.

Definition next_block (count : nat) :=
  match count with
  | 0 => log_fst
  | 1 => log_snd
  | _ => 0
  end.

Definition append (l : list nat) :=
  ( _ <- lock log_lock;
    hdr <- read_disk log_commit;
    if gt_dec (hdr + length l) 2 then
      _ <- unlock log_lock;
      Ret false
    else
      match l with
      | nil =>
        _ <- unlock log_lock;
        Ret true
      | x :: nil =>
        _ <- write_disk (next_block hdr) x;
        _ <- write_disk log_commit (hdr+1);
        _ <- unlock log_lock;
        Ret true
      | x :: y :: nil =>
        _ <- write_disk (next_block hdr) x;
        _ <- write_disk (next_block hdr+1) y;
        _ <- write_disk log_commit (hdr+2);
        _ <- unlock log_lock;
        Ret true
      | _ =>
        _ <- unlock log_lock;
        Ret false
      end
  )%proc.

Definition read :=
  ( _ <- lock log_lock;
    hdr <- read_disk log_commit;
    match hdr with
    | 0 =>
      _ <- unlock log_lock;
      Ret nil
    | 1 =>
      x <- read_disk log_fst;
      _ <- unlock log_lock;
      Ret (x :: nil)
    | 2 =>
      x <- read_disk log_fst;
      y <- read_disk log_snd;
      _ <- unlock log_lock;
      Ret (x :: y :: nil)
    | _ =>
      _ <- unlock log_lock;
      Ret nil
    end
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
