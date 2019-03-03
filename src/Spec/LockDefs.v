Inductive LockStatus := Locked | ReadLocked (num:nat) | Unlocked.
Inductive LockMode := Reader | Writer.

(* returns [Some s'] when the lock should be acquired to status s', and None
  if the lock would block *)
Definition lock_acquire (m:LockMode) (s:LockStatus) : option LockStatus :=
  match m, s with
  | Reader, ReadLocked n => Some (ReadLocked (S n))
  (* note that the number is one less than the number of readers, so that
       ReadLocked 0 means something *)
  | Reader, Unlocked => Some (ReadLocked 0)
  | Writer, Unlocked => Some Locked
  | _, _ => None
  end.

(* returns [Some s'] when the lock should be released to status s', and None if this usage is an error *)
Definition lock_release (m:LockMode) (s:LockStatus) : option LockStatus :=
  match m, s with
  | Reader, ReadLocked 0 => Some Unlocked
  | Reader, ReadLocked (S n) => Some (ReadLocked n)
  | Writer, Locked => Some Unlocked
  | _, _ => None
  end.

(* lock_available reports whether acquiring and releasing the lock atomically
  would succeed; phrased as an option unit for compatibility with readSome *)
Definition lock_available (m:LockMode) (s:LockStatus) : option unit :=
  match m, s with
  | Reader, ReadLocked _ => Some tt
  | _, Unlocked => Some tt
  | _, _ => None
  end.


Definition force_read_lock (s:LockStatus) : LockStatus :=
  match s with
  | ReadLocked n => ReadLocked (S n)
  | _ => ReadLocked 0
  end.

Definition force_read_unlock (s:LockStatus) : LockStatus :=
  match s with
  | ReadLocked (S n) => ReadLocked n
  | _ => Unlocked
  end.
