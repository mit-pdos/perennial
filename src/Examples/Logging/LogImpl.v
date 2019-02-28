From RecoveryRefinement Require Import Examples.Logging.LogAPI.
From RecoveryRefinement Require Import ExMach.ExMachAPI.

(* disk layout *)
Definition log_len := 0.
Definition log_idx i := 1 + i.

(* memory addresses *)
(* txn1 occupies two addresses *)
Definition txn1_start := 0.
(* txn2 occupies two addresses *)
Definition txn2_start := 2.
Definition state := 4.
Definition disk_lock := 5.
Definition state_lock := 6.

Inductive BufState :=
| Empty | Txn1 | Txn2
| Txn12 | Txn21
.

Definition enc_state (s:BufState) : nat.
  destruct s; [ exact 0 | exact 1 | exact 2 | exact 3 | exact 4 ].
Defined.

Definition dec_state (n:nat) : option BufState :=
  match n with
  | 0 => Some Empty
  | 1 => Some Txn1
  | 2 => Some Txn2
  | 3 => Some Txn12
  | 4 => Some Txn21
  | _ => None
  end.

Theorem enc_dec_id s : dec_state (enc_state s) = Some s.
Proof.
  destruct s; reflexivity.
Qed.
