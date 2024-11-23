From Perennial.program_proof.tulip Require Export prelude.
From Goose.github_com.mit_pdos.tulip Require Export
  backup gcoord index params quorum replica tulip tuple txn txnlog util.

Definition dbval_to_val (v : dbval) : val :=
  match v with
  | Some s => (#true, (#(LitString s), #()))
  | None => (#false, (zero_val stringT, #()))
  end.

Definition dbval_from_val (v : val) : option dbval :=
  match v with
  | (#(LitBool b), (#(LitString s), #()))%V => if b then Some (Some s) else Some None
  | _ => None
  end.

#[global]
Instance dbval_into_val : IntoVal dbval.
Proof.
  refine {|
      to_val := dbval_to_val;
      from_val := dbval_from_val;
      IntoVal_def := None;
    |}.
  intros v.
  by destruct v.
Defined.

#[global]
Instance dbval_into_val_for_type : IntoValForType dbval (boolT * (stringT * unitT)%ht).
Proof. constructor; [done | done | intros [v |]; by auto]. Defined.

Definition dbmod_to_val (x : dbmod) : val :=
  (#(LitString x.1), (dbval_to_val x.2, #())).

Definition dbmod_from_val (v : val) : option dbmod :=
  match v with
  | (#(LitString k), (dbv, #()))%V => match dbval_from_val dbv with
                                     | Some x => Some (k, x)
                                     | _ => None
                                     end
  | _ => None
  end.

#[global]
Instance dbmod_into_val : IntoVal dbmod.
Proof.
  refine {|
      to_val := dbmod_to_val;
      from_val := dbmod_from_val;
      IntoVal_def := ("", None);
    |}.
  intros [k v].
  by destruct v.
Defined.

Definition ppsl_to_val (v : ppsl) : val := (#v.1, (#v.2, #())).

Definition ppsl_from_val (v : val) : option ppsl :=
  match v with
  | (#(LitInt n), (#(LitBool b), #()))%V => Some (n, b)
  | _ => None
  end.

#[global]
Instance ppsl_into_val : IntoVal ppsl.
Proof.
  refine {|
      to_val := ppsl_to_val;
      from_val := ppsl_from_val;
      IntoVal_def := (W64 0, false);
    |}.
  intros v.
  by destruct v.
Defined.

Definition u64_dbval_to_val (x : u64 * dbval) : val := (#x.1, (dbval_to_val x.2, #())).

Definition u64_dbval_from_val (v : val) : option (u64 * dbval) :=
  match v with
  | (#(LitInt n), (dbv, #()))%V => match dbval_from_val dbv with
                                  | Some x => Some (n, x)
                                  | _ => None
                                  end
  | _ => None
  end.

#[global]
Instance u64_dbval_into_val : IntoVal (u64 * dbval).
Proof.
  refine {|
      to_val := u64_dbval_to_val;
      from_val := u64_dbval_from_val;
      IntoVal_def := (W64 0, None);
    |}.
  intros [n v].
  by destruct v.
Defined.

#[global]
Instance u64_dbval_into_val_for_type :
  IntoValForType (u64 * dbval) (uint64T * (boolT * (stringT * unitT) * unitT)%ht).
Proof.
  constructor; [done | done |].
  intros [t [v |]]; by auto 10.
Defined.

Definition ccommand_to_val (pwrsS : Slice.t) (c : ccommand) : val :=
  match c with
  | CmdCommit ts _ => (#(U64 1), (#(U64 ts), (to_val pwrsS, (zero_val stringT, #()))))
  | CmdAbort ts => (#(U64 2), (#(U64 ts), (Slice.nil, (zero_val stringT, #()))))
  end.

Inductive rpres :=
| ReplicaOK
| ReplicaCommittedTxn
| ReplicaAbortedTxn
| ReplicaStaleCoordinator
| ReplicaFailedValidation
| ReplicaInvalidRank
| ReplicaWrongLeader.

Definition rpres_to_u64 (r : rpres) :=
  match r with
  | ReplicaOK => (U64 0)
  | ReplicaCommittedTxn => (U64 1)
  | ReplicaAbortedTxn => (U64 2)
  | ReplicaStaleCoordinator => (U64 3)
  | ReplicaFailedValidation => (U64 4)
  | ReplicaInvalidRank => (U64 5)
  | ReplicaWrongLeader => (U64 6)
  end.

#[global]
Instance rpres_to_u64_inj :
  Inj eq eq rpres_to_u64.
Proof. intros x y H. by destruct x, y. Defined.

Inductive txnphase :=
| TxnPrepared
| TxnCommitted
| TxnAborted.

Definition txnphase_to_u64 (p : txnphase) :=
  match p with
  | TxnPrepared => (U64 0)
  | TxnCommitted => (U64 1)
  | TxnAborted => (U64 2)
  end.

#[global]
Instance txnphase_to_u64_inj :
  Inj eq eq txnphase_to_u64.
Proof. intros x y H. by destruct x, y. Defined.

Section def.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition own_dbmap_in_slice s (l : list dbmod) (m : dbmap) : iProp Σ :=
    own_slice s (struct.t WriteEntry) (DfracOwn 1) l ∗ ⌜map_to_list m ≡ₚ l⌝.

  Definition own_pwrs_slice (pwrsS : Slice.t) (c : ccommand) : iProp Σ :=
    match c with
    | CmdCommit _ pwrs => (∃ pwrsL : list dbmod, own_dbmap_in_slice pwrsS pwrsL pwrs)
    | _ => True
    end.

  Definition validate_outcome γ gid rid ts res : iProp Σ :=
    match res with
    | ReplicaOK => is_replica_validated_ts γ gid rid ts
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => False
    | ReplicaFailedValidation => True
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  #[global]
  Instance validate_outcome_persistent γ gid rid ts res :
    Persistent (validate_outcome γ gid rid ts res).
  Proof. destruct res; apply _. Defined.

  Definition fast_prepare_outcome γ gid rid ts res : iProp Σ :=
    match res with
    | ReplicaOK => is_replica_validated_ts γ gid rid ts ∗
                  is_replica_pdec_at_rank γ gid rid ts O true
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => True
    | ReplicaFailedValidation => is_replica_pdec_at_rank γ gid rid ts O false
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  #[global]
  Instance fast_prepare_outcome_persistent γ gid rid ts res :
    Persistent (fast_prepare_outcome γ gid rid ts res).
  Proof. destruct res; apply _. Defined.

  Definition accept_outcome γ gid rid ts rank pdec res : iProp Σ :=
    match res with
    | ReplicaOK => is_replica_pdec_at_rank γ gid rid ts rank pdec
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => True
    | ReplicaFailedValidation => False
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  #[global]
  Instance accept_outcome_persistent γ gid rid ts rank pdec res :
    Persistent (accept_outcome γ gid rid ts rank pdec res).
  Proof. destruct res; apply _. Defined.

  Definition query_outcome γ ts res : iProp Σ :=
    match res with
    | ReplicaOK => True
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => True
    | ReplicaFailedValidation => False
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  #[global]
  Instance query_outcome_persistent γ ts res :
    Persistent (query_outcome γ ts res).
  Proof. destruct res; apply _. Defined.

  Definition safe_group_txnphase γ ts gid (phase : txnphase) : iProp Σ :=
    match phase with
    | TxnPrepared => quorum_prepared γ gid ts ∗ quorum_validated γ gid ts
    | TxnCommitted => ∃ wrs, is_txn_committed γ ts wrs
    | TxnAborted => is_txn_aborted γ ts ∨ quorum_unprepared γ gid ts
    end.

  #[global]
  Instance safe_group_txnphase_persistent γ ts gid phase :
    Persistent (safe_group_txnphase γ ts gid phase).
  Proof. destruct phase; apply _. Defined.

  Definition safe_txnphase γ ts (phase : txnphase) : iProp Σ :=
    match phase with
    | TxnPrepared => (∃ wrs, all_prepared γ ts wrs)
    | TxnCommitted => (∃ wrs, is_txn_committed γ ts wrs)
    | TxnAborted => is_txn_aborted γ ts
    end.

  #[global]
  Instance safe_txnphase_persistent γ ts phase :
    Persistent (safe_txnphase γ ts phase).
  Proof. destruct phase; apply _. Defined.

End def.
