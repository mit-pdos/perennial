From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip Require Import base encode.

Inductive txnreq :=
| ReadReq        (ts : u64) (key : string)
| FastPrepareReq (ts : u64) (pwrs : dbmap)
| ValidateReq    (ts : u64) (rank : u64) (pwrs : dbmap)
| PrepareReq     (ts : u64) (rank : u64)
| UnprepareReq   (ts : u64) (rank : u64)
| QueryReq       (ts : u64) (rank : u64)
| RefreshReq     (ts : u64) (rank : u64)
| CommitReq      (ts : u64) (pwrs : dbmap)
| AbortReq       (ts : u64).

#[global]
Instance txnreq_eq_decision :
  EqDecision txnreq.
Proof. solve_decision. Qed.

#[global]
Instance txnreq_countable :
  Countable txnreq.
Admitted.

Definition encode_fast_prepare_req (ts : u64) (pwrs : dbmap) (data : list u8) :=
  ∃ datapwrs, data = u64_le (U64 201) ++ u64_le ts ++ datapwrs ∧ encode_dbmap pwrs datapwrs.

Definition encode_txnreq (req : txnreq) (data : list u8) :=
  match req with
  | FastPrepareReq ts pwrs => encode_fast_prepare_req ts pwrs data
  | _ => True
  end.

Inductive rpres :=
| ReplicaOK
| ReplicaCommittedTxn
| ReplicaAbortedTxn
| ReplicaStaleCoordinator
| ReplicaFailedValidation
| ReplicaInvalidRank
| ReplicaWrongLeader.

#[global]
  Instance rpres_eq_decision :
  EqDecision rpres.
Proof. solve_decision. Qed.

Inductive txnresp :=
| ReadResp        (ts : u64) (rid : u64) (key : string) (ver : dbpver) (slow : bool)
| FastPrepareResp (ts : u64) (rid : u64) (res : rpres)
| ValidateResp    (ts : u64) (rid : u64) (res : rpres)
| PrepareResp     (ts : u64) (rank : u64) (rid : u64) (res : rpres)
| UnprepareResp   (ts : u64) (rank : u64) (rid : u64) (res : rpres)
| QueryResp       (ts : u64) (res : rpres)
| CommitResp      (ts : u64) (res : rpres)
| AbortResp       (ts : u64) (res : rpres).

#[global]
  Instance txnresp_eq_decision :
  EqDecision txnresp.
Proof. solve_decision. Qed.

#[global]
  Instance txnresp_countable :
  Countable txnresp.
Admitted.

Definition encode_txnresp (resp : txnresp) : list u8.
Admitted.
