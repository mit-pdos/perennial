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

Definition encode_read_req_xkind (ts : u64) (key : string) :=
  u64_le ts ++ encode_string key.

Definition encode_read_req (ts : u64) (key : string) (data : list u8) :=
  data = u64_le (U64 100) ++ encode_read_req_xkind ts key.

Definition encode_fast_prepare_req_xkind (ts : u64) (m : dbmap) (data : list u8) :=
  ∃ mdata, data = u64_le ts ++ mdata ∧ encode_dbmap m mdata.

Definition encode_fast_prepare_req (ts : u64) (m : dbmap) (data : list u8) :=
  ∃ reqdata, data = u64_le (U64 201) ++ reqdata ∧ encode_fast_prepare_req_xkind ts m reqdata.

Definition encode_validate_req_xkind (ts rank : u64) (m : dbmap) (data : list u8) :=
  ∃ mdata, data = u64_le ts ++ u64_le rank ++ mdata ∧ encode_dbmap m mdata.

Definition encode_validate_req (ts rank : u64) (m : dbmap) (data : list u8) :=
  ∃ reqdata, data = u64_le (U64 202) ++ reqdata ∧ encode_validate_req_xkind ts rank m reqdata.

Definition encode_req_of_ts_rank_xkind (ts rank : u64) := u64_le ts ++ u64_le rank.

Definition encode_req_of_ts_rank (kind : u64) (ts rank : u64) (data : list u8) :=
  data = u64_le kind ++ encode_req_of_ts_rank_xkind ts rank.

Definition encode_commit_req_xkind (ts : u64) (m : dbmap) (data : list u8) :=
  ∃ mdata, data = u64_le ts ++ mdata ∧ encode_dbmap m mdata.

Definition encode_commit_req (ts : u64) (m : dbmap) (data : list u8) :=
  ∃ reqdata, data = u64_le (U64 300) ++ reqdata ∧ encode_commit_req_xkind ts m reqdata.

Definition encode_abort_req_xkind (ts : u64) := u64_le ts.

Definition encode_abort_req (ts : u64) (data : list u8) :=
  data = u64_le (U64 301) ++ encode_abort_req_xkind ts.

Definition encode_txnreq (req : txnreq) (data : list u8) :=
  match req with
  | ReadReq ts key => encode_read_req ts key data
  | FastPrepareReq ts pwrs => encode_fast_prepare_req ts pwrs data
  | ValidateReq ts rank pwrs => encode_validate_req ts rank pwrs data
  | PrepareReq ts rank => encode_req_of_ts_rank (U64 203) ts rank data
  | UnprepareReq ts rank => encode_req_of_ts_rank (U64 204) ts rank data
  | QueryReq ts rank => encode_req_of_ts_rank (U64 205) ts rank data
  | RefreshReq ts rank => encode_req_of_ts_rank (U64 210) ts rank data
  | CommitReq ts pwrs => encode_commit_req ts pwrs data
  | AbortReq ts => encode_abort_req ts data
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
