From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip Require Import base encode.

Inductive txnreq :=
| ReadReq        (ts : u64) (key : byte_string)
| FastPrepareReq (ts : u64) (pwrs : dbmap) (ptgs : txnptgs)
| ValidateReq    (ts : u64) (rank : u64) (pwrs : dbmap) (ptgs : txnptgs)
| PrepareReq     (ts : u64) (rank : u64)
| UnprepareReq   (ts : u64) (rank : u64)
| QueryReq       (ts : u64) (rank : u64)
| InquireReq     (ts : u64) (rank : u64) (cid : coordid)
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
Proof.
  refine (inj_countable'
            (λ x, match x with
                  | ReadReq ts key => inl (ts, key)
                  | FastPrepareReq ts pwrs ptgs => inr (inl (ts, pwrs, ptgs))
                  | ValidateReq ts rank pwrs ptgs => inr (inr (inl (ts, rank, pwrs, ptgs)))
                  | PrepareReq ts rank => inr (inr (inr (inl (ts, rank))))
                  | UnprepareReq ts rank =>
                      inr (inr (inr (inr (inl (ts, rank)))))
                  | QueryReq ts rank =>
                      inr (inr (inr (inr (inr (inl (ts, rank))))))
                  | InquireReq ts rank cid =>
                      inr (inr (inr (inr (inr (inr (inl (ts, rank, cid)))))))
                  | RefreshReq ts rank =>
                      inr (inr (inr (inr (inr (inr (inr (inl (ts, rank))))))))
                  | CommitReq ts pwrs =>
                      inr (inr (inr (inr (inr (inr (inr (inr (inl (ts, pwrs)))))))))
                  | AbortReq ts =>
                      inr (inr (inr (inr (inr (inr (inr (inr (inr ts))))))))
                  end)
            (λ x, match x with
                  | inl (ts, key) => ReadReq ts key
                  | inr (inl (ts, pwrs, ptgs)) => FastPrepareReq ts pwrs ptgs
                  | inr (inr (inl (ts, rank, pwrs, ptgs))) => ValidateReq ts rank pwrs ptgs
                  | inr (inr (inr (inl (ts, rank)))) => PrepareReq ts rank
                  | inr (inr (inr (inr (inl (ts, rank))))) => UnprepareReq ts rank
                  | inr (inr (inr (inr (inr (inl (ts, rank)))))) =>
                      QueryReq ts rank
                  | inr (inr (inr (inr (inr (inr (inl (ts, rank, cid))))))) =>
                      InquireReq ts rank cid
                  | inr (inr (inr (inr (inr (inr (inr (inl (ts, rank)))))))) =>
                      RefreshReq ts rank
                  | inr (inr (inr (inr (inr (inr (inr (inr (inl (ts, pwrs))))))))) =>
                      CommitReq ts pwrs
                  | inr (inr (inr (inr (inr (inr (inr (inr (inr ts)))))))) =>
                      AbortReq ts
                  end)
            _).
  intros [| | | | | | | | |] => //=.
Qed.

Definition encode_read_req_xkind (ts : u64) (key : byte_string) :=
  u64_le ts ++ encode_string key.

Definition encode_read_req (ts : u64) (key : byte_string) (data : list u8) :=
  data = u64_le (U64 100) ++ encode_read_req_xkind ts key.

Definition encode_fast_prepare_req_xkind
  (ts : u64) (m : dbmap) (g : txnptgs) (data : list u8) :=
  ∃ mdata gdata, data = u64_le ts ++ mdata ++ gdata ∧
                 encode_dbmap m mdata ∧
                 encode_txnptgs g gdata.

Definition encode_fast_prepare_req
  (ts : u64) (m : dbmap) (g : txnptgs) (data : list u8) :=
  ∃ reqdata, data = u64_le (U64 201) ++ reqdata ∧ encode_fast_prepare_req_xkind ts m g reqdata.

Definition encode_validate_req_xkind
  (ts rank : u64) (m : dbmap) (g : txnptgs) (data : list u8) :=
  ∃ mdata gdata, data = u64_le ts ++ u64_le rank ++ mdata ++ gdata ∧
                 encode_dbmap m mdata ∧
                 encode_txnptgs g gdata.

Definition encode_validate_req
  (ts rank : u64) (m : dbmap) (g : txnptgs) (data : list u8) :=
  ∃ reqdata, data = u64_le (U64 202) ++ reqdata ∧ encode_validate_req_xkind ts rank m g reqdata.

Definition encode_ts_rank (ts rank : u64) := u64_le ts ++ u64_le rank.

Definition encode_txnreq_of_ts_rank (kind : u64) (ts rank : u64) (data : list u8) :=
  data = u64_le kind ++ encode_ts_rank ts rank.

Definition encode_inquire_req_xkind (ts rank : u64) (cid : coordid) :=
  encode_ts_rank ts rank ++ u64_le cid.1 ++ u64_le cid.2.

Definition encode_inquire_req (ts rank : u64) (cid : coordid) (data : list u8) :=
  data = u64_le (U64 206) ++ encode_inquire_req_xkind ts rank cid.

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
  | FastPrepareReq ts pwrs ptgs => encode_fast_prepare_req ts pwrs ptgs data
  | ValidateReq ts rank pwrs ptgs => encode_validate_req ts rank pwrs ptgs data
  | PrepareReq ts rank => encode_txnreq_of_ts_rank (U64 203) ts rank data
  | UnprepareReq ts rank => encode_txnreq_of_ts_rank (U64 204) ts rank data
  | QueryReq ts rank => encode_txnreq_of_ts_rank (U64 205) ts rank data
  | InquireReq ts rank cid => encode_inquire_req ts rank cid data
  | RefreshReq ts rank => encode_txnreq_of_ts_rank (U64 210) ts rank data
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

#[global]
Instance rpres_countable :
  Countable rpres.
Proof.
  refine (inj_countable'
            (λ x, match x with
                  | ReplicaOK => 0
                  | ReplicaCommittedTxn => 1
                  | ReplicaAbortedTxn => 2
                  | ReplicaStaleCoordinator => 3
                  | ReplicaFailedValidation => 4
                  | ReplicaInvalidRank => 5
                  | ReplicaWrongLeader => 6
                  end)
            (λ x, match x with
                  | 0 => _
                  | 1 => _
                  | 2 => _
                  | 3 => _
                  | 4 => _
                  | 5 => _
                  | _ => ReplicaWrongLeader
                  end)
            _).
  intros [| | | | | |] => //=.
Qed.

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

Inductive txnresp :=
| ReadResp        (ts : u64) (rid : u64) (key : byte_string) (ver : dbpver) (slow : bool)
| FastPrepareResp (ts : u64) (rid : u64) (res : rpres)
| ValidateResp    (ts : u64) (rid : u64) (res : rpres)
| PrepareResp     (ts : u64) (rank : u64) (rid : u64) (res : rpres)
| UnprepareResp   (ts : u64) (rank : u64) (rid : u64) (res : rpres)
| QueryResp       (ts : u64) (res : rpres)
| InquireResp     (ts : u64) (rank : u64) (pp : ppsl) (vd : bool) (pwrs : dbmap) (rid : u64) (cid : coordid) (res : rpres)
| CommitResp      (ts : u64) (res : rpres)
| AbortResp       (ts : u64) (res : rpres).

#[global]
Instance txnresp_eq_decision :
  EqDecision txnresp.
Proof. solve_decision. Qed.

#[global]
Instance txnresp_countable :
  Countable txnresp.
Proof.
  refine (inj_countable'
            (λ x, match x with
                  | ReadResp ts rid key ver slow => inl (ts, rid, key, ver, slow)
                  | FastPrepareResp ts rid res => inr (inl (ts, rid, res))
                  | ValidateResp ts rid res => inr (inr (inl (ts, rid, res)))
                  | PrepareResp ts rank rid res => inr (inr (inr (inl (ts, rank, rid, res))))
                  | UnprepareResp ts rank rid res =>
                      inr (inr (inr (inr (inl (ts, rank, rid, res)))))
                  | QueryResp ts res =>
                      inr (inr (inr (inr (inr (inl (ts, res))))))
                  | InquireResp ts rank pp vd pwrs rid cid res =>
                      inr (inr (inr (inr (inr (inr (inl (ts, rank, pp, vd, pwrs, rid, cid, res)))))))
                  | CommitResp ts res =>
                      inr (inr (inr (inr (inr (inr (inr (inl (ts, res))))))))
                  | AbortResp ts res =>
                      inr (inr (inr (inr (inr (inr (inr (inr (ts, res))))))))
                  end)
            (λ x, match x with
                  | inl (ts, rid, key, ver, slow) => ReadResp ts rid key ver slow
                  | inr (inl (ts, rid, res)) => FastPrepareResp ts rid res
                  | inr (inr (inl (ts, rid, res))) => ValidateResp ts rid res
                  | inr (inr (inr (inl (ts, rank, rid, res)))) => PrepareResp ts rank rid res
                  | inr (inr (inr (inr (inl (ts, rank, rid, res))))) =>
                      UnprepareResp ts rank rid res
                  | inr (inr (inr (inr (inr (inl (ts, res)))))) =>
                      QueryResp ts res
                  | inr (inr (inr (inr (inr (inr (inl (ts, rank, pp, vd, pwrs, rid, cid, res))))))) =>
                      InquireResp ts rank pp vd pwrs rid cid res
                  | inr (inr (inr (inr (inr (inr (inr (inl (ts, res)))))))) =>
                      CommitResp ts res
                  | inr (inr (inr (inr (inr (inr (inr (inr (ts, res)))))))) =>
                      AbortResp ts res
                  end)
            _).
  intros [| | | | | | | |] => //=.
Qed.

Definition encode_read_resp_xkind
  (ts rid : u64) (key : byte_string) (ver : dbpver) (slow : bool) :=
  u64_le ts ++ u64_le rid ++ encode_string key ++
    encode_dbpver ver ++ [if slow then U8 1 else U8 0].

Definition encode_read_resp
  (ts rid : u64) (key : byte_string) (ver : dbpver) (slow : bool) :=
  u64_le (U64 100) ++ encode_read_resp_xkind ts rid key ver slow.

Definition encode_ts_rid_res (ts rid : u64) (res : rpres) :=
  u64_le ts ++ u64_le rid ++ u64_le (rpres_to_u64 res).

Definition encode_fast_prepare_resp (ts rid : u64) (res : rpres) :=
  u64_le (U64 201) ++ encode_ts_rid_res ts rid res.

Definition encode_validate_resp (ts rid : u64) (res : rpres) :=
  u64_le (U64 202) ++ encode_ts_rid_res ts rid res.

Definition encode_ts_rank_rid_res (ts rank rid : u64) (res : rpres) :=
  u64_le ts ++ u64_le rank ++ u64_le rid ++ u64_le (rpres_to_u64 res).

Definition encode_prepare_resp (ts rank rid : u64) (res : rpres) :=
  u64_le (U64 203) ++ encode_ts_rank_rid_res ts rank rid res.

Definition encode_unprepare_resp (ts rank rid : u64) (res : rpres) :=
  u64_le (U64 204) ++ encode_ts_rank_rid_res ts rank rid res.

Definition encode_ts_res (ts : u64) (res : rpres) :=
  u64_le ts ++ u64_le (rpres_to_u64 res).

Definition encode_query_resp (ts : u64) (res : rpres) :=
  u64_le (U64 205) ++ encode_ts_res ts res.

Definition encode_inquire_resp_xkind
  (ts : u64) (rank : u64) (pp : ppsl) (vd : bool) (pwrs : dbmap) (rid : u64) (cid : coordid)
  (res : rpres) (data : list u8) :=
  if vd
  then ∃ mdata, data = u64_le ts ++ u64_le rid ++ u64_le rank ++ encode_ppsl pp ++
                         [if vd then W8 1 else W8 0] ++
                         u64_le cid.1 ++ u64_le cid.2 ++ u64_le (rpres_to_u64 res) ++ mdata ∧
                encode_dbmap pwrs mdata
  else data = u64_le ts ++ u64_le rid ++ u64_le rank ++ encode_ppsl pp ++
                [if vd then W8 1 else W8 0] ++  u64_le cid.1 ++ u64_le cid.2 ++
                u64_le (rpres_to_u64 res).

Definition encode_inquire_resp
  (ts : u64) (rank : u64) (pp : ppsl) (vd : bool) (pwrs : dbmap) (rid : u64) (cid : coordid)
  (res : rpres) (data : list u8) :=
  ∃ reqdata, data = u64_le (U64 206) ++ reqdata ∧
             encode_inquire_resp_xkind ts rank pp vd pwrs rid cid res reqdata.

Definition encode_commit_resp (ts : u64) (res : rpres) :=
  u64_le (U64 300) ++ encode_ts_res ts res.

Definition encode_abort_resp (ts : u64) (res : rpres) :=
  u64_le (U64 301) ++ encode_ts_res ts res.

Definition encode_txnresp (resp : txnresp) (data : list u8) :=
  match resp with
  | ReadResp ts rid key ver slow => data = encode_read_resp ts rid key ver slow
  | FastPrepareResp ts rid res => data = encode_fast_prepare_resp ts rid res
  | ValidateResp ts rid res => data = encode_validate_resp ts rid res
  | PrepareResp ts rank rid res => data = encode_prepare_resp ts rank rid res
  | UnprepareResp ts rank rid res => data = encode_unprepare_resp ts rank rid res
  | QueryResp ts res => data = encode_query_resp ts res
  | InquireResp ts rank pp vd pwrs rid cid res => encode_inquire_resp ts rank pp vd pwrs rid cid res data
  | CommitResp ts res => data = encode_commit_resp ts res
  | AbortResp ts res => data = encode_abort_resp ts res
  end.
