From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip Require Import encode.


Inductive pxreq :=
| RequestVoteReq (term : u64) (lsnlc : u64)
| AppendEntriesReq (term : u64) (lsnlc : u64) (lsne : u64) (ents : list byte_string).

#[global]
Instance pxreq_eq_decision :
  EqDecision pxreq.
Proof. solve_decision. Qed.

#[global]
Instance pxreq_countable :
  Countable pxreq.
Proof.
  refine (inj_countable'
            (λ x, match x with
                  | RequestVoteReq term lsnlc => inl (term, lsnlc)
                  | AppendEntriesReq term lsnlc lsne ents => inr (term, lsnlc, lsne, ents)
                  end)
            (λ x, match x with
                  | inl (term, lsnlc) => RequestVoteReq term lsnlc
                  | inr (term, lsnlc, lsne, ents) => AppendEntriesReq term lsnlc lsne ents
                  end)
            _).
  intros [|] => //=.
Qed.

Definition encode_request_vote_req_xkind (term lsnlc : u64) :=
  u64_le term ++ u64_le lsnlc.

Definition encode_request_vote_req (term lsnlc : u64) :=
  u64_le (U64 0) ++ encode_request_vote_req_xkind term lsnlc.

Definition encode_append_entries_req_xkind
  (term lsnlc lsne : u64) (ents : list byte_string) :=
  u64_le term ++ u64_le lsnlc ++ u64_le lsne ++ encode_strings ents.

Definition encode_append_entries_req
  (term lsnlc lsne : u64) (ents : list byte_string) :=
  u64_le (U64 1) ++ encode_append_entries_req_xkind term lsnlc lsne ents.

Definition encode_pxreq (req : pxreq) : list u8 :=
  match req with
  | RequestVoteReq term lsnlc =>
      encode_request_vote_req term lsnlc
  | AppendEntriesReq term lsnlc lsne ents =>
      encode_append_entries_req term lsnlc lsne ents
  end.

Inductive pxresp :=
| RequestVoteResp (nid term terme : u64) (ents : list byte_string)
| AppendEntriesResp (nid term lsneq : u64).

#[global]
Instance pxresp_eq_decision :
  EqDecision pxresp.
Proof. solve_decision. Qed.

#[global]
Instance pxresp_countable :
  Countable pxresp.
Proof.
  refine (inj_countable'
            (λ x, match x with
                  | RequestVoteResp nid term terme ents => inl (nid, term, terme, ents)
                  | AppendEntriesResp nid term lsneq => inr (nid, term, lsneq)
                  end)
            (λ x, match x with
                  | inl (nid, term, terme, ents) => RequestVoteResp nid term terme ents
                  | inr (nid, term, lsneq) => AppendEntriesResp nid term lsneq
                  end)
            _).
  intros [|] => //=.
Qed.

Definition encode_request_vote_resp_xkind
  (nid term terme : u64) (ents : list byte_string) :=
  u64_le nid ++ u64_le term ++ u64_le terme ++ encode_strings ents.

Definition encode_request_vote_resp
  (nid term terme : u64) (ents : list byte_string) :=
  u64_le (U64 0) ++ encode_request_vote_resp_xkind nid term terme ents.

Definition encode_append_entries_resp_xkind (nid term lsneq : u64) :=
  u64_le nid ++ u64_le term ++ u64_le lsneq.

Definition encode_append_entries_resp (nid term lsneq : u64) :=
  u64_le (U64 1) ++ encode_append_entries_resp_xkind nid term lsneq.

Definition encode_pxresp (resp : pxresp) : list u8 :=
  match resp with
  | RequestVoteResp nid term terme ents =>
      encode_request_vote_resp nid term terme ents
  | AppendEntriesResp nid term lsneq =>
      encode_append_entries_resp nid term lsneq
  end.
