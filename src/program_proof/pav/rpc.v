From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import auditor advrpc core serde server.

Section specs.
Context `{!heapGS Σ, !pavG Σ}.
Lemma wp_NewRpcServer ptr_serv serv :
  {{{
    "Hown_serv" ∷ server.Server.own ptr_serv serv
  }}}
  NewRpcServer #ptr_serv
  {{{
    ptr_rpcserv rpcserv, RET #ptr_rpcserv;
    "Hown_rpcserv" ∷ advrpc.Server.own ptr_rpcserv rpcserv
  }}}.
Proof. Admitted.

Lemma wp_NewRpcAuditor ptr_adtr :
  {{{
    "Hown_adtr" ∷ Auditor.valid ptr_adtr
  }}}
  NewRpcAuditor #ptr_adtr
  {{{
    ptr_rpcserv rpcserv, RET #ptr_rpcserv;
    "Hown_rpcserv" ∷ advrpc.Server.own ptr_rpcserv rpcserv
  }}}.
Proof. Admitted.

Lemma wp_CallServPut ptr_cli cli (uid : w64) sl_pk d0 (pk : list w8) :
  {{{
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk
  }}}
  CallServPut #ptr_cli #uid (slice_val sl_pk)
  {{{
    (err : bool) ptr_dig dig ptr_memb memb ptr_nonmemb nonmemb,
    RET (#ptr_dig, #ptr_memb, #ptr_nonmemb, #err);
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Herr" ∷ (if err then True else
      "#Hown_dig" ∷ SigDig.own ptr_dig dig ∗
      "Hown_memb" ∷ Memb.own ptr_memb memb ∗
      "Hown_nonmemb" ∷ NonMemb.own ptr_nonmemb nonmemb)
  }}}.
Proof. Admitted.

Lemma wp_CallServGet ptr_cli cli (uid : w64) :
  {{{
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli
  }}}
  CallServGet #ptr_cli #uid
  {{{
    (err is_reg : bool) ptr_dig dig sl_hist hist_ref hist ptr_memb memb ptr_nonmemb nonmemb,
    RET (#ptr_dig, slice_val sl_hist, #is_reg, #ptr_memb, #ptr_nonmemb, #err);
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli ∗
    "Herr" ∷ (if err then True else
      "#Hown_dig" ∷ SigDig.own ptr_dig dig ∗
      "Hsl_hist" ∷ own_slice_small sl_hist ptrT (DfracOwn 1) hist_ref ∗
      "Hown_hist" ∷ ([∗ list] l;v ∈ hist_ref;hist, MembHide.own l v) ∗
      "Hown_memb" ∷ Memb.own ptr_memb memb ∗
      "%Hpk_dfrac" ∷ ⌜ memb.(Memb.PkOpen).(CommitOpen.d) = DfracOwn 1 ⌝ ∗
      "Hown_nonmemb" ∷ NonMemb.own ptr_nonmemb nonmemb)
  }}}.
Proof. Admitted.

Lemma wp_CallServSelfMon ptr_cli cli (uid : w64) :
  {{{
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli
  }}}
  CallServSelfMon #ptr_cli #uid
  {{{
    (err : bool) ptr_dig dig ptr_nonmemb nonmemb, RET (#ptr_dig, #ptr_nonmemb, #err);
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli ∗
    "Herr" ∷ (if err then True else
      "#Hown_dig" ∷ SigDig.own ptr_dig dig ∗
      "Hown_nonmemb" ∷ NonMemb.own ptr_nonmemb nonmemb)
  }}}.
Proof. Admitted.

Lemma wp_CallServAudit ptr_cli cli (ep : w64) :
  {{{
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli
  }}}
  CallServAudit #ptr_cli #ep
  {{{
    (err : bool) ptr_upd upd, RET (#ptr_upd, #err);
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli ∗
    if negb err then
      "Hown_upd" ∷ UpdateProof.own ptr_upd upd
    else True
  }}}.
Proof. Admitted.

Lemma wp_CallAdtrUpdate ptr_cli cli ptr_upd upd :
  {{{
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli ∗
    "Hown_upd" ∷ UpdateProof.own ptr_upd upd
  }}}
  CallAdtrUpdate #ptr_cli #ptr_upd
  {{{
    (err : bool), RET #err;
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli ∗
    "Hown_upd" ∷ UpdateProof.own ptr_upd upd
  }}}.
Proof. Admitted.

Lemma wp_CallAdtrGet ptr_cli cli (ep : w64) :
  {{{
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli
  }}}
  CallAdtrGet #ptr_cli #ep
  {{{
    (err : bool) ptr_adtrInfo adtrInfo, RET (#ptr_adtrInfo, #err);
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli ∗
    if negb err then
      "Hown_info" ∷ AdtrEpochInfo.own ptr_adtrInfo adtrInfo
    else True
  }}}.
Proof. Admitted.

End specs.
