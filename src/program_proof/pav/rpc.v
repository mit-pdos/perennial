From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import auditor advrpc core cryptoffi serde server.

Section specs.
Context `{!heapGS Σ, !pavG Σ}.
Lemma wp_NewRpcServer ptr_serv serv :
  {{{
    "Hserv" ∷ is_Server ptr_serv serv
  }}}
  NewRpcServer #ptr_serv
  {{{
    ptr_rpcserv rpcserv, RET #ptr_rpcserv;
    "Hown_rpcserv" ∷ advrpc.Server.own ptr_rpcserv rpcserv
  }}}.
Proof. Admitted.

Lemma wp_NewRpcAuditor ptr_adtr :
  {{{
    "Hadtr" ∷ Auditor.valid ptr_adtr
  }}}
  NewRpcAuditor #ptr_adtr
  {{{
    ptr_rpcserv rpcserv, RET #ptr_rpcserv;
    "Hown_rpcserv" ∷ advrpc.Server.own ptr_rpcserv rpcserv
  }}}.
Proof. Admitted.

Lemma wp_CallServPut ptr_cli addr (uid : w64) sl_pk d0 (pk : list w8) :
  {{{
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr false ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk
  }}}
  CallServPut #ptr_cli #uid (slice_val sl_pk)
  {{{
    (err : bool) ptr_dig dig ptr_memb memb ptr_nonmemb nonmemb,
    RET (#ptr_dig, #ptr_memb, #ptr_nonmemb, #err);
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr false ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Herr" ∷ (if err then True else
      "Hown_dig" ∷ SigDig.own ptr_dig dig (DfracOwn 1) ∗
      "Hown_memb" ∷ Memb.own ptr_memb memb (DfracOwn 1) ∗
      "Hown_nonmemb" ∷ NonMemb.own ptr_nonmemb nonmemb (DfracOwn 1))
  }}}.
Proof. Admitted.

(* TODO: this is a direct copy of the Server__Put spec.
later, need to properly bind these two. *)
Lemma wp_CallServPut_good ptr_cli addr serv uid nVers sl_pk d0 (pk : list w8) cli_ep :
  {{{
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr true ∗
    "Hvers" ∷ uid ↪[serv.(Server.γvers)] nVers ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) cli_ep
  }}}
  CallServPut #ptr_cli #uid (slice_val sl_pk)
  {{{
    ptr_sigdig sigdig ptr_lat lat ptr_bound bound err label commit,
    RET (#ptr_sigdig, #ptr_lat, #ptr_bound, #err);
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr true ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗

    "Hvers" ∷ uid ↪[serv.(Server.γvers)] (word.add nVers (W64 1)) ∗
    "%Heq_ep" ∷ ⌜ sigdig.(SigDig.Epoch) = lat.(Memb.EpochAdded) ⌝ ∗
    "%Heq_pk" ∷ ⌜ pk = lat.(Memb.PkOpen).(CommitOpen.Val) ⌝ ∗
    "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) (uint.nat sigdig.(SigDig.Epoch)) ∗
    "%Hlt_ep" ∷ ⌜ Z.of_nat cli_ep < uint.Z sigdig.(SigDig.Epoch) ⌝ ∗
    "#Hsigdig" ∷ SigDig.own ptr_sigdig sigdig DfracDiscarded ∗
    "#Hsig" ∷ is_sig serv.(Server.sig_pk)
      (PreSigDig.encodesF $ PreSigDig.mk sigdig.(SigDig.Epoch) sigdig.(SigDig.Dig))
      sigdig.(SigDig.Sig) ∗
    "Hlat" ∷ Memb.own ptr_lat lat (DfracOwn 1) ∗
    "#Hwish_lat" ∷ wish_checkMemb serv.(Server.vrf_pk) uid nVers
      sigdig.(SigDig.Dig) lat label commit ∗
    "Hbound" ∷ NonMemb.own ptr_bound bound (DfracOwn 1) ∗
    "#Hwish_bound" ∷ wish_checkNonMemb serv.(Server.vrf_pk)
      uid (word.add nVers (W64 1)) sigdig.(SigDig.Dig) bound ∗
    "->" ∷ ⌜ err = false ⌝
  }}}.
Proof. Admitted.

Lemma wp_CallServGet ptr_cli addr (uid : w64) :
  {{{
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr false
  }}}
  CallServGet #ptr_cli #uid
  {{{
    (err is_reg : bool) ptr_dig dig sl_hist hist_ref hist ptr_memb memb ptr_nonmemb nonmemb,
    RET (#ptr_dig, slice_val sl_hist, #is_reg, #ptr_memb, #ptr_nonmemb, #err);
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr false ∗
    "Herr" ∷ (if err then True else
      "#Hown_dig" ∷ SigDig.own ptr_dig dig (DfracOwn 1) ∗
      "Hsl_hist" ∷ own_slice_small sl_hist ptrT (DfracOwn 1) hist_ref ∗
      "Hown_hist" ∷ ([∗ list] l;v ∈ hist_ref;hist, MembHide.own l v (DfracOwn 1)) ∗
      "Hown_memb" ∷ Memb.own ptr_memb memb (DfracOwn 1) ∗
      "Hown_nonmemb" ∷ NonMemb.own ptr_nonmemb nonmemb (DfracOwn 1))
  }}}.
Proof. Admitted.

Lemma wp_CallServSelfMon ptr_cli addr (uid : w64) :
  {{{
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr false
  }}}
  CallServSelfMon #ptr_cli #uid
  {{{
    (err : bool) ptr_dig dig ptr_nonmemb nonmemb, RET (#ptr_dig, #ptr_nonmemb, #err);
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr false ∗
    "Herr" ∷ (if err then True else
      "#Hown_dig" ∷ SigDig.own ptr_dig dig (DfracOwn 1) ∗
      "Hown_nonmemb" ∷ NonMemb.own ptr_nonmemb nonmemb (DfracOwn 1))
  }}}.
Proof. Admitted.

Lemma wp_CallServAudit ptr_cli addr (ep : w64) :
  {{{
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr false
  }}}
  CallServAudit #ptr_cli #ep
  {{{
    (err : bool) ptr_upd upd, RET (#ptr_upd, #err);
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr false ∗
    if negb err then
      "Hown_upd" ∷ UpdateProof.own ptr_upd upd (DfracOwn 1)
    else True
  }}}.
Proof. Admitted.

Lemma wp_CallAdtrUpdate ptr_cli addr ptr_upd upd d0 :
  {{{
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr false ∗
    "Hown_upd" ∷ UpdateProof.own ptr_upd upd d0
  }}}
  CallAdtrUpdate #ptr_cli #ptr_upd
  {{{
    (err : bool), RET #err;
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr false ∗
    "Hown_upd" ∷ UpdateProof.own ptr_upd upd d0
  }}}.
Proof. Admitted.

Lemma wp_CallAdtrGet ptr_cli addr (ep : w64) :
  {{{
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr false
  }}}
  CallAdtrGet #ptr_cli #ep
  {{{
    (err : bool) ptr_adtrInfo adtrInfo, RET (#ptr_adtrInfo, #err);
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr false ∗
    if negb err then
      "Hown_info" ∷ AdtrEpochInfo.own ptr_adtrInfo adtrInfo (DfracOwn 1)
    else True
  }}}.
Proof. Admitted.

End specs.
