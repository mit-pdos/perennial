From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import
  auditor advrpc core cryptoffi serde server.

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

(* TODO: this is mostly a copy of the Server__Put spec.
later, need to properly bind these two. *)
Lemma wp_CallServPut ptr_cli addr is_good serv uid nVers sl_pk d0 (pk : list w8) cli_next_ep :
  {{{
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr is_good ∗
    "Hvers" ∷ (if negb is_good then True else uid ↪[serv.(Server.γvers)] nVers) ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "#Hlb_ep" ∷ (if negb is_good then True else mono_nat_lb_own serv.(Server.γepoch) cli_next_ep)
  }}}
  CallServPut #ptr_cli #uid (slice_val sl_pk)
  {{{
    ptr_sigdig sigdig ptr_lat lat ptr_bound bound err label commit,
    RET (#ptr_sigdig, #ptr_lat, #ptr_bound, #err);
    let new_next_ep := word.add sigdig.(SigDig.Epoch) (W64 1) in
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr is_good ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "%Hgenie" ∷ ⌜ is_good = true → err = false ⌝ ∗

    "Herr" ∷ (if err then True else
      "#Hsigdig" ∷ SigDig.own ptr_sigdig sigdig DfracDiscarded ∗
      "Hlat" ∷ Memb.own ptr_lat lat (DfracOwn 1) ∗
      "Hbound" ∷ NonMemb.own ptr_bound bound (DfracOwn 1)) ∗

    "Hgood" ∷ (if negb is_good then True else
      "Hvers" ∷ uid ↪[serv.(Server.γvers)] (word.add nVers (W64 1)) ∗

      "%Heq_ep" ∷ ⌜ sigdig.(SigDig.Epoch) = lat.(Memb.EpochAdded) ⌝ ∗
      "%Heq_pk" ∷ ⌜ pk = lat.(Memb.PkOpen).(CommitOpen.Val) ⌝ ∗
      "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) (uint.nat new_next_ep) ∗
      "%Hlt_ep" ∷ ⌜ Z.of_nat cli_next_ep < uint.Z new_next_ep ⌝ ∗
      (* provable from new_next_ep = the w64 size of epochHist slice. *)
      "%Hnoof_ep" ∷ ⌜ uint.Z new_next_ep = (uint.Z sigdig.(SigDig.Epoch) + 1)%Z ⌝ ∗

      "#Hsig" ∷ is_sig serv.(Server.sig_pk)
        (PreSigDig.encodesF $ PreSigDig.mk sigdig.(SigDig.Epoch) sigdig.(SigDig.Dig))
        sigdig.(SigDig.Sig) ∗

      "#Hwish_lat" ∷ wish_checkMemb serv.(Server.vrf_pk) uid nVers
        sigdig.(SigDig.Dig) lat label commit ∗

      "#Hwish_bound" ∷ wish_checkNonMemb serv.(Server.vrf_pk)
        uid (word.add nVers (W64 1)) sigdig.(SigDig.Dig) bound)
  }}}.
Proof. Admitted.

Lemma wp_CallServSelfMon ptr_cli addr is_good (uid : w64) serv nVers cli_next_ep :
  {{{
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr is_good ∗
    "Hvers" ∷ (if negb is_good then True else uid ↪[serv.(Server.γvers)] nVers) ∗
    "#Hlb_ep" ∷ (if negb is_good then True else mono_nat_lb_own serv.(Server.γepoch) cli_next_ep)
  }}}
  CallServSelfMon #ptr_cli #uid
  {{{
    (err : bool) ptr_sigdig sigdig ptr_bound bound,
    RET (#ptr_sigdig, #ptr_bound, #err);
    let new_next_ep := word.add sigdig.(SigDig.Epoch) (W64 1) in
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr is_good ∗
    "%Hgenie" ∷ ⌜ is_good = true → err = false ⌝ ∗

    "Herr" ∷ (if err then True else
      "#Hsigdig" ∷ SigDig.own ptr_sigdig sigdig DfracDiscarded ∗
      "Hbound" ∷ NonMemb.own ptr_bound bound (DfracOwn 1)) ∗

    "Hgood" ∷ (if negb is_good then True else
      "Hvers" ∷ uid ↪[serv.(Server.γvers)] nVers ∗

      "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) (uint.nat new_next_ep) ∗
      "%Hlt_ep" ∷ ⌜ Z.of_nat cli_next_ep ≤ uint.Z new_next_ep ⌝ ∗
      "%Hnoof_ep" ∷ ⌜ uint.Z new_next_ep = (uint.Z sigdig.(SigDig.Epoch) + 1)%Z ⌝ ∗

      "#Hsig" ∷ is_sig serv.(Server.sig_pk)
        (PreSigDig.encodesF $ PreSigDig.mk sigdig.(SigDig.Epoch) sigdig.(SigDig.Dig))
        sigdig.(SigDig.Sig) ∗
      "#Hwish_bound" ∷ wish_checkNonMemb serv.(Server.vrf_pk) uid nVers
        sigdig.(SigDig.Dig) bound)
  }}}.
Proof. Admitted.

Lemma wp_CallServGet ptr_cli addr is_good (uid : w64) serv cli_next_ep :
  {{{
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr is_good ∗
    "#Hlb_ep" ∷ (if negb is_good then True else mono_nat_lb_own serv.(Server.γepoch) cli_next_ep)
  }}}
  CallServGet #ptr_cli #uid
  {{{
    (err : bool) ptr_sigdig sigdig sl_hist ptr2_hist hist
    (is_reg : bool) ptr_lat lat ptr_bound bound (nVers : w64),
    RET (#ptr_sigdig, slice_val sl_hist, #is_reg, #ptr_lat, #ptr_bound, #err);
    let new_next_ep := word.add sigdig.(SigDig.Epoch) (W64 1) in
    "Hown_cli" ∷ advrpc.own_Client ptr_cli addr is_good ∗
    "%Hgenie" ∷ ⌜ is_good = true → err = false ⌝ ∗

    "Herr" ∷ (if err then True else
      "#Hsigdig" ∷ SigDig.own ptr_sigdig sigdig DfracDiscarded ∗
      "Hhist" ∷ ([∗ list] l;x ∈ ptr2_hist;hist,
        MembHide.own l x (DfracOwn 1)) ∗
      "Hsl_hist" ∷ own_slice_small sl_hist ptrT (DfracOwn 1) ptr2_hist ∗
      "Hlat" ∷ Memb.own ptr_lat lat (DfracOwn 1) ∗
      "Hbound" ∷ NonMemb.own ptr_bound bound (DfracOwn 1)) ∗

    "Hgood" ∷ (if negb is_good then True else
      "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) (uint.nat new_next_ep) ∗
      "%Hlt_ep" ∷ ⌜ Z.of_nat cli_next_ep ≤ uint.Z new_next_ep ⌝ ∗
      "%Hnoof_ep" ∷ ⌜ uint.Z new_next_ep = (uint.Z sigdig.(SigDig.Epoch) + 1)%Z ⌝ ∗

      "#Hsig" ∷ is_sig serv.(Server.sig_pk)
        (PreSigDig.encodesF $ PreSigDig.mk sigdig.(SigDig.Epoch) sigdig.(SigDig.Dig))
        sigdig.(SigDig.Sig) ∗
      "%Hlen_hist" ∷ ⌜ length hist = pred (uint.nat nVers) ⌝ ∗
      "#Hwish_hist" ∷ ([∗ list] ver ↦ x ∈ hist,
        ∃ label,
        wish_checkMembHide serv.(Server.vrf_pk) uid (W64 ver)
          sigdig.(SigDig.Dig) x label) ∗
      "%Heq_is_reg" ∷ ⌜ is_reg = negb $ bool_decide (nVers = (W64 0)) ⌝ ∗
      "#Hwish_lat" ∷ (if negb is_reg then True else
        ∃ label commit,
        wish_checkMemb serv.(Server.vrf_pk) uid (word.sub nVers (W64 1))
          sigdig.(SigDig.Dig) lat label commit) ∗
      "#Hwish_bound" ∷ wish_checkNonMemb serv.(Server.vrf_pk) uid nVers
        sigdig.(SigDig.Dig) bound)
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
