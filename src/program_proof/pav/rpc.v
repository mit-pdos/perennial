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

Lemma wp_CallServAudit ptr_cli cli (ep : w64) :
  {{{
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli
  }}}
  CallServAudit #ptr_cli #ep
  {{{
    ptr_upd upd (err : bool), RET (#ptr_upd, #err);
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
    ptr_adtrInfo adtrInfo (err : bool), RET (#ptr_adtrInfo, #err);
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli ∗
    if negb err then
      "Hown_info" ∷ AdtrEpochInfo.own ptr_adtrInfo adtrInfo
    else True
  }}}.
Proof. Admitted.

End specs.
