From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import auditor advrpc client core serde server.

Section specs.
Context `{!heapGS Σ, !pavG Σ}.
Lemma wp_newRpcServer ptr_serv serv :
  {{{
    "Hown_serv" ∷ server.Server.own ptr_serv serv
  }}}
  newRpcServer #ptr_serv
  {{{
    ptr_rpcserv rpcserv, RET #ptr_rpcserv;
    "Hown_rpcserv" ∷ advrpc.Server.own ptr_rpcserv rpcserv
  }}}.
Proof. Admitted.

Lemma wp_newRpcAuditor ptr_adtr :
  {{{
    "Hown_adtr" ∷ Auditor.valid ptr_adtr
  }}}
  newRpcAuditor #ptr_adtr
  {{{
    ptr_rpcserv rpcserv, RET #ptr_rpcserv;
    "Hown_rpcserv" ∷ advrpc.Server.own ptr_rpcserv rpcserv
  }}}.
Proof. Admitted.

Lemma wp_callServAudit ptr_cli cli (ep : w64) :
  {{{
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli
  }}}
  callServAudit #ptr_cli #ep
  {{{
    ptr_upd upd (err : bool), RET (#ptr_upd, #err);
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli ∗
    if negb err then
      "Hown_upd" ∷ UpdateProof.own ptr_upd upd
    else True
  }}}.
Proof. Admitted.

Lemma wp_callAdtrUpdate ptr_cli cli ptr_upd upd :
  {{{
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli ∗
    "Hown_upd" ∷ UpdateProof.own ptr_upd upd
  }}}
  callAdtrUpdate #ptr_cli #ptr_upd
  {{{
    (err : bool), RET #err;
    "Hown_cli" ∷ advrpc.Client.own ptr_cli cli ∗
    "Hown_upd" ∷ UpdateProof.own ptr_upd upd
  }}}.
Proof. Admitted.

End specs.
