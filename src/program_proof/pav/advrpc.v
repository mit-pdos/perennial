From Perennial.program_proof.pav Require Import prelude.

From Goose.github_com.mit_pdos.pav Require Import advrpc.

Module Server.
Definition t : Type. Admitted.

Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ. Admitted.
End defs.
End Server.

Section specs.
Context `{!heapGS Σ}.

Lemma wp_NewServer (handlers : loc) :
  {{{ True }}}
  NewServer #handlers
  {{{
    ptr_serv serv, RET #ptr_serv;
    "Hown_serv" ∷ Server.own ptr_serv serv
  }}}.
Proof. Admitted.

Lemma wp_Server__Serve ptr_serv serv (addr : w64) :
  {{{
    "Hown_serv" ∷ Server.own ptr_serv serv
  }}}
  Server__Serve #ptr_serv #addr
  {{{ RET #(); True }}}.
Proof. Admitted.

Definition own_Client (ptr : loc) (addr : w64) (is_good : bool) : iProp Σ. Admitted.

Lemma wp_Dial (addr : w64) (is_good : bool) :
  {{{ True }}}
  Dial #addr
  {{{
    ptr_cli, RET #ptr_cli;
    "Hrpc_cli" ∷ own_Client ptr_cli addr is_good
  }}}.
Proof. Admitted.

End specs.
