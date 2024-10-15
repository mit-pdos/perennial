From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import advrpc.

Module Server.
Definition t : Type. Admitted.

Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ. Admitted.
End defs.
End Server.

Module Client.
Definition t : Type. Admitted.

Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ. Admitted.
End defs.
End Client.

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

Lemma wp_Dial (addr : w64) :
  {{{ True }}}
  Dial #addr
  {{{
    ptr_cli cli, RET #ptr_cli;
    "Hown_cli" ∷ Client.own ptr_cli cli
  }}}.
Proof. Admitted.

End specs.