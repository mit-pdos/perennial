From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import cryptoffi.

Section inv.
Context `{!heapGS Σ}.
Definition serv_sigpred (γ : gname) : (list w8 → iProp Σ) :=
  (* TODO: fill in. *)
  λ data, True%I.
End inv.

Module Server.
Definition t : Type. Admitted.

Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ. Admitted.
End defs.
End Server.

Section specs.
Context `{!heapGS Σ}.
Lemma wp_newServer :
  {{{ True }}}
  newServer #()
  {{{
    ptr_serv (serv : Server.t) sl_sigPk sigPk γ (vrfPk : loc), RET (#ptr_serv, slice_val sl_sigPk, #vrfPk);
    "Hown_serv" ∷ Server.own ptr_serv serv ∗
    "#Hsl_sigPk" ∷ own_slice_small sl_sigPk byteT DfracDiscarded sigPk ∗
    "#His_sigPk" ∷ is_pk sigPk (serv_sigpred γ)
  }}}.
Proof. Admitted.
End specs.
