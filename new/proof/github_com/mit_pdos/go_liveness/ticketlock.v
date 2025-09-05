Require Import New.generatedproof.github_com.mit_pdos.go_liveness.ticketlock.
Require Import New.proof.sync.atomic.
Require Import New.proof.runtime.
Require Import New.proof.proof_prelude.
From New.proof Require Import grove_prelude.

Set Implicit Arguments.

Section proof.

Context `{!heapGS Σ}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit ticketlock := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf ticketlock := build_get_is_pkg_init_wf.

Lemma wp_TicketLock_New :
  {{{
        is_pkg_init ticketlock ∗
        True
  }}}
    @! ticketlock.New #()
  {{{
        RET #(); True
  }}}.
Proof.
  wp_start.
Admitted.

Lemma wp_TicketLock_Acquire (ptr : loc) :
  {{{
        is_pkg_init ticketlock ∗
        True
  }}}
    ptr @ (ptrT.id ticketlock.TicketLock.id) @ "Acquire" #()
  {{{
        RET #(); True
  }}}.
Proof.
Admitted.

Lemma wp_TicketLock_Release (ptr : loc) :
  {{{
        is_pkg_init ticketlock ∗
        True
  }}}
    ptr @ (ptrT.id ticketlock.TicketLock.id) @ "Release" #()
  {{{
        RET #(); True
  }}}.
Proof.
Admitted.

End proof.
