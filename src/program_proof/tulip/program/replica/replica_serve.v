From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_request_session.
From Perennial.program_proof.tulip.paxos Require Import base.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ, !paxos_ghostG Σ}.

  Theorem wp_Replica__Serve (rp : loc) addr gid rid γ :
    is_replica_plus_network rp addr gid rid γ -∗
    {{{ True }}}
      Replica__Serve #rp
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hrp" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Serve() {                                            @*)
    (*@     ls := grove_ffi.Listen(rp.addr)                                     @*)
    (*@     for {                                                               @*)
    (*@         conn := grove_ffi.Accept(ls)                                    @*)
    (*@         go func() {                                                     @*)
    (*@             rp.RequestSession(conn)                                     @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply wp_Listen.
    wp_pures.
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.
    wp_apply wp_Accept.
    iIntros (chanpeer) "_".
    wp_pures.
    wp_apply (wp_fork).
    { (* Fork. *)
      wp_apply wp_Replica__RequestSession.
      { iFrame "# %". }
      done.
    }
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
