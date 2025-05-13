From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import
  repr paxos_request_session.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section serve.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__Serve (px : loc) nidme γ :
    is_paxos px nidme γ -∗
    {{{ True }}}
      Paxos__Serve #px
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hinv" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) Serve() {                                              @*)
    (*@     addrme := px.addrm[px.nidme]                                        @*)
    (*@     ls := grove_ffi.Listen(addrme)                                      @*)
    (*@     for {                                                               @*)
    (*@         conn := grove_ffi.Accept(ls)                                    @*)
    (*@         go func() {                                                     @*)
    (*@             px.RequestSession(conn)                                     @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iNamed "Hinv". iNamed "Haddrm". iNamed "Hnids".
    do 2 wp_loadField.
    wp_apply (wp_MapGet with "Haddrm").
    iIntros (addrme ok) "[%Hok _]".
    destruct ok; last first.
    { apply map_get_false in Hok as [Hok _].
      rewrite -not_elem_of_dom in Hok.
      set_solver.
    }
    apply map_get_true in Hok.
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
      wp_apply wp_Paxos__RequestSession.
      { apply Hok. }
      { iFrame "# %". }
      done.
    }
    wp_pures.
    by iApply "HΦ".
  Qed.

End serve.
