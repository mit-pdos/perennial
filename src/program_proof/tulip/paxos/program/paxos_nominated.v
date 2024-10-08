From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section nominated.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__nominated (px : loc) nidme termc nids γ :
    {{{ own_paxos_with_termc px nidme termc nids γ }}}
      Paxos__nominated #px
    {{{ (iscand : bool), RET #iscand; 
        if iscand
        then own_paxos_nominated_with_termc px nidme termc nids γ
        else own_paxos_with_termc px nidme termc nids γ
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) nominated() bool {                                     @*)
    (*@     return px.iscand                                                    @*)
    (*@ }                                                                       @*)
    iNamed "Hpx". iNamed "Hcand".
    wp_loadField.
    iApply "HΦ".
    destruct iscand; iFrame.
  Qed.

End nominated.
