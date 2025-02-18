From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section getlsnc.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__getlsnc (px : loc) (nidme termc : u64) nids γ :
    {{{ own_paxos_leading_with_termc px nidme termc nids γ }}}
      Paxos__getlsnc #px
    {{{ (lsnc : u64) (logc : list byte_string), RET #lsnc;
        own_paxos_leading_with_termc px nidme termc nids γ ∗
        safe_ledger_above γ nids (uint.nat termc) logc ∗
        ⌜length logc = uint.nat lsnc⌝
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) getlsnc() uint64 {                                     @*)
    (*@     return px.lsnc                                                      @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx". iNamed "Hleader". iNamed "Honlyl". subst terml.
    wp_loadField.
    set logc := take _ log.
    iApply ("HΦ" $! _ logc).
    iFrame "Hcand HisleaderP".
    iFrame "∗ # %".
    iPureIntro.
    split; first done.
    rewrite length_take.
    clear -Hlsncub. lia.
  Qed.

  Theorem wp_Paxos__getlsnc__nominated (px : loc) (nidme termc : u64) nids γ :
    {{{ own_paxos_nominated_with_termc px nidme termc nids γ }}}
      Paxos__getlsnc #px
    {{{ (lsnc : u64), RET #lsnc;
        own_paxos_nominated_with_termc px nidme termc nids γ ∗
        is_prepare_lsn γ (uint.nat termc) (uint.nat lsnc)
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) getlsnc() uint64 {                                     @*)
    (*@     return px.lsnc                                                      @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx". iNamed "Hcand". iNamed "Honlyc".
    wp_loadField.
    iApply "HΦ".
    iAssert (is_prepare_lsn γ (uint.nat termc) (uint.nat lsnc))%I as "#Hlsnprc'".
    { rewrite length_take_le; [done | word]. }
    iFrame "Hleader HiscandP".
    iFrame "∗ # %".
  Qed.

  Theorem wp_Paxos__getlsnc__weak (px : loc) (nidme : u64) nids γ :
    {{{ own_paxos px nidme nids γ }}}
      Paxos__getlsnc #px
    {{{ (lsnc : u64), RET #lsnc; own_paxos px nidme nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) getlsnc() uint64 {                                     @*)
    (*@     return px.lsnc                                                      @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx". iNamed "Hcand". iNamed "Honlyc".
    wp_loadField.
    iApply "HΦ".
    iFrame "Hleader HiscandP".
    iFrame "∗ # %".
  Qed.

End getlsnc.
