From Perennial.program_proof.tulip.paxos Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section resume.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_resume (nidme termc terml lsnc : u64) (log : list string) γ :
    {{{ own_current_term_half γ nidme (uint.nat termc) ∗
        own_ledger_term_half γ nidme (uint.nat terml) ∗
        own_committed_lsn_half γ nidme (uint.nat lsnc) ∗
        own_node_ledger_half γ nidme log
    }}}
      resume #()
    {{{ (logP : Slice.t), RET (#termc, #terml, #lsnc, to_val logP);
        own_current_term_half γ nidme (uint.nat termc) ∗
        own_ledger_term_half γ nidme (uint.nat terml) ∗
        own_committed_lsn_half γ nidme (uint.nat lsnc) ∗
        own_node_ledger_half γ nidme log ∗
        own_slice logP stringT (DfracOwn 1) log
    }}}.
  Proof.
    (*@ func resume() (uint64, uint64, uint64, []string) {                      @*)
    (*@     // TODO: Read the underlying file and perform recovery to re-construct @*)
    (*@     // @termc, @terml, @lsnc, and @log.                                 @*)
    (*@     return 0, 0, 0, make([]string, 0)                                   @*)
    (*@ }                                                                       @*)
  Admitted.

End resume.
