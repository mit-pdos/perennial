From Perennial.program_proof.tulip.paxos Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section resume.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_resume (fname : byte_string) (nidme termc terml lsnc : u64) (log : list byte_string) γ :
    {{{ own_current_term_half γ nidme (uint.nat termc) ∗
        own_ledger_term_half γ nidme (uint.nat terml) ∗
        own_committed_lsn_half γ nidme (uint.nat lsnc) ∗
        own_node_ledger_half γ nidme log
    }}}
      resume #(LitString fname)
    {{{ (logP : Slice.t), RET (#termc, #terml, #lsnc, to_val logP);
        own_current_term_half γ nidme (uint.nat termc) ∗
        own_ledger_term_half γ nidme (uint.nat terml) ∗
        own_committed_lsn_half γ nidme (uint.nat lsnc) ∗
        own_node_ledger_half γ nidme log ∗
        own_slice logP stringT (DfracOwn 1) log
    }}}.
  Proof.
    (*@ func resume(fname string) (uint64, uint64, uint64, []string) {          @*)
    (*@     var termc uint64                                                    @*)
    (*@     var terml uint64                                                    @*)
    (*@     var lsnc  uint64                                                    @*)
    (*@     var log = make([]string, 0)                                         @*)
    (*@                                                                         @*)
    (*@     var kind uint64                                                     @*)
    (*@     var term uint64                                                     @*)
    (*@     var lsn  uint64                                                     @*)
    (*@     var ents []string                                                   @*)
    (*@                                                                         @*)
    (*@     var data = grove_ffi.FileRead(fname)                                @*)
    (*@                                                                         @*)
    (*@     for 0 < uint64(len(data)) {                                         @*)
    (*@         kind, data = marshal.ReadInt(data)                              @*)
    (*@                                                                         @*)
    (*@         if kind == CMD_EXTEND {                                         @*)
    (*@             ents, data = util.DecodeStrings(data)                       @*)
    (*@                                                                         @*)
    (*@             log = append(log, ents...)                                  @*)
    (*@         } else if kind == CMD_APPEND {                                  @*)
    (*@             ents = make([]string, 1)                                    @*)
    (*@             var ent string                                              @*)
    (*@             ent, data = util.DecodeString(data)                         @*)
    (*@                                                                         @*)
    (*@             log = append(log, ent)                                      @*)
    (*@         } else if kind == CMD_PREPARE {                                 @*)
    (*@             term, data = marshal.ReadInt(data)                          @*)
    (*@                                                                         @*)
    (*@             termc = term                                                @*)
    (*@         } else if kind == CMD_ADVANCE {                                 @*)
    (*@             term, data = marshal.ReadInt(data)                          @*)
    (*@             lsn, data = marshal.ReadInt(data)                           @*)
    (*@             ents, data = util.DecodeStrings(data)                       @*)
    (*@                                                                         @*)
    (*@             terml = term                                                @*)
    (*@             // Prove safety of this triming operation using well-formedness of @*)
    (*@             // the write-ahead log. See [execute_paxos_advance] in recovery.v. @*)
    (*@             log = log[: lsn]                                            @*)
    (*@             log = append(log, ents...)                                  @*)
    (*@         } else if kind == CMD_ACCEPT {                                  @*)
    (*@             lsn, data = marshal.ReadInt(data)                           @*)
    (*@             ents, data = util.DecodeStrings(data)                       @*)
    (*@                                                                         @*)
    (*@             // Prove safety of this triming operation using well-formedness of @*)
    (*@             // the write-ahead log. See [execute_paxos_accept] in recovery.v. @*)
    (*@             log = log[: lsn]                                            @*)
    (*@             log = append(log, ents...)                                  @*)
    (*@         } else if kind == CMD_EXPAND {                                  @*)
    (*@             lsn, data = marshal.ReadInt(data)                           @*)
    (*@                                                                         @*)
    (*@             lsnc = lsn                                                  @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return termc, terml, lsnc, log                                      @*)
    (*@ }                                                                       @*)
  Admitted.

End resume.
