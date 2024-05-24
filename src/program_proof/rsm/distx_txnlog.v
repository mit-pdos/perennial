From Perennial.program_proof.rsm Require Import distx.
From Goose.github_com.mit_pdos.rsm Require Import distx.

Section program.
  Context `{!heapGS Σ, !distx_ghostG Σ}.

  Definition txnlogN := nroot .@ "txnlog".

  Definition command_to_val (c : command) : val.
  Admitted.
  
  Definition own_txnlog (log : loc) (gid : groupid) (γ : distx_names) : iProp Σ.
  Admitted.

  Theorem wp_TxnLog__Lookup (log : loc) (lsn : u64) (gid : groupid) γ :
    ⊢
    {{{ own_txnlog log gid γ }}}
    <<< ∀∀ l, clog_half γ gid l >>>
      TxnLog__Lookup #log #lsn @ ↑txnlogN
    <<< ∃∃ l', clog_half γ gid l' >>>
    {{{ (c : command) (ok : bool), RET (command_to_val c, #ok);
        own_txnlog log gid γ ∗
        ⌜if ok then l' !! (uint.nat lsn) = Some c else True⌝
    }}}.
  Proof.
    (*@ func (log *TxnLog) Lookup(lsn uint64) (Cmd, bool) {                     @*)
    (*@     return Cmd{}, false                                                 @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_TxnLog__SubmitAbort (log : loc) (ts : u64) (gid : groupid) γ :
    ⊢
    {{{ own_txnlog log gid γ }}}
    <<< ∀∀ vs, cpool_half γ gid vs >>>
      TxnLog__SubmitAbort #log #ts @ ↑txnlogN
    <<< cpool_half γ gid ({[CmdAbt (uint.nat ts)]} ∪ vs) >>>
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term); own_txnlog log gid γ }}}.
  Proof.
    (*@ func (log *TxnLog) SubmitAbort(ts uint64) (uint64, uint64) {            @*)
    (*@     // TODO: marshalling a abort command                                @*)
    (*@     // TODO: invoke paxos.Submit()                                      @*)
    (*@     return 0, 0                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_TxnLog__SubmitCommit (log : loc) (ts : u64) (gid : groupid) γ :
    ⊢
    {{{ own_txnlog log gid γ }}}
    <<< ∀∀ vs, cpool_half γ gid vs >>>
      TxnLog__SubmitCommit #log #ts @ ↑txnlogN
    <<< cpool_half γ gid ({[CmdCmt (uint.nat ts)]} ∪ vs) >>>
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term); own_txnlog log gid γ }}}.
  Proof.
    (*@ func (log *TxnLog) SubmitCommit(ts uint64) (uint64, uint64) {           @*)
    (*@     // TODO: marshalling a commit command                               @*)
    (*@     // TODO: invoke paxos.Submit()                                      @*)
    (*@     return 0, 0                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_TxnLog__SubmitPrepare
    (log : loc) (ts : u64) (wrs : Slice.t)
    (wrsM : dbmap) (gid : groupid) γ :
    ⊢
    {{{ own_txnlog log gid γ (* TODO: slice ownership *) }}}
    <<< ∀∀ vs, cpool_half γ gid vs >>>
      TxnLog__SubmitPrepare #log #ts (to_val wrs) @ ↑txnlogN
    <<< cpool_half γ gid ({[CmdPrep (uint.nat ts) wrsM]} ∪ vs) >>>
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term); own_txnlog log gid γ }}}.
  Proof.
    (* some mixcode bug when function takes a slice *)
    (*@     // TODO: marshalling a prepare command                              @*)
    (*@     // TODO: invoke paxos.Submit()                                      @*)
    (*@     return 0, 0                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_TxnLog__SubmitRead
    (log : loc) (ts : u64) (key : string) (gid : groupid) γ :
    ⊢
    {{{ own_txnlog log gid γ }}}
    <<< ∀∀ vs, cpool_half γ gid vs >>>
      TxnLog__SubmitRead #log #ts #(LitString key) @ ↑txnlogN
    <<< cpool_half γ gid ({[CmdRead (uint.nat ts) key]} ∪ vs) >>>
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term); own_txnlog log gid γ }}}.
  Proof.
    (*@ func (log *TxnLog) SubmitRead(ts uint64, key string) (uint64, uint64) { @*)
    (*@     // TODO: marshalling a read command                                 @*)
    (*@     // TODO: invoke paxos.Submit()                                      @*)
    (*@     return 0, 0                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_TxnLog__WaitUntilSafe
    (log : loc) (lsn : u64) (term : u64) (c : command) (gid : groupid) γ :
    cmd_receipt γ gid (uint.nat lsn) (uint.nat term) c -∗
    {{{ own_txnlog log gid γ }}}
      TxnLog__WaitUntilSafe #log #lsn #term
    {{{ (ok : bool), RET #ok;
        own_txnlog log gid γ ∗
        ∃ l, clog_lb γ gid l ∧ ⌜l !! (uint.nat lsn) = Some c⌝
    }}}.
  Proof.
    (*@ func (log *TxnLog) WaitUntilSafe(lsn uint64, term uint64) bool {        @*)
    (*@     // TODO: invoke paxos.WaitUntilSafe(lsn, term)                      @*)
    (*@     // TODO: have some timeout here                                     @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
