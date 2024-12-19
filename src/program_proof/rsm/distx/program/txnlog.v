From Perennial.program_proof.rsm.distx Require Import prelude.
From Goose.github_com.mit_pdos.rsm Require Import distx.

Section program.
  Context `{!heapGS Σ, !distx_ghostG Σ}.

  Definition txnlogN := nroot .@ "txnlog".

  Definition command_to_val (pwrsS : Slice.t) (c : command) : val :=
    match c with
    | CmdRead ts key => (#(U64 0), (#(U64 ts), (Slice.nil, (#(LitString key), #()))))
    | CmdPrep ts _ => (#(U64 1), (#(U64 ts), (to_val pwrsS, (zero_val stringT, #()))))
    | CmdCmt ts => (#(U64 2), (#(U64 ts), (Slice.nil, (zero_val stringT, #()))))
    | CmdAbt ts => (#(U64 3), (#(U64 ts), (Slice.nil, (zero_val stringT, #()))))
    end.

  Definition own_dbmap_in_slice s (l : list dbmod) (m : dbmap) : iProp Σ :=
    own_slice s (struct.t WriteEntry) (DfracOwn 1) l ∗ ⌜map_to_list m = l⌝.

  Definition own_pwrs_slice (pwrsS : Slice.t) (c : command) : iProp Σ :=
    match c with
    | CmdPrep _ pwrs => (∃ pwrsL : list dbmod, own_dbmap_in_slice pwrsS pwrsL pwrs)
    | _ => True
    end.
  
  Definition is_txnlog (txnlog : loc) (gid : groupid) (γ : distx_names) : iProp Σ.
  Admitted.

  #[global]
  Instance is_txnlog_persistent txnlog gid γ :
    Persistent (is_txnlog txnlog gid γ).
  Admitted.

  Theorem wp_TxnLog__Lookup (log : loc) (lsn : u64) (gid : groupid) γ :
    is_txnlog log gid γ -∗
    {{{ True }}}
    <<< ∀∀ l, clog_half γ gid l >>>
      TxnLog__Lookup #log #lsn @ ↑txnlogN
    <<< ∃∃ l', clog_half γ gid l' >>>
    {{{ (c : command) (ok : bool) (pwrsS : Slice.t), RET (command_to_val pwrsS c, #ok);
        own_pwrs_slice pwrsS c ∗
        ⌜if ok then l' !! (uint.nat lsn) = Some c else True⌝
    }}}.
  Proof.
    (*@ func (log *TxnLog) Lookup(lsn uint64) (Cmd, bool) {                     @*)
    (*@     return Cmd{}, false                                                 @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_TxnLog__SubmitAbort (log : loc) (ts : u64) (gid : groupid) γ :
    is_txnlog log gid γ -∗
    {{{ True }}}
    <<< ∀∀ vs, cpool_half γ gid vs >>>
      TxnLog__SubmitAbort #log #ts @ ↑txnlogN
    <<< cpool_half γ gid ({[CmdAbt (uint.nat ts)]} ∪ vs) >>>
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term);
        cmd_receipt γ gid (uint.nat lsn) (uint.nat term) (CmdAbt (uint.nat ts))
    }}}.
  Proof.
    (*@ func (log *TxnLog) SubmitAbort(ts uint64) (uint64, uint64) {            @*)
    (*@     // TODO: marshalling a abort command                                @*)
    (*@     // TODO: invoke paxos.Submit()                                      @*)
    (*@     return 0, 0                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_TxnLog__SubmitCommit (log : loc) (ts : u64) (gid : groupid) γ :
    is_txnlog log gid γ -∗
    {{{ True }}}
    <<< ∀∀ vs, cpool_half γ gid vs >>>
      TxnLog__SubmitCommit #log #ts @ ↑txnlogN
    <<< cpool_half γ gid ({[CmdCmt (uint.nat ts)]} ∪ vs) >>>
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term);
        cmd_receipt γ gid (uint.nat lsn) (uint.nat term) (CmdCmt (uint.nat ts))
    }}}.
  Proof.
    (*@ func (log *TxnLog) SubmitCommit(ts uint64) (uint64, uint64) {           @*)
    (*@     // TODO: marshalling a commit command                               @*)
    (*@     // TODO: invoke paxos.Submit()                                      @*)
    (*@     return 0, 0                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_TxnLog__SubmitPrepare
    (log : loc) (ts : u64) (pwrsS : Slice.t)
    (pwrsL : list dbmod) (pwrs : dbmap) (gid : groupid) γ :
    is_txnlog log gid γ -∗
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs }}}
    <<< ∀∀ vs, cpool_half γ gid vs >>>
      TxnLog__SubmitPrepare #log #ts (to_val pwrsS) @ ↑txnlogN
    <<< cpool_half γ gid ({[CmdPrep (uint.nat ts) pwrs]} ∪ vs) >>>
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term);
        cmd_receipt γ gid (uint.nat lsn) (uint.nat term) (CmdPrep (uint.nat ts) pwrs)
    }}}.
  Proof.
    (* some mixcode bug when function takes a slice *)
    (*@     // TODO: marshalling a prepare command                              @*)
    (*@     // TODO: invoke paxos.Submit()                                      @*)
    (*@     return 0, 0                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_TxnLog__SubmitRead
    (log : loc) (ts : u64) (key : byte_string) (gid : groupid) γ :
    is_txnlog log gid γ -∗
    {{{ True }}}
    <<< ∀∀ vs, cpool_half γ gid vs >>>
      TxnLog__SubmitRead #log #ts #(LitString key) @ ↑txnlogN
    <<< cpool_half γ gid ({[CmdRead (uint.nat ts) key]} ∪ vs) >>>
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term);
        cmd_receipt γ gid (uint.nat lsn) (uint.nat term) (CmdRead (uint.nat ts) key)
    }}}.
  Proof.
    (*@ func (log *TxnLog) SubmitRead(ts uint64, key string) (uint64, uint64) { @*)
    (*@     // TODO: marshalling a read command                                 @*)
    (*@     // TODO: invoke paxos.Submit()                                      @*)
    (*@     return 0, 0                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_TxnLog__WaitUntilSafe
    (log : loc) (lsn : u64) (term : u64) (c : command) (gid : groupid) γ :
    is_txnlog log gid γ -∗
    cmd_receipt γ gid (uint.nat lsn) (uint.nat term) c -∗
    {{{ True }}}
      TxnLog__WaitUntilSafe #log #lsn #term
    {{{ (ok : bool), RET #ok;
        if ok
        then ∃ l, clog_lb γ gid l ∧ ⌜l !! (uint.nat lsn) = Some c⌝
        else True
    }}}.
  Proof.
    (*@ func (log *TxnLog) WaitUntilSafe(lsn uint64, term uint64) bool {        @*)
    (*@     // TODO: invoke paxos.WaitUntilSafe(lsn, term)                      @*)
    (*@     // TODO: have some timeout here                                     @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
