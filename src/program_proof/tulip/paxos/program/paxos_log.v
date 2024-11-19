From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section log.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_logAdvance
    (fname : string) (termW : u64) (lsnW : u64) (entsS : Slice.t) (ents : list string) E :
    let lsn := uint.nat lsnW in
    let term := uint.nat termW in
    ⊢
    {{{ own_slice_small entsS stringT (DfracOwn 1) ents }}}
    <<< ∀∀ bs wal, fname f↦ bs ∗ ⌜encode_paxos_cmds wal = bs⌝ >>>
      logAdvance #(LitString fname) #termW #lsnW (to_val entsS) @ E
    <<< ∃∃ bs', fname f↦ bs' ∗ ⌜encode_paxos_cmds (wal ++ [CmdPaxosAdvance term lsn ents]) = bs'⌝ >>>
    {{{ RET #(); own_slice_small entsS stringT (DfracOwn 1) ents }}}.
  Proof.
    (*@ func logAdvance(fname string, term uint64, lsn uint64, ents []string) { @*)
    (*@     var data = make([]byte, 0, 64)                                      @*)
    (*@                                                                         @*)
    (*@     data = marshal.WriteInt(data, CMD_ADVANCE)                          @*)
    (*@     data = marshal.WriteInt(data, term)                                 @*)
    (*@     data = marshal.WriteInt(data, lsn)                                  @*)
    (*@     data = util.EncodeStrings(data, ents)                               @*)
    (*@                                                                         @*)
    (*@     grove_ffi.FileAppend(fname, data)                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_logAccept
    (fname : string) (lsnW : u64) (entsS : Slice.t) (ents : list string) E :
    let lsn := uint.nat lsnW in
    ⊢
    {{{ own_slice_small entsS stringT (DfracOwn 1) ents }}}
    <<< ∀∀ bs wal, fname f↦ bs ∗ ⌜encode_paxos_cmds wal = bs⌝ >>>
      logAccept #(LitString fname) #lsnW (to_val entsS) @ E
    <<< ∃∃ bs', fname f↦ bs' ∗ ⌜encode_paxos_cmds (wal ++ [CmdPaxosAccept lsn ents]) = bs'⌝ >>>
    {{{ RET #(); own_slice_small entsS stringT (DfracOwn 1) ents }}}.
  Proof.
    (*@ func logAccept(fname string, lsn uint64, ents []string) {               @*)
    (*@     var data = make([]byte, 0, 64)                                      @*)
    (*@                                                                         @*)
    (*@     data = marshal.WriteInt(data, CMD_ACCEPT)                           @*)
    (*@     data = marshal.WriteInt(data, lsn)                                  @*)
    (*@     data = util.EncodeStrings(data, ents)                               @*)
    (*@                                                                         @*)
    (*@     grove_ffi.FileAppend(fname, data)                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_logPrepare (fname : string) (termW : u64) E :
    let term := uint.nat termW in
    ⊢
    {{{ True }}}
    <<< ∀∀ bs wal, fname f↦ bs ∗ ⌜encode_paxos_cmds wal = bs⌝ >>>
      logPrepare #(LitString fname) #termW @ E
    <<< ∃∃ bs', fname f↦ bs' ∗ ⌜encode_paxos_cmds (wal ++ [CmdPaxosPrepare term]) = bs'⌝ >>>
    {{{ RET #(); True }}}.
  Proof.
    (*@ func logPrepare(fname string, term uint64) {                            @*)
    (*@     var data = make([]byte, 0, 16)                                      @*)
    (*@                                                                         @*)
    (*@     data = marshal.WriteInt(data, CMD_PREPARE)                          @*)
    (*@     data = marshal.WriteInt(data, term)                                 @*)
    (*@                                                                         @*)
    (*@     grove_ffi.FileAppend(fname, data)                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_logAppend (fname : string) (ent : string) E :
    ⊢
    {{{ True }}}
    <<< ∀∀ bs wal, fname f↦ bs ∗ ⌜encode_paxos_cmds wal = bs⌝ >>>
      logAppend #(LitString fname) #(LitString ent) @ E
    <<< ∃∃ bs', fname f↦ bs' ∗ ⌜encode_paxos_cmds (wal ++ [CmdPaxosExtend [ent]]) = bs'⌝ >>>
    {{{ RET #(); True }}}.
  Proof.
    (*@ func logAppend(fname string, ent string) {                              @*)
    (*@     var data = make([]byte, 0, 32)                                      @*)
    (*@                                                                         @*)
    (*@     data = marshal.WriteInt(data, CMD_APPEND)                           @*)
    (*@     data = util.EncodeString(data, ent)                                 @*)
    (*@                                                                         @*)
    (*@     grove_ffi.FileAppend(fname, data)                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_logExtend (fname : string) (entsS : Slice.t) (ents : list string) E :
    ⊢
    {{{ own_slice_small entsS stringT (DfracOwn 1) ents }}}
    <<< ∀∀ bs wal, fname f↦ bs ∗ ⌜encode_paxos_cmds wal = bs⌝ >>>
      logExtend #(LitString fname) (to_val entsS) @ E
    <<< ∃∃ bs', fname f↦ bs' ∗ ⌜encode_paxos_cmds (wal ++ [CmdPaxosExtend ents]) = bs'⌝ >>>
    {{{ RET #(); own_slice_small entsS stringT (DfracOwn 1) ents }}}.
  Proof.
    (*@ func logExtend(fname string, ents []string) {                           @*)
    (*@     // Currently not used. For batch optimization.                      @*)
    (*@     var data = make([]byte, 0, 64)                                      @*)
    (*@                                                                         @*)
    (*@     data = marshal.WriteInt(data, CMD_EXTEND)                           @*)
    (*@     data = util.EncodeStrings(data, ents)                               @*)
    (*@                                                                         @*)
    (*@     grove_ffi.FileAppend(fname, data)                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_logExpand (fname : string) (lsnW : u64) E :
    let lsn := uint.nat lsnW in
    ⊢
    {{{ True }}}
    <<< ∀∀ bs wal, fname f↦ bs ∗ ⌜encode_paxos_cmds wal = bs⌝ >>>
      logExpand #(LitString fname) #lsnW @ E
    <<< ∃∃ bs', fname f↦ bs' ∗ ⌜encode_paxos_cmds (wal ++ [CmdPaxosExpand lsn]) = bs'⌝ >>>
    {{{ RET #(); True }}}.
  Proof.
    (*@ func logExpand(fname string, lsn uint64) {                              @*)
    (*@     var data = make([]byte, 0, 16)                                      @*)
    (*@                                                                         @*)
    (*@     data = marshal.WriteInt(data, CMD_EXPAND)                           @*)
    (*@     data = marshal.WriteInt(data, lsn)                                  @*)
    (*@                                                                         @*)
    (*@     grove_ffi.FileAppend(fname, data)                                   @*)
    (*@ }                                                                       @*)
  Admitted.

End log.
