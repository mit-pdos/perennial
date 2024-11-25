From Perennial.program_proof.tulip.program Require Import prelude.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__logRead (rp : loc) (ts : u64) (key : string) :
    {{{ True }}}
      Replica__logRead #rp #ts #(LitString key)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (rp *Replica) logRead(ts uint64, key string) {                     @*)
    (*@     // TODO: Create an inconsistent log entry for reading @key at @ts.  @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__logValidate rp (ts : u64) (pwrsS : Slice.t) :
    {{{ True }}}
      Replica__logValidate #rp #ts (to_val pwrsS) slice.nil
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (rp *Replica) logValidate(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) { @*)
    (*@     // TODO: Create an inconsistent log entry for validating @ts with @pwrs and @ptgs. @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__logFastPrepare (rp : loc) (ts : u64) (pwrs : Slice.t) :
    {{{ True }}}
      Replica__logFastPrepare #rp #ts (to_val pwrs) slice.nil
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (rp *Replica) logFastPrepare(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) { @*)
    (*@     // TODO: Create an inconsistent log entry for fast preparing @ts.   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__logAccept (rp : loc) (ts : u64) (rank : u64) (dec : bool) :
    {{{ True }}}
      Replica__logAccept #rp #ts #rank #dec
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (rp *Replica) logAccept(ts uint64, rank uint64, dec bool) {        @*)
    (*@     // TODO: Create an inconsistent log entry for accepting prepare decision @*)
    (*@     // @dec for @ts in @rank.                                           @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
