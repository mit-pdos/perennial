From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.


  Theorem wp_GroupCoordinator__SendRead
    (gcoord : loc) (rid : u64) (ts : u64) (key : string) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendRead #gcoord #rid #ts #(LitString key)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendRead(rid, ts uint64, key string) {  @*)
    (*@     gcoord.Send(rid, message.EncodeTxnRead(ts, key))                    @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendFastPrepare
    (gcoord : loc) (rid : u64) (ts : u64) (pwrsP : loc) (ptgsP : Slice.t) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendFastPrepare #gcoord #rid #ts #pwrsP (to_val ptgsP)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendFastPrepare(rid, ts uint64, pwrs tulip.KVMap, ptgs []uint64) { @*)
    (*@     gcoord.Send(rid, message.EncodeTxnFastPrepare(ts, pwrs, ptgs))      @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendValidate
    (gcoord : loc) (rid : u64) (ts : u64) (rank : u64) (pwrsP : loc) (ptgsP : Slice.t) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendValidate #gcoord #rid #ts #rank #pwrsP (to_val ptgsP)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendValidate(rid, ts, rank uint64, pwrs tulip.KVMap, ptgs []uint64) { @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendPrepare
    (gcoord : loc) (rid : u64) (tsW : u64) (rank : u64) gid γ :
    let ts := uint.nat tsW in
    is_group_prepare_proposal γ gid ts 1%nat true -∗
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendPrepare #gcoord #rid #tsW #rank
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendPrepare(rid, ts, rank uint64) {     @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendUnprepare
    (gcoord : loc) (rid : u64) (tsW : u64) (rank : u64) gid γ :
    let ts := uint.nat tsW in
    is_group_prepare_proposal γ gid ts 1%nat false -∗
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendUnprepare #gcoord #rid #tsW #rank
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendUnprepare(rid, ts, rank uint64) {   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendQuery
    (gcoord : loc) (rid : u64) (ts : u64) (rank : u64) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendQuery #gcoord #rid #ts #rank
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendQuery(rid, ts, rank uint64) {       @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendRefresh
    (gcoord : loc) (rid : u64) (ts : u64) (rank : u64) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendRefresh #gcoord #rid #ts #rank
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendRefresh(rid, ts, rank uint64) {     @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendCommit
    (gcoord : loc) (rid : u64) (tsW : u64) (pwrsP : loc) q (pwrs : dbmap) gid γ :
    let ts := uint.nat tsW in
    safe_commit γ gid ts pwrs -∗
    is_gcoord gcoord gid γ -∗
    {{{ own_map pwrsP q pwrs }}}
      GroupCoordinator__SendCommit #gcoord #rid #tsW #pwrsP
    {{{ RET #(); own_map pwrsP q pwrs }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendCommit(rid, ts uint64, pwrs tulip.KVMap) { @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendAbort (gcoord : loc) (rid : u64) (tsW : u64) gid γ :
    let ts := uint.nat tsW in
    safe_abort γ ts -∗
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendAbort #gcoord #rid #tsW
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendAbort(rid, ts uint64) {             @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
