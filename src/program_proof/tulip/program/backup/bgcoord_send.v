From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupCoordinator__SendInquire
    (gcoord : loc) (rid : u64) (tsW : u64) (rankW : u64) addrm gid γ :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    rid ∈ dom addrm ->
    is_backup_gcoord_with_addrm gcoord addrm rank ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__SendInquire #gcoord #rid #tsW #rankW
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *BackupGroupCoordinator) SendInquire(rid, ts, rank uint64) { @*)
    (*@     data := message.EncodeTxnInquireRequest(ts, rank)                   @*)
    (*@     gcoord.Send(rid, data)                                              @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupGroupCoordinator__SendValidate
    (gcoord : loc) (rid : u64) (tsW : u64) (rankW : u64) (pwrsP : loc) (ptgsP : Slice.t)
    q (pwrs : dbmap) (ptgs : txnptgs) addrm gid γ :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    rid ∈ dom addrm ->
    safe_txn_pwrs γ gid ts pwrs -∗
    is_txnptgs_in_slice ptgsP ptgs -∗
    is_backup_gcoord_with_addrm gcoord addrm rank ts gid γ -∗
    {{{ own_map pwrsP q pwrs }}}
      BackupGroupCoordinator__SendValidate #gcoord #rid #tsW #rankW #pwrsP (to_val ptgsP)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *BackupGroupCoordinator) SendValidate(rid, ts, rank uint64, pwrs tulip.KVMap, ptgs []uint64) { @*)
    (*@     data := message.EncodeTxnValidateRequest(ts, rank, pwrs, ptgs)      @*)
    (*@     gcoord.Send(rid, data)                                              @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupGroupCoordinator__SendPrepare
    (gcoord : loc) (rid : u64) (tsW : u64) (rankW : u64) addrm gid γ :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    rid ∈ dom addrm ->
    is_group_prepare_proposal γ gid ts rank true -∗
    is_backup_gcoord_with_addrm gcoord addrm rank ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__SendPrepare #gcoord #rid #tsW #rankW
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *BackupGroupCoordinator) SendPrepare(rid, ts, rank uint64) { @*)
    (*@     data := message.EncodeTxnPrepareRequest(ts, rank)                   @*)
    (*@     gcoord.Send(rid, data)                                              @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupGroupCoordinator__SendUnprepare
    (gcoord : loc) (rid : u64) (tsW : u64) (rankW : u64) addrm gid γ :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    rid ∈ dom addrm ->
    is_group_prepare_proposal γ gid ts rank false -∗
    is_backup_gcoord_with_addrm gcoord addrm rank ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__SendUnprepare #gcoord #rid #tsW #rankW
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *BackupGroupCoordinator) SendUnprepare(rid, ts, rank uint64) { @*)
    (*@     data := message.EncodeTxnUnprepareRequest(ts, rank)                 @*)
    (*@     gcoord.Send(rid, data)                                              @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupGroupCoordinator__SendRefresh
    (gcoord : loc) (rid : u64) (tsW : u64) (rankW : u64) addrm gid γ :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    rid ∈ dom addrm ->
    is_backup_gcoord_with_addrm gcoord addrm rank ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__SendRefresh #gcoord #rid #tsW #rankW
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *BackupGroupCoordinator) SendRefresh(rid, ts, rank uint64) { @*)
    (*@     data := message.EncodeTxnRefreshRequest(ts, rank)                   @*)
    (*@     gcoord.Send(rid, data)                                              @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
