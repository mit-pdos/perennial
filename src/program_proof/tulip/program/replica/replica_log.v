From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import
  encode_string encode_kvmap_from_slice.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_logRead (fname : byte_string) (ts : u64) (key : byte_string) (bs : list u8) :
    {{{ fname f↦ bs }}}
      logRead #(LitString fname) #ts #(LitString key)
    {{{ (bs' : list u8), RET #(); fname f↦ bs' }}}.
  Proof.
    iIntros (Φ) "Hfile HΦ".
    wp_rec.

    (*@ func logRead(fname string, ts uint64, key string) {                     @*)
    (*@     // Create an inconsistent log entry for reading @key at @ts.        @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs1 := marshal.WriteInt(bs, CMD_READ)                               @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := util.EncodeString(bs2, key)                                  @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_EncodeString with "Hbs").
    iIntros (p4) "Hbs".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs3)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    wp_pures.
    destruct err; wp_pures.
    { wp_apply wp_Exit. iIntros "[]". }
    by iApply "HΦ".
  Qed.

  Theorem wp_logValidate
    (fname : byte_string) (ts : u64) (pwrsP : Slice.t) (pwrs : dbmap) (bs : list u8) :
    {{{ fname f↦ bs ∗ own_dbmap_in_slice pwrsP pwrs }}}
      logValidate #(LitString fname) #ts (to_val pwrsP) slice.nil
    {{{ (bs' : list u8), RET #(); fname f↦ bs' ∗ own_dbmap_in_slice pwrsP pwrs }}}.
  Proof.
    iIntros (Φ) "[Hfile Hpwrs] HΦ".
    wp_rec.

    (*@ func logValidate(fname string, ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) { @*)
    (*@     // Create an inconsistent log entry for validating @ts with @pwrs and @ptgs. @*)
    (*@     bs := make([]byte, 0, 64)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs1 := marshal.WriteInt(bs, CMD_VALIDATE)                           @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := util.EncodeKVMapFromSlice(bs2, pwrs)                         @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_EncodeKVMapFromSlice with "[$Hbs $Hpwrs]").
    iIntros (p4 mdata) "[Hbs [Hpwrs %Hmdata]]".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs3)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    wp_pures.
    destruct err; wp_pures.
    { wp_apply wp_Exit. iIntros "[]". }
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_logFastPrepare
    (fname : byte_string) (ts : u64) (pwrsP : Slice.t) (pwrs : dbmap) (bs : list u8) :
    {{{ fname f↦ bs ∗ own_dbmap_in_slice pwrsP pwrs }}}
      logFastPrepare #(LitString fname) #ts (to_val pwrsP) slice.nil
    {{{ (bs' : list u8), RET #(); fname f↦ bs' ∗ own_dbmap_in_slice pwrsP pwrs }}}.
  Proof.
    iIntros (Φ) "[Hfile Hpwrs] HΦ".
    wp_rec.

    (*@ func logFastPrepare(fname string, ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) { @*)
    (*@     // Create an inconsistent log entry for fast preparing @ts.         @*)
    (*@     bs := make([]byte, 0, 64)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs1 := marshal.WriteInt(bs, CMD_FAST_PREPARE)                       @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := util.EncodeKVMapFromSlice(bs2, pwrs)                         @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_EncodeKVMapFromSlice with "[$Hbs $Hpwrs]").
    iIntros (p4 mdata) "[Hbs [Hpwrs %Hmdata]]".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs3)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    wp_pures.
    destruct err; wp_pures.
    { wp_apply wp_Exit. iIntros "[]". }
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_logAccept (fname : byte_string) (ts : u64) (rank : u64) (dec : bool) (bs : list u8) :
    {{{ fname f↦ bs }}}
      logAccept #(LitString fname) #ts #rank #dec
    {{{ (bs' : list u8), RET #(); fname f↦ bs' }}}.
  Proof.
    iIntros (Φ) "Hfile HΦ".
    wp_rec.

    (*@ func logAccept(fname string, ts uint64, rank uint64, dec bool) {        @*)
    (*@     // Create an inconsistent log entry for accepting prepare decision @dec for @*)
    (*@     // @ts in @rank.                                                    @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs1 := marshal.WriteInt(bs, CMD_ACCEPT)                             @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := marshal.WriteInt(bs2, rank)                                  @*)
    (*@     bs4 := marshal.WriteBool(bs3, dec)                                  @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p4) "Hbs".
    wp_apply (wp_WriteBool with "Hbs").
    iIntros (p5) "Hbs".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs4)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    wp_pures.
    destruct err; wp_pures.
    { wp_apply wp_Exit. iIntros "[]". }
    iApply "HΦ".
    by iFrame.
  Qed.

End program.
