From Perennial.program_proof.rsm.pure Require Import serialize.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import
  encode_string encode_kvmap_from_slice encode_ints.

(* Copy pasted from grove_ffi_typed.v *)
Ltac inv_undefined :=
  match goal with
  | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] =>
    destruct e; try (apply suchThat_false in H; contradiction)
  end.
Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
  [ apply heap_base_atomic; cbn [relation.denote base_trans]; intros * H;
    repeat inv_undefined;
    try solve [ apply atomically_is_val in H; auto ]
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].
Local Ltac solve_atomic2 :=
  solve_atomic;
  (* TODO(Joe): Cleanup *)
  repeat match goal with
    | [ H: relation.denote _ ?s1 ?s2 ?v |- _ ] => inversion_clear H
    | _ => progress monad_inv
    | _ => case_match
    end; eauto.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_logRead
    (fname : byte_string) (lsnW tsW : u64) (key : byte_string) :
    let lsn := uint.nat lsnW in
    let ts := uint.nat tsW in
    ⊢
    {{{ True }}}
    <<< ∀∀ bs ilog, fname f↦ bs ∗ ⌜encode_ilog ilog bs⌝ >>>
      logRead #(LitString fname) #lsnW #tsW #(LitString key) @ ∅
    <<< ∃∃ bs' (failed : bool),
            if failed
            then fname f↦ bs
            else fname f↦ bs' ∗
                 ⌜encode_ilog (ilog ++ [(lsn, CmdRead ts key)]) bs'⌝
    >>>
    {{{ RET #(); ⌜not failed⌝ }}}.
  Proof.
    iIntros (lsn ts Φ) "!> _ HAU".
    wp_rec.

    (*@ func logRead(fname string, lsn, ts uint64, key string) {                @*)
    (*@     // Create an inconsistent log entry for reading @key at @ts.        @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs0 := marshal.WriteInt(bs, lsn)                                    @*)
    (*@     bs1 := marshal.WriteInt(bs0, CMD_READ)                              @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := util.EncodeString(bs2, key)                                  @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p4) "Hbs".
    wp_apply (wp_EncodeString with "Hbs").
    iIntros (p5) "Hbs".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs3)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iApply (wp_ncatomic _ _ ∅).
    { solve_atomic2. }
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    rewrite -!app_assoc app_nil_l.
    set frag := _ ++ _.
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    iMod "HAU" as (bs ilog) "[[Hfile %Henc] HAU]".
    iModIntro.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    destruct err eqn:Herr.
    { (* Case: Write failed. *)
      iMod ("HAU" $! bs true with "[$Hfile]") as "HΦ".
      iModIntro.
      wp_pures.
      wp_apply wp_Exit. iIntros "[]".
    }
    (* Case: Write succeeded. *)
    iMod ("HAU" $! _ false with "[$Hfile]") as "HΦ".
    { iPureIntro.
      rewrite /encode_ilog.
      destruct Henc as (frags & Hencfrag & Hserial).
      exists (frags ++ [frag]).
      split.
      { apply Forall2_app; first apply Hencfrag.
        apply Forall2_cons_2; last by apply Forall2_nil.
        simpl.
        exists (u64_le (U64 0) ++ u64_le ts ++ encode_string key).
        subst frag.
        assert (W64 lsn = lsnW) as -> by word.
        by assert (W64 ts = tsW) as -> by word.
      }
      by rewrite serialize_snoc Hserial.
    }
    iModIntro.
    wp_pures.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    by auto.
  Qed.

  Theorem wp_logAcquire
    (fname : byte_string) (lsnW tsW : u64) (pwrsP : Slice.t) (pwrs : dbmap)
    (ptgsP : Slice.t) (ptgs : txnptgs) :
    let lsn := uint.nat lsnW in
    let ts := uint.nat tsW in
    is_dbmap_in_slice pwrsP pwrs -∗
    is_txnptgs_in_slice ptgsP ptgs -∗
    {{{ True }}}
    <<< ∀∀ bs ilog, fname f↦ bs ∗ ⌜encode_ilog ilog bs⌝ >>>
      logAcquire #(LitString fname) #lsnW #tsW (to_val pwrsP) (to_val ptgsP) @ ∅
    <<< ∃∃ bs' (failed : bool),
            if failed
            then fname f↦ bs
            else fname f↦ bs' ∗
                 ⌜encode_ilog (ilog ++ [(lsn, CmdAcquire ts pwrs ptgs)]) bs'⌝
    >>>
    {{{ RET #(); ⌜not failed⌝ }}}.
  Proof.
    iIntros (lsn ts) "#Hpwrs #Hptgs".
    iIntros (Φ) "!> _ HAU".
    wp_rec.

    (*@ func logAcquire(fname string, lsn, ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) { @*)
    (*@     // Create an inconsistent log entry for validating @ts with @pwrs and @ptgs. @*)
    (*@     bs := make([]byte, 0, 64)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs0 := marshal.WriteInt(bs, lsn)                                    @*)
    (*@     bs1 := marshal.WriteInt(bs0, CMD_ACQUIRE)                           @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := util.EncodeKVMapFromSlice(bs2, pwrs)                         @*)
    (*@     bs4 := util.EncodeInts(bs3, ptgs)                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p4) "Hbs".
    iMod (is_dbmap_in_slice_unpersist with "Hpwrs") as "HpwrsR".
    wp_apply (wp_EncodeKVMapFromSlice with "[$Hbs $HpwrsR]").
    iIntros (p5 mdata) "[Hbs [_ %Hmdata]]".
    wp_apply (wp_EncodeInts__encode_txnptgs with "Hptgs Hbs").
    iIntros (p6 gdata) "[Hbs %Hgdata]".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs4)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iApply (wp_ncatomic _ _ ∅).
    { solve_atomic2. }
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    rewrite -!app_assoc app_nil_l.
    set frag := _ ++ _.
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    iMod "HAU" as (bs ilog) "[[Hfile %Henc] HAU]".
    iModIntro.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    destruct err eqn:Herr.
    { (* Case: Write failed. *)
      iMod ("HAU" $! bs true with "[$Hfile]") as "HΦ".
      iModIntro.
      wp_pures.
      wp_apply wp_Exit. iIntros "[]".
    }
    (* Case: Write succeeded. *)
    iMod ("HAU" $! _ false with "[$Hfile]") as "HΦ".
    { iPureIntro.
      rewrite /encode_ilog.
      destruct Henc as (frags & Hencfrag & Hserial).
      exists (frags ++ [frag]).
      split.
      { apply Forall2_app; first apply Hencfrag.
        apply Forall2_cons_2; last by apply Forall2_nil.
        simpl.
        exists (u64_le (U64 1) ++ u64_le ts ++ mdata ++ gdata).
        subst frag.
        assert (W64 lsn = lsnW) as -> by word.
        assert (W64 ts = tsW) as -> by word.
        split; first done.
        by exists mdata, gdata.
      }
      by rewrite serialize_snoc Hserial.
    }
    iModIntro.
    wp_pures.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    by auto.
  Qed.

  Theorem wp_logFastPrepare
    (fname : byte_string) (lsnW tsW : u64) (pwrsP : Slice.t) (pwrs : dbmap)
    (ptgsP : Slice.t) (ptgs : txnptgs) :
    let lsn := uint.nat lsnW in
    let ts := uint.nat tsW in
    let icmds := [(lsn, CmdAcquire ts pwrs ptgs); (lsn, CmdAccept ts O true)] in
    is_dbmap_in_slice pwrsP pwrs -∗
    is_txnptgs_in_slice ptgsP ptgs -∗
    {{{ True }}}
    <<< ∀∀ bs ilog, fname f↦ bs ∗ ⌜encode_ilog ilog bs⌝ >>>
      logFastPrepare #(LitString fname) #lsnW #tsW (to_val pwrsP) (to_val ptgsP) @ ∅
    <<< ∃∃ bs' (failed : bool),
            if failed
            then fname f↦ bs
            else fname f↦ bs' ∗
                 ⌜encode_ilog (ilog ++ icmds) bs'⌝
    >>>
    {{{ RET #(); ⌜not failed⌝ }}}.
  Proof.
    iIntros (lsn ts icmds) "#Hpwrs #Hptgs".
    iIntros (Φ) "!> _ HAU".
    wp_rec.

    (*@ func logFastPrepare(fname string, lsn, ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) { @*)
    (*@     // Create an inconsistent log entry for fast preparing @ts.         @*)
    (*@     bs := make([]byte, 0, 128)                                          @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs0 := marshal.WriteInt(bs, lsn)                                    @*)
    (*@     bs1 := marshal.WriteInt(bs0, CMD_ACQUIRE)                           @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := util.EncodeKVMapFromSlice(bs2, pwrs)                         @*)
    (*@     bs4 := util.EncodeInts(bs3, ptgs)                                   @*)
    (*@     bs5 := marshal.WriteInt(bs4, lsn)                                   @*)
    (*@     bs6 := marshal.WriteInt(bs5, CMD_ACCEPT)                            @*)
    (*@     bs7 := marshal.WriteInt(bs6, ts)                                    @*)
    (*@     bs8 := marshal.WriteInt(bs7, 0)                                     @*)
    (*@     bs9 := marshal.WriteBool(bs8, true)                                 @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p4) "Hbs".
    iMod (is_dbmap_in_slice_unpersist with "Hpwrs") as "HpwrsR".
    wp_apply (wp_EncodeKVMapFromSlice with "[$Hbs $HpwrsR]").
    iIntros (p5 mdata) "[Hbs [_ %Hmdata]]".
    wp_apply (wp_EncodeInts__encode_txnptgs with "Hptgs Hbs").
    iIntros (p6 gdata) "[Hbs %Hgdata]".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p7) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p8) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p9) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p10) "Hbs".
    wp_apply (wp_WriteBool with "Hbs").
    iIntros (p11) "Hbs".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs9)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iApply (wp_ncatomic _ _ ∅).
    { solve_atomic2. }
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    rewrite -4!app_assoc app_nil_l.
    rewrite -(app_assoc _ _ gdata).
    rewrite -(app_assoc _ _ (mdata ++ gdata)).
    rewrite -(app_assoc _ _ (u64_le tsW ++ mdata ++ gdata)).
    set fragacq := _ ++ u64_le (W64 1) ++ _.
    set fragacp := _ ++ u64_le (W64 3) ++ _.
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    iMod "HAU" as (bs ilog) "[[Hfile %Henc] HAU]".
    iModIntro.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    destruct err eqn:Herr.
    { (* Case: Write failed. *)
      iMod ("HAU" $! bs true with "[$Hfile]") as "HΦ".
      iModIntro.
      wp_pures.
      wp_apply wp_Exit. iIntros "[]".
    }
    (* Case: Write succeeded. *)
    iMod ("HAU" $! _ false with "[$Hfile]") as "HΦ".
    { iPureIntro.
      rewrite /encode_ilog.
      destruct Henc as (frags & Hencfrag & Hserial).
      exists (frags ++ [fragacq; fragacp]).
      split.
      { apply Forall2_app; first apply Hencfrag.
        apply Forall2_cons_2.
        { simpl.
          exists (u64_le (U64 1) ++ u64_le ts ++ mdata ++ gdata).
          subst fragacq.
          assert (W64 lsn = lsnW) as -> by word.
          assert (W64 ts = tsW) as -> by word.
          split; first done.
          by exists mdata, gdata.
        }
        apply Forall2_cons_2; last by apply Forall2_nil.
        simpl.
        exists (u64_le (U64 3) ++ u64_le ts ++ u64_le (U64 O) ++ [U8 1]).
        subst fragacp.
        assert (W64 lsn = lsnW) as -> by word.
        assert (W64 ts = tsW) as -> by word.
        done.
      }
      by rewrite serialize_app Hserial.
    }
    iModIntro.
    wp_pures.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    by auto.
  Qed.

  Theorem wp_logAccept
    (fname : byte_string) (lsnW tsW rankW : u64) (dec : bool) :
    let lsn := uint.nat lsnW in
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    ⊢
    {{{ True }}}
    <<< ∀∀ bs ilog, fname f↦ bs ∗ ⌜encode_ilog ilog bs⌝ >>>
      logAccept #(LitString fname) #lsnW #tsW #rankW #dec @ ∅
    <<< ∃∃ bs' (failed : bool),
            if failed
            then fname f↦ bs
            else fname f↦ bs' ∗
                 ⌜encode_ilog (ilog ++ [(lsn, CmdAccept ts rank dec)]) bs'⌝
    >>>
    {{{ RET #(); ⌜not failed⌝ }}}.
  Proof.
    iIntros (lsn ts rank Φ) "!> _ HAU".
    wp_rec.

    (*@ func logAccept(fname string, lsn, ts uint64, rank uint64, dec bool) {   @*)
    (*@     // Create an inconsistent log entry for accepting prepare decision @dec for @*)
    (*@     // @ts in @rank.                                                    @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs0 := marshal.WriteInt(bs, lsn)                                    @*)
    (*@     bs1 := marshal.WriteInt(bs0, CMD_ACCEPT)                            @*)
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
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p5) "Hbs".
    wp_apply (wp_WriteBool with "Hbs").
    iIntros (p6) "Hbs".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs4)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iApply (wp_ncatomic _ _ ∅).
    { solve_atomic2. }
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    rewrite -!app_assoc app_nil_l.
    set frag := _ ++ _.
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    iMod "HAU" as (bs ilog) "[[Hfile %Henc] HAU]".
    iModIntro.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    destruct err eqn:Herr.
    { (* Case: Write failed. *)
      iMod ("HAU" $! bs true with "[$Hfile]") as "HΦ".
      iModIntro.
      wp_pures.
      wp_apply wp_Exit. iIntros "[]".
    }
    (* Case: Write succeeded. *)
    iMod ("HAU" $! _ false with "[$Hfile]") as "HΦ".
    { iPureIntro.
      rewrite /encode_ilog.
      destruct Henc as (frags & Hencfrag & Hserial).
      exists (frags ++ [frag]).
      split.
      { apply Forall2_app; first apply Hencfrag.
        apply Forall2_cons_2; last by apply Forall2_nil.
        simpl.
        exists (u64_le (U64 3) ++ u64_le ts ++ u64_le rank ++ [if dec then W8 1 else W8 0]).
        subst frag.
        assert (W64 lsn = lsnW) as -> by word.
        assert (W64 ts = tsW) as -> by word.
        by assert (W64 rank = rankW) as -> by word.
      }
      by rewrite serialize_snoc Hserial.
    }
    iModIntro.
    wp_pures.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    by auto.
  Qed.

  Theorem wp_logAdvance
    (fname : byte_string) (lsnW tsW rankW : u64) :
    let lsn := uint.nat lsnW in
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    ⊢
    {{{ True }}}
    <<< ∀∀ bs ilog, fname f↦ bs ∗ ⌜encode_ilog ilog bs⌝ >>>
      logAdvance #(LitString fname) #lsnW #tsW #rankW @ ∅
    <<< ∃∃ bs' (failed : bool),
            if failed
            then fname f↦ bs
            else fname f↦ bs' ∗
                 ⌜encode_ilog (ilog ++ [(lsn, CmdAdvance ts rank)]) bs'⌝
    >>>
    {{{ RET #(); ⌜not failed⌝ }}}.
  Proof.
    iIntros (lsn ts rank Φ) "!> _ HAU".
    wp_rec.

    (*@ func logAdvance(fname string, lsn, ts uint64, rank uint64) {            @*)
    (*@     // Create an inconsistent log entry for accepting prepare decision @dec for @*)
    (*@     // @ts in @rank.                                                    @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs0 := marshal.WriteInt(bs, lsn)                                    @*)
    (*@     bs1 := marshal.WriteInt(bs0, CMD_ADVANCE)                           @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := marshal.WriteInt(bs2, rank)                                  @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p4) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p5) "Hbs".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs3)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iApply (wp_ncatomic _ _ ∅).
    { solve_atomic2. }
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    rewrite -!app_assoc app_nil_l.
    set frag := _ ++ _.
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    iMod "HAU" as (bs ilog) "[[Hfile %Henc] HAU]".
    iModIntro.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    destruct err eqn:Herr.
    { (* Case: Write failed. *)
      iMod ("HAU" $! bs true with "[$Hfile]") as "HΦ".
      iModIntro.
      wp_pures.
      wp_apply wp_Exit. iIntros "[]".
    }
    (* Case: Write succeeded. *)
    iMod ("HAU" $! _ false with "[$Hfile]") as "HΦ".
    { iPureIntro.
      rewrite /encode_ilog.
      destruct Henc as (frags & Hencfrag & Hserial).
      exists (frags ++ [frag]).
      split.
      { apply Forall2_app; first apply Hencfrag.
        apply Forall2_cons_2; last by apply Forall2_nil.
        simpl.
        exists (u64_le (U64 2) ++ u64_le ts ++ u64_le rank).
        subst frag.
        assert (W64 lsn = lsnW) as -> by word.
        assert (W64 ts = tsW) as -> by word.
        by assert (W64 rank = rankW) as -> by word.
      }
      by rewrite serialize_snoc Hserial.
    }
    iModIntro.
    wp_pures.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    by auto.
  Qed.

End program.
