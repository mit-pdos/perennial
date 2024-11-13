From Perennial.program_proof.tulip Require Import prelude.
From Perennial.program_proof.tulip.program Require Import tuple index txnlog.
(* From Perennial.program_proof.tulip.tulip.invariance Require Import advance accept. *)
From Goose.github_com.mit_pdos.tulip Require Import replica.

Section replica.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type Replica struct {                                                   @*)
  (*@     // Mutex.                                                           @*)
  (*@     mu *sync.Mutex                                                      @*)
  (*@     // Replica ID.                                                      @*)
  (*@     rid uint64                                                          @*)
  (*@     // Replicated transaction log.                                      @*)
  (*@     txnlog *txnlog.TxnLog                                               @*)
  (*@     //                                                                  @*)
  (*@     // Fields below are application states.                             @*)
  (*@     //                                                                  @*)
  (*@     // LSN up to which all commands have been applied.                  @*)
  (*@     lsna   uint64                                                       @*)
  (*@     // Write sets of validated transactions.                            @*)
  (*@     prepm  map[uint64][]tulip.WriteEntry                                @*)
  (*@     // Participant groups of validated transactions.                    @*)
  (*@     ptgsm  map[uint64][]uint64                                          @*)
  (*@     // Prepare status table.                                            @*)
  (*@     pstbl  map[uint64]PrepareStatusEntry                                @*)
  (*@     // Transaction status table; mapping from transaction timestamps to their @*)
  (*@     // commit/abort status.                                             @*)
  (*@     txntbl map[uint64]bool                                              @*)
  (*@     // Mapping from keys to their prepare timestamps.                   @*)
  (*@     ptsm  map[string]uint64                                             @*)
  (*@     // Mapping from keys to their smallest preparable timestamps.       @*)
  (*@     sptsm map[string]uint64                                             @*)
  (*@     // Index.                                                           @*)
  (*@     idx    *index.Index                                                 @*)
  (*@     //                                                                  @*)
  (*@     // Fields below are group info initialized after creation of all replicas. @*)
  (*@     //                                                                  @*)
  (*@     // Replicas in the same group. Read-only.                           @*)
  (*@     rps    map[uint64]grove_ffi.Address                                 @*)
  (*@     // ID of the replica believed to be the leader of this group. Used to @*)
  (*@     // initialize backup coordinators.                                  @*)
  (*@     leader uint64                                                       @*)
  (*@ }                                                                       @*)
  Definition own_replica_cm (rp : loc) (cm : gmap nat bool) : iProp Σ :=
    ∃ (txntblP : loc) (txntbl : gmap u64 bool),
      "HtxntblP" ∷ rp ↦[Replica :: "txntbl"] #txntblP ∗
      "Htxntbl"  ∷ own_map txntblP (DfracOwn 1) txntbl ∗
      "%Hcmabs"  ∷ ⌜(kmap Z.of_nat cm : gmap Z bool) = kmap uint.Z txntbl⌝.

  Definition own_replica_cpm (rp : loc) (cpm : gmap nat dbmap) : iProp Σ :=
    ∃ (prepmP : loc) (prepmS : gmap u64 Slice.t) (prepm : gmap u64 dbmap),
      "HprepmP"  ∷ rp ↦[Replica :: "prepm"] #prepmP ∗
      "HprepmS"  ∷ own_map prepmP (DfracOwn 1) prepmS ∗
      "Hprepm"   ∷ ([∗ map] s; m ∈ prepmS; prepm, ∃ l, own_dbmap_in_slice s l m) ∗
      "%Hcpmabs" ∷ ⌜(kmap Z.of_nat cpm : gmap Z dbmap) = kmap uint.Z prepm⌝.

  Definition absrel_ptsm (ptsm : gmap dbkey nat) (ptsmM : gmap dbkey u64) :=
    ∀ k,
    k ∈ keys_all ->
    match ptsmM !! k with
    | Some ptsW => ptsm !! k = Some (uint.nat ptsW)
    | _ => ptsm !! k = Some O
    end.

  Definition own_replica_ptsm_sptsm
    (rp : loc) (ptsm sptsm : gmap dbkey nat) : iProp Σ :=
    ∃ (ptsmP : loc) (sptsmP : loc) (ptsmM : gmap dbkey u64) (sptsmM : gmap dbkey u64),
      "HptsmP"     ∷ rp ↦[Replica :: "ptsm"] #ptsmP ∗
      "HsptsmP"    ∷ rp ↦[Replica :: "sptsm"] #sptsmP ∗
      "HptsmM"     ∷ own_map ptsmP (DfracOwn 1) ptsmM ∗
      "HsptsmM"    ∷ own_map sptsmP (DfracOwn 1) sptsmM ∗
      "%Hptsmabs"  ∷ ⌜absrel_ptsm ptsm ptsmM⌝ ∗
      "%Hsptsmabs" ∷ ⌜absrel_ptsm sptsm sptsmM⌝.

  Definition own_replica_bm_laim
    (rp : loc) (bm : gmap nat ballot) (laim : gmap nat nat) : iProp Σ :=
    (* TODO: find the right type for pstbl and the absrel. *)
    ∃ (pstblP : loc) (pstbl : gmap u64 u64),
      "HpstblP" ∷ rp ↦[Replica :: "pstbl"] #pstblP ∗
      "Hpstbl"  ∷ own_map pstblP (DfracOwn 1) pstbl.

  Definition own_replica (rp : loc) (gid rid : u64) α γ : iProp Σ :=
    ∃ (lsna : u64) (cm : gmap nat bool) (histm : gmap dbkey dbhist)
      (cpm : gmap nat dbmap) (ptgsm : gmap nat (gset u64))
      (sptsm ptsm : gmap dbkey nat) (bm : gmap nat ballot) (laim : gmap nat nat)
      (clog : dblog) (ilog : list (nat * icommand)),
      let log := merge_clog_ilog clog ilog in
      "Hlsna"      ∷ rp ↦[Replica :: "lsna"] #lsna ∗
      "Hcm"        ∷ own_replica_cm rp cm ∗
      "Hphistm"    ∷ ([∗ map] k ↦ h ∈ histm, own_phys_hist_half α k h) ∗
      "Hcpm"       ∷ own_replica_cpm rp cpm ∗
      "Hptsmsptsm" ∷ own_replica_ptsm_sptsm rp ptsm sptsm ∗
      "Hbmlaim"    ∷ own_replica_bm_laim rp bm laim ∗
      "Hclog"      ∷ own_replica_clog_half γ gid rid clog ∗
      "Hilog"      ∷ own_replica_ilog_half γ gid rid ilog ∗
      "%Hexec"     ∷ ⌜execute_cmds log = LocalState cm histm cpm ptgsm sptsm ptsm bm laim⌝.

  Definition is_replica (rp : loc) α γ : iProp Σ :=
    ∃ (gid rid : u64) (mu : loc) (txnlog : loc) (idx : loc),
      "#HmuP"     ∷ readonly (rp ↦[Replica :: "mu"] #mu) ∗
      "#Hlock"    ∷ is_lock tulipNS #mu (own_replica rp gid rid α γ) ∗
      "#HtxnlogP" ∷ readonly (rp ↦[Replica :: "txnlog"] #txnlog) ∗
      "#Htxnlog"  ∷ is_txnlog txnlog gid γ ∗
      "#HidxP"    ∷ readonly (rp ↦[Replica :: "idx"] #idx) ∗
      "#Hidx"     ∷ is_index idx α ∗
      "%Hgid"     ∷ ⌜gid ∈ gids_all⌝.

  Definition key_writable_ptsm (ptsm : gmap dbkey nat) (key : dbkey) :=
    match ptsm !! key with
    | Some pts => pts = O
    | _ => False
    end.

  Definition key_writable_sptsm (sptsm : gmap dbkey nat) (ts : nat) (key : dbkey) :=
    match sptsm !! key with
    | Some spts => (spts < ts)%nat
    | _ => False
    end.

  Definition key_writable (ptsm sptsm : gmap dbkey nat) (ts : nat) (key : dbkey) :=
    key_writable_ptsm ptsm key ∧ key_writable_sptsm sptsm ts key.

  Theorem wp_Replica__writableKey rp (ts : u64) key ptsm sptsm :
    uint.Z ts ≠ 0 ->
    key ∈ keys_all ->
    {{{ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__writableKey #rp #ts #(LitString key)
    {{{ (ok : bool), RET #ok;
        own_replica_ptsm_sptsm rp ptsm sptsm ∗
        ⌜if ok then key_writable ptsm sptsm (uint.nat ts) key else True⌝
    }}}.
  Proof.
    iIntros (Htsnz Hkey Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) writableKey(ts uint64, key string) bool {            @*)
    (*@     // The default of prepare timestamps are 0, so no need to check existence. @*)
    (*@     pts := rp.ptsm[key]                                                 @*)
    (*@     if pts != 0 {                                                       @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapGet with "HptsmM").
    iIntros (pts okpts) "[%Hpts HptsmM]".
    wp_pures.
    case_bool_decide as Hptsz; wp_pures; last first.
    { iApply "HΦ". by iFrame. }

    (*@     // Even though the default of smallest preparable timestamps are 1, using @*)
    (*@     // the fact that @ts is positive also means no need to check existence. @*)
    (*@     spts := rp.sptsm[key]                                               @*)

    (*@     if ts <= spts {                                                     @*)

    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapGet with "HsptsmM").
    iIntros (spts okspts) "[%Hspts HsptsmM]".
    wp_pures.
    case_bool_decide as Hgespts; wp_pures.
    { iApply "HΦ". by iFrame "HptsmP HsptsmP ∗". }

    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    assert (Hwritable : key_writable ptsm sptsm (uint.nat ts) key).
    { inv Hptsz.
      split.
      { specialize (Hptsmabs _ Hkey).
        destruct okpts.
        { apply map_get_true in Hpts.
          rewrite Hpts uint_nat_W64_0 in Hptsmabs.
          by rewrite /key_writable_ptsm Hptsmabs.
        }
        apply map_get_false in Hpts as [Hpts _].
        rewrite Hpts in Hptsmabs.
        by rewrite /key_writable_ptsm Hptsmabs.
      }
      { specialize (Hsptsmabs _ Hkey).
        destruct okspts.
        { apply map_get_true in Hspts.
          rewrite Hspts in Hsptsmabs.
          rewrite /key_writable_sptsm Hsptsmabs.
          clear -Hgespts. word.
        }
        apply map_get_false in Hspts as [Hspts _].
        rewrite Hspts in Hsptsmabs.
        rewrite /key_writable_sptsm Hsptsmabs.
        clear -Hgespts Htsnz. word.
      }
    }
    by iFrame "HptsmP HsptsmP ∗".
  Qed.

  Definition key_readable (ptsm : gmap dbkey nat) (ts : nat) (key : dbkey) :=
    match ptsm !! key with
    | Some pts => pts = O ∨ (ts < pts)%nat
    | _ => False
    end.

  Theorem wp_Replica__readableKey rp (ts : u64) key ptsm sptsm :
    key ∈ keys_all ->
    {{{ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__readableKey #rp #ts #(LitString key)
    {{{ (ok : bool), RET #ok;
        own_replica_ptsm_sptsm rp ptsm sptsm ∗
        ⌜if ok then key_readable ptsm (uint.nat ts) key else True⌝
    }}}.
  Proof.
    iIntros (Hkey Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) readableKey(ts uint64, key string) bool {            @*)
    (*@     pts := rp.ptsm[key]                                                 @*)
    (*@     if pts != 0 && pts <= ts {                                          @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapGet with "HptsmM").
    iIntros (pts ok) "[%Hpts HptsmM]".
    wp_apply wp_and_pure.
    { wp_pures. by rewrite -bool_decide_not. }
    { iIntros (_). by wp_pures. }
    case_bool_decide as Hcond; wp_pures.
    { iApply "HΦ". by iFrame. }

    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    apply Classical_Prop.not_and_or in Hcond.
    assert (Hreadable : key_readable ptsm (uint.nat ts) key).
    { specialize (Hptsmabs _ Hkey).
      destruct ok.
      { apply map_get_true in Hpts.
        rewrite Hpts in Hptsmabs.
        rewrite /key_readable Hptsmabs.
        destruct Hcond as [Hz | Hlt].
        { left. apply dec_stable in Hz. inv Hz. by rewrite uint_nat_W64_0. }
        { right. clear -Hlt. word. }
      }
      apply map_get_false in Hpts as [Hpts _].
      rewrite Hpts in Hptsmabs.
      rewrite /key_readable Hptsmabs.
      by left.
    }
    by iFrame.
  Qed.

  Theorem wp_Replica__acquireKey rp (ts : u64) key ptsm sptsm :
    {{{ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__acquireKey #rp #ts #(LitString key)
    {{{ RET #();
        own_replica_ptsm_sptsm rp (<[key := uint.nat ts]> ptsm) (<[key := uint.nat ts]> sptsm)
    }}}.
  Proof.
    iIntros (Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) acquireKey(ts uint64, key string) {                  @*)
    (*@     rp.ptsm[key]  = ts                                                  @*)
    (*@     rp.sptsm[key] = ts                                                  @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapInsert with "HptsmM"); first done.
    iIntros "HptsmM".
    wp_loadField.
    wp_apply (wp_MapInsert with "HsptsmM"); first done.
    iIntros "HsptsmM".
    wp_pures.
    iApply "HΦ".
    iFrame "HptsmP HsptsmP ∗".
    iPureIntro.
    split.
    { intros k Hk.
      destruct (decide (k = key)) as [-> | Hne]; last first.
      { do 2 (rewrite lookup_insert_ne; last done).
        by apply Hptsmabs.
      }
      by rewrite 2!lookup_insert.
    }
    { intros k Hk.
      destruct (decide (k = key)) as [-> | Hne]; last first.
      { do 2 (rewrite lookup_insert_ne; last done).
        by apply Hsptsmabs.
      }
      by rewrite 2!lookup_insert.
    }
  Qed.

  Theorem wp_Replica__releaseKey rp key ptsm sptsm :
    {{{ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__releaseKey #rp #(LitString key)
    {{{ RET #();
        own_replica_ptsm_sptsm rp (<[key := O]> ptsm) sptsm
    }}}.
  Proof.
    iIntros (Φ) "Hrp HΦ".
    wp_rec.
    (*@ func (rp *Replica) releaseKey(key string) {                             @*)
    (*@     delete(rp.ptsm, key)                                                @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapDelete with "HptsmM").
    iIntros "HptsmM".
    wp_pures.
    iApply "HΦ".
    iFrame "∗ %".
    iPureIntro.
    intros k Hk.
    destruct (decide (k = key)) as [-> | Hne]; last first.
    { rewrite lookup_delete_ne; last done.
      rewrite lookup_insert_ne; last done.
      by apply Hptsmabs.
    }
    by rewrite lookup_delete lookup_insert.
  Qed.

  Theorem wp_Replica__bumpKey rp (ts : u64) key ptsm sptsm :
    uint.Z ts ≠ 0 ->
    key ∈ keys_all ->
    {{{ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__bumpKey #rp #ts #(LitString key)
    {{{ (spts : nat), RET #(bool_decide (spts < pred (uint.nat ts))%nat);
        own_replica_ptsm_sptsm rp ptsm (<[key := (spts `max` pred (uint.nat ts))%nat]> sptsm) ∗
        ⌜sptsm !! key = Some spts⌝
    }}}.
  Proof.
    iIntros (Htsnz Hkey Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) bumpKey(ts uint64, key string) bool {                @*)
    (*@     spts := rp.sptsm[key]                                               @*)
    (*@     if ts - 1 <= spts {                                                 @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@     rp.sptsm[key] = ts - 1                                              @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapGet with "HsptsmM").
    iIntros (sptsW ok) "[%Hspts HsptsmM]".
    wp_pures.
    case_bool_decide as Hcond; wp_pures.
    { rewrite word.unsigned_sub_nowrap in Hcond; last word.
      destruct ok.
      { apply map_get_true in Hspts.
        iSpecialize ("HΦ" $! (uint.nat sptsW)).
        case_bool_decide as Hts; first word.
        iApply "HΦ".
        iFrame "HptsmP HsptsmP ∗ %".
        iPureIntro.
        split; last first.
        { specialize (Hsptsmabs _ Hkey).
          by rewrite Hspts in Hsptsmabs.
        }
        intros k Hk.
        destruct (decide (k = key)) as [-> | Hne]; last first.
        { rewrite lookup_insert_ne; last done.
          by apply Hsptsmabs.
        }
        rewrite lookup_insert Hspts.
        f_equal.
        clear -Hts. word.
      }
      { apply map_get_false in Hspts as [Hspts ->].
        simpl in Hcond.
        iSpecialize ("HΦ" $! O).
        case_bool_decide as Hts; first word.
        assert (uint.Z ts = 1) by word.
        iApply "HΦ".
        iFrame "HptsmP HsptsmP ∗ %".
        iPureIntro.
        assert (Hz : sptsm !! key = Some O).
        { specialize (Hsptsmabs _ Hkey).
          by rewrite Hspts in Hsptsmabs.
        }
        split; last apply Hz.
        replace (_ `max` _)%nat with O; last word.
        by rewrite insert_id.
      }
    }
    rewrite word.unsigned_sub_nowrap in Hcond; last word.
    wp_loadField.
    wp_apply (wp_MapInsert with "HsptsmM"); first done.
    iIntros "HsptsmM".
    wp_pures.
    destruct ok.
    { apply map_get_true in Hspts.
      iSpecialize ("HΦ" $! (uint.nat sptsW)).
      case_bool_decide as Hts; last word.
      iApply "HΦ".
      iFrame "HptsmP HsptsmP ∗ %".
      iPureIntro.
      split; last first.
      { specialize (Hsptsmabs _ Hkey).
        by rewrite Hspts in Hsptsmabs.
      }
      intros k Hk.
      destruct (decide (k = key)) as [-> | Hne]; last first.
      { do 2 (rewrite lookup_insert_ne; last done).
        by apply Hsptsmabs.
      }
      rewrite 2!lookup_insert.
      f_equal.
      clear -Hcond. word.
    }
    { apply map_get_false in Hspts as [Hspts ->].
      simpl in Hcond.
      iSpecialize ("HΦ" $! O).
      case_bool_decide as Hts; last word.
      { iApply "HΦ".
        assert (Hsptsmkey : sptsm !! key = Some O).
        { specialize (Hsptsmabs _ Hkey).
          by rewrite Hspts in Hsptsmabs.
        }
        iFrame "HptsmP HsptsmP ∗ %".
        iPureIntro.
        intros k Hk.
        destruct (decide (k = key)) as [-> | Hne]; last first.
        { do 2 (rewrite lookup_insert_ne; last done).
          by apply Hsptsmabs.
        }
        rewrite 2!lookup_insert.
        f_equal.
        word.
      }
    }
  Qed.

End replica.
