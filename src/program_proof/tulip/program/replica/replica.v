From Perennial.program_proof.tulip Require Import prelude.
From Perennial.program_proof.tulip.invariance Require Import validate execute accept.
From Perennial.program_proof Require Import std_proof.
From Perennial.program_proof.tulip.program Require Import tuple index txnlog.
From Goose.github_com.mit_pdos.tulip Require Import tulip replica.

Inductive rpres :=
| ReplicaOK
| ReplicaCommittedTxn
| ReplicaAbortedTxn
| ReplicaStaleCoordinator
| ReplicaFailedValidation
| ReplicaInvalidRank
| ReplicaWrongLeader.

Definition rpres_to_u64 (r : rpres) :=
  match r with
  | ReplicaOK => (U64 0)
  | ReplicaCommittedTxn => (U64 1)
  | ReplicaAbortedTxn => (U64 2)
  | ReplicaStaleCoordinator => (U64 3)
  | ReplicaFailedValidation => (U64 4)
  | ReplicaInvalidRank => (U64 5)
  | ReplicaWrongLeader => (U64 6)
  end.

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

  Lemma own_replica_ptsm_sptsm_dom rp ptsm sptsm :
    own_replica_ptsm_sptsm rp ptsm sptsm -∗
    ⌜keys_all ⊆ dom ptsm ∧ keys_all ⊆ dom sptsm⌝.
  Proof.
    iNamed 1.
    iPureIntro.
    split.
    - intros k Hk. specialize (Hptsmabs _ Hk).
      apply elem_of_dom. by destruct (ptsmM !! k).
    - intros k Hk. specialize (Hsptsmabs _ Hk).
      apply elem_of_dom. by destruct (sptsmM !! k).
  Qed.

  Definition ppsl_to_nat_bool (psl : ppsl) := (uint.nat psl.1, psl.2).

  Definition own_replica_psm_rkm
    (rp : loc) (psm : gmap nat (nat * bool)) (rkm : gmap nat nat) : iProp Σ :=
    ∃ (pstblP : loc) (rktblP : loc) (pstbl : gmap u64 ppsl) (rktbl : gmap u64 u64),
      "HpstblP"  ∷ rp ↦[Replica :: "pstbl"] #pstblP ∗
      "HrktblP"  ∷ rp ↦[Replica :: "rktbl"] #rktblP ∗
      "Hpstbl"   ∷ own_map pstblP (DfracOwn 1) pstbl ∗
      "Hrktbl"   ∷ own_map rktblP (DfracOwn 1) rktbl ∗
      "%Hpsmabs" ∷ ⌜(kmap Z.of_nat psm : gmap Z (nat * bool)) = kmap uint.Z (fmap ppsl_to_nat_bool pstbl)⌝ ∗
      "%Hrkmabs" ∷ ⌜(kmap Z.of_nat rkm : gmap Z nat) = kmap uint.Z (fmap (λ x, uint.nat x) rktbl)⌝.

  Definition own_replica (rp : loc) (gid rid : u64) γ α : iProp Σ :=
    ∃ (lsna : u64) (cm : gmap nat bool) (histm : gmap dbkey dbhist)
      (cpm : gmap nat dbmap) (ptgsm : gmap nat (gset u64))
      (sptsm ptsm : gmap dbkey nat) (psm : gmap nat (nat * bool)) (rkm : gmap nat nat)
      (clog cloga : dblog) (ilog : list (nat * icommand)),
      let log := merge_clog_ilog cloga ilog in
      "Hlsna"       ∷ rp ↦[Replica :: "lsna"] #lsna ∗
      "Hcm"         ∷ own_replica_cm rp cm ∗
      "Hphistm"     ∷ ([∗ map] k ↦ h ∈ histm, own_phys_hist_half α k h) ∗
      "Hcpm"        ∷ own_replica_cpm rp cpm ∗
      "Hptsmsptsm"  ∷ own_replica_ptsm_sptsm rp ptsm sptsm ∗
      "Hpsmrkm"     ∷ own_replica_psm_rkm rp psm rkm ∗
      "Hclog"       ∷ own_replica_clog_half γ gid rid clog ∗
      "Hilog"       ∷ own_replica_ilog_half γ gid rid ilog ∗
      "#Hrpvds"     ∷ ([∗ set] t ∈ dom cpm, is_replica_validated_ts γ gid rid t) ∗
      "#Hfpw"       ∷ ([∗ map] t ↦ ps ∈ psm, fast_proposal_witness γ gid rid t ps) ∗
      "#Hclogalb"   ∷ is_txn_log_lb γ gid cloga ∗
      "%Hdompsmrkm" ∷ ⌜dom psm = dom rkm⌝ ∗
      "%Hcloga"     ∷ ⌜prefix clog cloga⌝ ∗
      "%Hexec"      ∷ ⌜execute_cmds log = LocalState cm histm cpm ptgsm sptsm ptsm psm rkm⌝.

  Definition is_replica (rp : loc) : iProp Σ :=
    ∃ (mu : loc) (txnlog : loc) (idx : loc) (gid rid : u64) γ α,
      "#HmuP"     ∷ readonly (rp ↦[Replica :: "mu"] #mu) ∗
      "#Hlock"    ∷ is_lock tulipNS #mu (own_replica rp gid rid γ α) ∗
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
    key ∈ keys_all ->
    {{{ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__writableKey #rp #ts #(LitString key)
    {{{ (ok : bool), RET #ok;
        own_replica_ptsm_sptsm rp ptsm sptsm ∗
        ⌜if ok then key_writable ptsm sptsm (uint.nat ts) key else True⌝
    }}}.
  Proof.
    iIntros (Hkey Φ) "Hrp HΦ".
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
        clear -Hgespts. word.
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

  Theorem wp_Replica__acquire rp (tsW : u64) pwrsS pwrsL pwrs ptsm sptsm :
    valid_wrs pwrs ->
    let ts := uint.nat tsW in
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs ∗ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__acquire #rp #tsW (to_val pwrsS)
    {{{ (acquired : bool), RET #acquired;
        own_dbmap_in_slice pwrsS pwrsL pwrs ∗
        if acquired
        then own_replica_ptsm_sptsm rp (acquire ts pwrs ptsm) (acquire ts pwrs sptsm) ∗
             ⌜validated_ptsm ptsm pwrs⌝ ∗
             ⌜validated_sptsm sptsm ts pwrs⌝
        else own_replica_ptsm_sptsm rp ptsm sptsm
    }}}.
  Proof.
    iIntros (Hvw ts Φ) "[[HpwrsS %HpwrsL] Hrp] HΦ".
    wp_rec.
    iDestruct (own_replica_ptsm_sptsm_dom with "Hrp") as %[Hdomptsm Hdomsptsm].

    (*@ func (rp *Replica) acquire(ts uint64, pwrs []tulip.WriteEntry) bool {   @*)
    (*@     // Check if all keys are writable.                                  @*)
    (*@     var pos uint64 = 0                                                  @*)
    (*@                                                                         @*)
    wp_apply (wp_ref_to); first by auto.
    iIntros (posP) "HposP".
    wp_pures.

    (*@     for pos < uint64(len(pwrs)) {                                       @*)
    (*@         ent := pwrs[pos]                                                @*)
    (*@         writable := rp.writableKey(ts, ent.Key)                         @*)
    (*@         if !writable {                                                  @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@         pos++                                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iDestruct (own_slice_sz with "HpwrsS") as %Hlen.
    iDestruct (own_slice_small_acc with "HpwrsS") as "[HpwrsS HpwrsC]".
    set P := (λ (cont : bool), ∃ (pos : u64),
      let pwrs' := list_to_map (take (uint.nat pos) pwrsL) in
      "HpwrsS"  ∷ own_slice_small pwrsS (struct.t WriteEntry) (DfracOwn 1) pwrsL ∗
      "HposP"   ∷ posP ↦[uint64T] #pos ∗
      "Hrp"     ∷ own_replica_ptsm_sptsm rp ptsm sptsm ∗
      "%Hptsm"  ∷ ⌜validated_ptsm ptsm pwrs'⌝ ∗
      "%Hsptsm" ∷ ⌜validated_sptsm sptsm ts pwrs'⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [HpwrsS HposP Hrp]"); last first; first 1 last.
    { (* Loop entry. *)
      iExists (W64 0).
      rewrite uint_nat_W64_0 take_0 list_to_map_nil.
      iFrame.
      iPureIntro.
      (* split; first done. *)
      split.
      { rewrite /validated_ptsm dom_empty_L.
        intros k n Hn.
        by apply map_lookup_filter_Some in Hn as [_ ?].
      }
      { rewrite /validated_sptsm dom_empty_L.
        intros k n Hn.
        by apply map_lookup_filter_Some in Hn as [_ ?].
      }
    }
    { (* Loop body. *)
      clear Φ. iIntros (Φ) "!> HP HΦ". iNamed "HP".
      wp_load.
      wp_apply (wp_slice_len).
      wp_if_destruct; last first.
      { (* Exit from the loop condition. *)
        iApply "HΦ".
        iExists pos.
        by iFrame "∗ %".
      }
      wp_load.
      destruct (lookup_lt_is_Some_2 pwrsL (uint.nat pos)) as [[k v] Hwr]; first word.
      wp_apply (wp_SliceGet with "[$HpwrsS]"); first done.
      iIntros "HpwrsL".
      wp_pures.
      wp_apply (wp_Replica__writableKey with "Hrp").
      { rewrite -HpwrsL in Hwr.
        apply elem_of_list_lookup_2, elem_of_map_to_list, elem_of_dom_2 in Hwr.
        clear -Hvw Hwr. set_solver.
      }
      iIntros (ok) "[Hrp %Hwritable]".
      wp_pures.
      destruct ok; wp_pures; last first.
      { iApply "HΦ".
        by iFrame "∗ %".
      }
      wp_load.
      wp_store.
      iApply "HΦ".
      iFrame "∗ %".
      iPureIntro.
      rewrite uint_nat_word_add_S; last word.
      rewrite (take_S_r _ _ _ Hwr) list_to_map_snoc; last first.
      { by eapply map_to_list_not_elem_of_take_key. }
      split.
      { intros x n Hn.
        apply map_lookup_filter_Some in Hn as [Hn Hx].
        rewrite /= dom_insert_L elem_of_union in Hx.
        destruct Hx as [Hx | Hx]; last first.
        { specialize (Hptsm x n). simpl in Hptsm.
          apply Hptsm.
          by apply map_lookup_filter_Some.
        }
        rewrite elem_of_singleton in Hx. subst x.
        destruct Hwritable as [Hwritable _].
        by rewrite /key_writable_ptsm Hn in Hwritable.
      }
      { intros x n Hn.
        apply map_lookup_filter_Some in Hn as [Hn Hx].
        rewrite /= dom_insert_L elem_of_union in Hx.
        destruct Hx as [Hx | Hx]; last first.
        { specialize (Hsptsm x n). simpl in Hsptsm.
          apply Hsptsm.
          by apply map_lookup_filter_Some.
        }
        rewrite elem_of_singleton in Hx. subst x.
        destruct Hwritable as [_ Hwritable].
        by rewrite /key_writable_sptsm Hn in Hwritable.
      }
    }
    iNamed 1. clear P.

    (*@     // Report error if some key cannot be locked.                       @*)
    (*@     if pos < uint64(len(pwrs)) {                                        @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_load.
    wp_apply wp_slice_len.
    wp_if_destruct.
    { iDestruct ("HpwrsC" with "HpwrsS") as "HpwrsS".
      iApply "HΦ".
      by iFrame "∗ %".
    }
    rewrite take_ge in Hptsm, Hsptsm; last word.
    rewrite -HpwrsL list_to_map_to_list in Hptsm, Hsptsm.

    (*@     // Acquire locks for each key.                                      @*)
    (*@     for _, ent := range(pwrs) {                                         @*)
    (*@         rp.acquireKey(ts, ent.Key)                                      @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    set P := (λ (i : u64),
      let pwrs' := list_to_map (take (uint.nat i) pwrsL) in
      own_replica_ptsm_sptsm rp (acquire ts pwrs' ptsm) (acquire ts pwrs' sptsm))%I.
    wp_apply (wp_forSlice P with "[] [$HpwrsS Hrp]"); last first; first 1 last.
    { (* Loop entry. *)
      subst P. simpl.
      by rewrite uint_nat_W64_0 take_0 list_to_map_nil /acquire 2!setts_empty.
    }
    { (* Loop body. *)
      clear Φ.
      iIntros (i [k v]) "!>".
      iIntros (Φ) "(Hrp & %Hbound & %Hi) HΦ".
      subst P. simpl.
      wp_pures.
      wp_apply (wp_Replica__acquireKey with "Hrp").
      iIntros "Hrp".
      iApply "HΦ".
      rewrite uint_nat_word_add_S; last word.
      rewrite (take_S_r _ _ _ Hi) list_to_map_snoc; last first.
      { by eapply map_to_list_not_elem_of_take_key. }
      rewrite /acquire setts_insert; last first.
      { rewrite -HpwrsL in Hi.
        apply elem_of_list_lookup_2, elem_of_map_to_list, elem_of_dom_2 in Hi.
        clear -Hvw Hi Hdomptsm. set_solver.
      }
      rewrite /acquire setts_insert; last first.
      { rewrite -HpwrsL in Hi.
        apply elem_of_list_lookup_2, elem_of_map_to_list, elem_of_dom_2 in Hi.
        clear -Hvw Hi Hdomsptsm. set_solver.
      }
      done.
    }
    iIntros "[HP HpwrsS]".
    iNamed "HP". clear P.
    rewrite -Hlen firstn_all -HpwrsL list_to_map_to_list in Hptsmabs, Hsptsmabs.

    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    wp_pures.
    iDestruct ("HpwrsC" with "HpwrsS") as "HpwrsS".
    iApply "HΦ".
    by iFrame "HptsmP HsptsmP ∗ %".
  Qed.

  Definition finalized_outcome γ ts res : iProp Σ :=
    match res with
    | ReplicaOK => False
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => False
    | ReplicaFailedValidation => False
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  Theorem wp_Replica__finalized rp (tsW : u64) gid rid γ α :
    let ts := uint.nat tsW in
    gid ∈ gids_all ->
    know_tulip_inv γ -∗
    {{{ own_replica rp gid rid γ α }}}
      Replica__finalized #rp #tsW
    {{{ (res : rpres) (ok : bool), RET (#(rpres_to_u64 res), #ok);
        own_replica rp gid rid γ α ∗
        if ok then finalized_outcome γ ts res else True
    }}}.
  Proof.
    iIntros (ts Hgid) "#Hinv".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) finalized(ts uint64) (uint64, bool) {                @*)
    (*@     cmted, done := rp.txntbl[ts]                                        @*)
    (*@     if done {                                                           @*)
    (*@         if cmted {                                                      @*)
    (*@             return tulip.REPLICA_COMMITTED_TXN, true                    @*)
    (*@         } else {                                                        @*)
    (*@             return tulip.REPLICA_ABORTED_TXN, true                      @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp". iNamed "Hcm".
    wp_loadField.
    wp_apply (wp_MapGet with "Htxntbl").
    iIntros (cmted bdone) "[%Hcmted Htxntbl]".
    wp_pures.
    destruct bdone; wp_pures.
    { destruct cmted; wp_pures.
      { iApply ("HΦ" $! ReplicaCommittedTxn).
        (* Open atomic invariant to obtain [is_txn_committed]. *)
        iInv "Hinv" as "> HinvO" "HinvC".
        iAssert (∃ wrs, is_txn_committed γ ts wrs)%I as "#Hcmted".
        { (* First show that [ts] is committed on the replica. *)
          rename cm into cmrp.
          apply map_get_true in Hcmted. symmetry in Hcmabs.
          pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcmabs Hcmted) as (ts' & Hts' & Hcmrpts).
          assert (ts' = ts) as ->.
          { subst ts. rewrite Hts'. lia. }
          (* Next open the group invariant to obtain [is_txn_committed]. *)
          iNamed "HinvO".
          unshelve epose proof (execute_cmds_apply_cmds cloga ilog cmrp histm _) as Happly.
          { by eauto 10. }
          iDestruct (big_sepS_elem_of with "Hgroups") as "Hgroup"; first apply Hgid.
          do 2 iNamed "Hgroup".
          iDestruct (txn_log_prefix with "Hlog Hclogalb") as %Hprefix.
          pose proof (apply_cmds_mono_cm Hprefix Hrsm Happly) as Hcmrp.
          pose proof (lookup_weaken _ _ _ _ Hcmrpts Hcmrp) as Hcmts.
          rewrite Hcm lookup_omap_Some in Hcmts.
          destruct Hcmts as (st & Hstcmted & Hst).
          destruct st; [done | | done].
          by iDestruct (big_sepM_lookup with "Hsafestm") as "Hcmted"; first apply Hst.
        }
        iMod ("HinvC" with "HinvO") as "_".
        by iFrame "∗ # %".
      }
      { iApply ("HΦ" $! ReplicaAbortedTxn).
        (* Open atomic invariant to obtain [is_txn_aborted]. *)
        iInv "Hinv" as "> HinvO" "HinvC".
        iAssert (is_txn_aborted γ ts)%I as "#Habted".
        { (* First show that [ts] is aborted on the replica. *)
          rename cm into cmrp.
          apply map_get_true in Hcmted. symmetry in Hcmabs.
          pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcmabs Hcmted) as (ts' & Hts' & Hcmrpts).
          assert (ts' = ts) as ->.
          { subst ts. rewrite Hts'. lia. }
          (* Next open the group invariant to obtain [is_txn_aborted]. *)
          iNamed "HinvO".
          unshelve epose proof (execute_cmds_apply_cmds cloga ilog cmrp histm _) as Happly.
          { by eauto 10. }
          iDestruct (big_sepS_elem_of with "Hgroups") as "Hgroup"; first apply Hgid.
          do 2 iNamed "Hgroup".
          iDestruct (txn_log_prefix with "Hlog Hclogalb") as %Hprefix.
          pose proof (apply_cmds_mono_cm Hprefix Hrsm Happly) as Hcmrp.
          pose proof (lookup_weaken _ _ _ _ Hcmrpts Hcmrp) as Hcmts.
          rewrite Hcm lookup_omap_Some in Hcmts.
          destruct Hcmts as (st & Hstabted & Hst).
          destruct st; [done | done |].
          by iDestruct (big_sepM_lookup with "Hsafestm") as "Habted"; first apply Hst.
        }
        iMod ("HinvC" with "HinvO") as "_".
        by iFrame "∗ # %".
      }
    }

    (*@     // @tulip.REPLICA_OK is a placeholder.                              @*)
    (*@     return tulip.REPLICA_OK, false                                      @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! ReplicaOK).
    by iFrame "∗ # %".
  Qed.

  Theorem wp_Replica__logValidate rp (ts : u64) (pwrsS : Slice.t) (ptgsS : Slice.t) :
    {{{ True }}}
      Replica__logValidate #rp #ts (to_val pwrsS) (to_val ptgsS)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (rp *Replica) logValidate(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) { @*)
    (*@     // TODO: Create an inconsistent log entry for validating @ts with @pwrs and @ptgs. @*)
    (*@ }                                                                       @*)
  Admitted.

  Definition validate_outcome γ gid rid ts res : iProp Σ :=
    match res with
    | ReplicaOK => is_replica_validated_ts γ gid rid ts
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => False
    | ReplicaFailedValidation => True
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  Theorem wp_Replica__validate
    rp (tsW : u64) pwrsS pwrsL pwrs (ptgsS : Slice.t) gid rid γ α :
    let ts := uint.nat tsW in
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    safe_txn_pwrs γ gid ts pwrs -∗
    know_tulip_inv γ -∗
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs ∗ own_replica rp gid rid γ α }}}
      Replica__validate #rp #tsW (to_val pwrsS) (to_val ptgsS)
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        own_replica rp gid rid γ α ∗ validate_outcome γ gid rid ts res
    }}}.
  Proof.
    iIntros (ts Hgid Hrid) "#Hsafepwrs #Hinv".
    iIntros (Φ) "!> [Hpwrs Hrp] HΦ".
    wp_rec.

    (*@ func (rp *Replica) validate(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) uint64 { @*)
    (*@     // Check if the transaction has aborted or committed. If so, returns the @*)
    (*@     // status immediately.                                              @*)
    (*@     res, final := rp.finalized(ts)                                      @*)
    (*@     if final {                                                          @*)
    (*@         return res                                                      @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__finalized with "Hinv Hrp").
    { apply Hgid. }
    iIntros (res final) "[Hrp Hfinal]".
    wp_pures.
    destruct final; wp_pures.
    { iApply ("HΦ" $! res). iFrame "Hrp". by destruct res. }

    (*@     // Check if the replica has already validated this transaction.     @*)
    (*@     _, validated := rp.prepm[ts]                                        @*)
    (*@     if validated {                                                      @*)
    (*@         return tulip.REPLICA_OK                                         @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp". iNamed "Hcpm".
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdomprepm.
    wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (prepS validated) "[%Hvalidated HprepmS]".
    wp_pures.
    destruct validated; wp_pures.
    { apply map_get_true in Hvalidated.
      iApply ("HΦ" $! ReplicaOK).
      assert (Hin : ts ∈ dom cpm).
      { apply elem_of_dom_2 in Hvalidated.
        rewrite Hdomprepm elem_of_dom in Hvalidated.
        destruct Hvalidated as [b Hb].
        symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hb) as (ts' & Hts' & Hin).
        assert (ts' = ts) as ->.
        { subst ts. rewrite Hts'. lia. }
        by apply elem_of_dom_2 in Hin.
      }
      iDestruct (big_sepS_elem_of with "Hrpvds") as "#Hrpvd"; first apply Hin.
      by iFrame "∗ # %".
    }

    (*@     // Validate timestamps.                                             @*)
    (*@     acquired := rp.acquire(ts, pwrs)                                    @*)
    (*@     if !acquired {                                                      @*)
    (*@         return tulip.REPLICA_FAILED_VALIDATION                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iDestruct (safe_txn_pwrs_dom_pwrs with "Hsafepwrs") as %Hdompwrs.
    wp_apply (wp_Replica__acquire with "[$Hpwrs $Hptsmsptsm]").
    { apply Hdompwrs. }
    iIntros (acquired) "[Hpwrs Hptsmsptsm]".
    wp_pures.
    destruct acquired; wp_pures; last first.
    { iApply ("HΦ" $! ReplicaFailedValidation). by iFrame "∗ # %". }
    iDestruct "Hptsmsptsm" as "(Hptsmsptsm & %Hvptsm & %Hvsptsm)".

    (*@     // Record the write set and the participant groups.                 @*)
    (*@     rp.prepm[ts] = pwrs                                                 @*)
    (*@     // rp.ptgsm[ts] = ptgs                                              @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapInsert with "HprepmS"); first done.
    iIntros "HprepmS".
    
    (*@     // Logical action: Validate(@ts, @pwrs, @ptgs).                     @*)
    (*@     rp.logValidate(ts, pwrs, ptgs)                                      @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__logValidate).
    wp_pures.
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
    (* First catching up the consistent log. *)
    destruct Hcloga as [cmdsa ->].
    iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
      as "(Hclog & Hilog & Hgroup & Hrp)".
    (* Then apply the validate transition. *)
    (* ∅ is a placeholder for participant groups. *)
    iMod (replica_inv_validate _ _ ∅ with "Hsafepwrs Hclog Hilog Hrp")
      as "(Hclog & Hilog & Hrp & #Hvd)".
    { apply Hexec. }
    { do 2 (split; first done).
      apply map_get_false in Hvalidated as [Hnone _].
      symmetry in Hcpmabs.
      rewrite -not_elem_of_dom Hdomprepm not_elem_of_dom in Hnone.
      unshelve epose proof (lookup_kmap_eq_None _ _ _ _ _ Hcpmabs Hnone) as Hcpm.
      apply Hcpm.
      word.
    }
    iDestruct ("HrgC" with "Hrp") as "Hrg".
    iDestruct ("HrgsC" with "Hrg") as "Hrgs".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".

    (*@     return tulip.REPLICA_OK                                             @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! ReplicaOK).
    iDestruct (big_sepM2_insert_2 _ _ _ tsW with "[Hpwrs] Hprepm") as "Hprepm".
    { iFrame "Hpwrs". }
    iAssert ([∗ set] t ∈ dom (<[ts := pwrs]> cpm), is_replica_validated_ts γ gid rid t)%I
      as "Hrpvds'".
    { rewrite dom_insert_L.
      iApply (big_sepS_insert_2 ts with "Hvd Hrpvds").
    }
    iClear "Hrpvds".
    iFrame "∗ # %".
    iModIntro.
    iPureIntro. simpl.
    exists (<[ts := ∅]> ptgsm).
    split.
    { rewrite 2!kmap_insert. f_equal; [word | done]. }
    split; first done.
    rewrite merge_clog_ilog_snoc_ilog; last done.
    by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
  Qed.

  Theorem wp_Replica__accept (rp : loc) (tsW : u64) (rankW : u64) (dec : bool) psm rkm :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    {{{ own_replica_psm_rkm rp psm rkm }}}
      Replica__accept #rp #tsW #rankW #dec
    {{{ RET #(); own_replica_psm_rkm rp (<[ts := (rank, dec)]> psm) (<[ts := S rank]> rkm) }}}.
  Proof.
    iIntros (ts rank Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) accept(ts uint64, rank uint64, dec bool) {           @*)
    (*@     pp := PrepareProposal{                                              @*)
    (*@         rank : rank,                                                    @*)
    (*@         dec  : dec,                                                     @*)
    (*@     }                                                                   @*)
    (*@     rp.pstbl[ts] = pp                                                   @*)
    (*@     rp.rktbl[ts] = std.SumAssumeNoOverflow(rank, 1)                     @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapInsert _ _ (rankW, dec) with "Hpstbl"); first done.
    iIntros "Hpstbl".
    wp_apply wp_SumAssumeNoOverflow.
    iIntros (Hnoof).
    wp_loadField.
    wp_apply (wp_MapInsert with "Hrktbl"); first done.
    iIntros "Hrktbl".
    wp_pures.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    split.
    { rewrite fmap_insert 2!kmap_insert. f_equal; [word | done]. }
    { rewrite fmap_insert 2!kmap_insert. f_equal; [word | word | done]. }
  Qed.

  Theorem wp_Replica__lowestRank rp (tsW : u64) psm rkm :
    let ts := uint.nat tsW in
    {{{ own_replica_psm_rkm rp psm rkm }}}
      Replica__lowestRank #rp #tsW
    {{{ (rank : u64) (ok : bool), RET (#rank, #ok);
        own_replica_psm_rkm rp psm rkm ∗
        ⌜if ok then rkm !! ts = Some (uint.nat rank) else rkm !! ts = None⌝
    }}}.
  Proof.
    iIntros (ts Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) lowestRank(ts uint64) (uint64, bool) {               @*)
    (*@     rank, ok := rp.rktbl[ts]                                            @*)
    (*@     return rank, ok                                                     @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapGet with "Hrktbl").
    iIntros (rankW ok) "[%Hok Hrktbl]".
    wp_pures.
    iApply "HΦ".
    iFrame "∗ %".
    iPureIntro.
    destruct ok.
    { apply map_get_true in Hok.
      assert (Hrktbl : fmap (λ x, uint.nat x) rktbl !! tsW = Some (uint.nat rankW)).
      { by rewrite lookup_fmap Hok. }
      symmetry in Hrkmabs.
      pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hrkmabs Hrktbl) as (ts' & Hts' & Hrkmts).
      assert (ts' = ts) as ->.
      { subst ts. rewrite Hts'. lia. }
      done.
    }
    { apply map_get_false in Hok as [Hnone _].
      assert (Hrktbl : fmap (λ x, uint.nat x) rktbl !! tsW = None).
      { by rewrite lookup_fmap Hnone. }
      symmetry in Hrkmabs.
      apply (lookup_kmap_eq_None _ _ _ _ _ Hrkmabs Hrktbl).
      word.
    }
  Qed.

  Theorem wp_Replica__lastProposal rp (tsW : u64) psm rkm :
    let ts := uint.nat tsW in
    {{{ own_replica_psm_rkm rp psm rkm }}}
      Replica__lastProposal #rp #tsW
    {{{ (rank : u64) (pdec : bool) (ok : bool), RET (#rank, #pdec, #ok);
        own_replica_psm_rkm rp psm rkm ∗
        ⌜if ok then psm !! ts = Some (uint.nat rank, pdec) else psm !! ts = None⌝
    }}}.
  Proof.
    iIntros (ts Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) lastProposal(ts uint64) (uint64, bool, bool) {       @*)
    (*@     ps, ok := rp.pstbl[ts]                                              @*)
    (*@     return ps.rank, ps.dec, ok                                          @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapGet with "Hpstbl").
    iIntros (psl ok) "[%Hok Hpstbl]".
    wp_pures.
    iApply "HΦ".
    iFrame "∗ %".
    iPureIntro.
    destruct ok.
    { apply map_get_true in Hok.
      assert (Hpstbl : fmap ppsl_to_nat_bool pstbl !! tsW = Some (uint.nat psl.1, psl.2)).
      { by rewrite lookup_fmap Hok. }
      symmetry in Hpsmabs.
      pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hpsmabs Hpstbl) as (ts' & Hts' & Hpsmts).
      assert (ts' = ts) as ->.
      { subst ts. rewrite Hts'. lia. }
      done.
    }
    { apply map_get_false in Hok as [Hnone _].
      assert (Hpstbl : fmap ppsl_to_nat_bool pstbl !! tsW = None).
      { by rewrite lookup_fmap Hnone. }
      symmetry in Hpsmabs.
      apply (lookup_kmap_eq_None _ _ _ _ _ Hpsmabs Hpstbl).
      word.
    }
  Qed.

  Definition try_accept_outcome γ gid rid ts rank pdec res : iProp Σ :=
    match res with
    | ReplicaOK => is_replica_pdec_at_rank γ gid rid ts rank pdec
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => True
    | ReplicaFailedValidation => False
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

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

  Theorem wp_Replica__tryAccept rp (tsW : u64) (rankW : u64) (dec : bool) gid rid γ α :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    rank ≠ O ->
    is_group_prepare_proposal γ gid ts rank dec -∗
    know_tulip_inv γ -∗
    {{{ own_replica rp gid rid γ α }}}
      Replica__tryAccept #rp #tsW #rankW #dec
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        own_replica rp gid rid γ α ∗ try_accept_outcome γ gid rid ts rank dec res
    }}}.
  Proof.
    iIntros (ts rank Hgid Hrid Hranknz) "#Hgpsl #Hinv".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) tryAccept(ts uint64, rank uint64, dec bool) uint64 { @*)
    (*@     // Check if the transaction has aborted or committed. If so, returns the @*)
    (*@     // status immediately.                                              @*)
    (*@     res, final := rp.finalized(ts)                                      @*)
    (*@     if final {                                                          @*)
    (*@         return res                                                      @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__finalized with "Hinv Hrp").
    { apply Hgid. }
    iIntros (res final) "[Hrp Hfinal]".
    wp_pures.
    destruct final; wp_pures.
    { iApply ("HΦ" $! res). iFrame "Hrp". by destruct res. }

    (*@     // Check if the coordinator is the most recent one. If not, report the @*)
    (*@     // existence of a more recent coordinator.                          @*)
    (*@     rankl, ok := rp.lowestRank(ts)                                      @*)
    (*@     if ok && rank < rankl {                                             @*)
    (*@         return tulip.REPLICA_STALE_COORDINATOR                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_apply (wp_Replica__lowestRank with "Hpsmrkm").
    iIntros (rankl ok) "[Hpsmrkm %Hok]".
    wp_pures.
    unshelve wp_apply (wp_and_pure (ok = true)).
    { shelve. }
    { apply _. }
    { shelve. }
    { wp_pures. case_bool_decide as Hcase; last apply not_true_is_false in Hcase; by subst ok. }
    { iIntros (_). by wp_pures. }
    case_bool_decide as Hcase; wp_pures.
    { iApply ("HΦ" $! ReplicaStaleCoordinator). by iFrame "∗ # %". }

    (*@     // Update prepare status table to record that @ts is prepared at @rank. @*)
    (*@     rp.accept(ts, rank, dec)                                            @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__accept with "Hpsmrkm").
    iIntros "Hpsmrkm".
    wp_pures.

    (*@     // Logical actions: Execute() and then Accept(@ts, @rank, @dec).    @*)
    (*@     rp.logAccept(ts, rank, dec)                                         @*)
    (*@                                                                         @*)
    wp_apply wp_Replica__logAccept.
    wp_pures.
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
    (* First catching up the consistent log. *)
    destruct Hcloga as [cmdsa ->].
    iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
      as "(Hclog & Hilog & Hgroup & Hrp)".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod (replica_inv_accept ts rank dec with "[Hgpsl] Hclog Hilog Hrp")
      as "(Hclog & Hilog & Hrp & #Hacc)".
    { apply Hexec. }
    { simpl.
      destruct ok; rewrite Hok; last done.
      apply Classical_Prop.not_and_or in Hcase.
      destruct Hcase as [? | Hge]; first done.
      clear -Hge. lia.
    }
    { case_decide as Hrank; [word | done]. }
    iDestruct ("HrgC" with "Hrp") as "Hrg".
    iDestruct ("HrgsC" with "Hrg") as "Hrgs".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".

    (*@     return tulip.REPLICA_OK                                             @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! ReplicaOK).
    iAssert ([∗ map] t ↦ ps ∈ <[ts := (rank, dec)]> psm, fast_proposal_witness γ gid rid t ps)%I
      as "Hfpw'".
    { iApply (big_sepM_insert_2 with "[] Hfpw").
      rewrite /fast_proposal_witness /=.
      case_decide; [word | done].
    }
    iClear "Hfpw".
    iFrame "∗ # %".
    iPureIntro. simpl.
    exists ptgsm.
    split.
    { by rewrite 2!dom_insert_L Hdompsmrkm. }
    split; first done.
    rewrite merge_clog_ilog_snoc_ilog; last done.
    by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
  Qed.

  Theorem wp_Replica__logFastPrepare (rp : loc) (ts : u64) (pwrs : Slice.t) (ptgs : Slice.t) :
    {{{ True }}}
      Replica__logFastPrepare #rp #ts (to_val pwrs) (to_val ptgs)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (rp *Replica) logFastPrepare(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) { @*)
    (*@     // TODO: Create an inconsistent log entry for fast preparing @ts.   @*)
    (*@ }                                                                       @*)
  Admitted.

  Definition fast_prepare_outcome γ gid rid ts res : iProp Σ :=
    match res with
    | ReplicaOK => is_replica_validated_ts γ gid rid ts ∗
                  is_replica_pdec_at_rank γ gid rid ts O true
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => True
    | ReplicaFailedValidation => is_replica_pdec_at_rank γ gid rid ts O false
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  Theorem wp_Replica__fastPrepare
    rp (tsW : u64) pwrsS pwrsL pwrs (ptgsS : Slice.t) gid rid γ α :
    let ts := uint.nat tsW in
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    safe_txn_pwrs γ gid ts pwrs -∗
    know_tulip_inv γ -∗
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs ∗ own_replica rp gid rid γ α }}}
      Replica__fastPrepare #rp #tsW (to_val pwrsS) (to_val ptgsS)
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        own_replica rp gid rid γ α ∗ fast_prepare_outcome γ gid rid ts res
    }}}.
  Proof.
    iIntros (ts Hgid Hrid) "#Hsafepwrs #Hinv".
    iIntros (Φ) "!> [Hpwrs Hrp] HΦ".
    wp_rec.

    (*@ func (rp *Replica) fastPrepare(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) uint64 { @*)
    (*@     // Check if the transaction has aborted or committed. If so, returns the @*)
    (*@     // status immediately.                                              @*)
    (*@     res, final := rp.finalized(ts)                                      @*)
    (*@     if final {                                                          @*)
    (*@         return res                                                      @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__finalized with "Hinv Hrp").
    { apply Hgid. }
    iIntros (res final) "[Hrp Hfinal]".
    wp_pures.
    destruct final; wp_pures.
    { iApply ("HΦ" $! res). iFrame "Hrp". by destruct res. }

    (*@     // Check if the coordinator is the most recent one. If not, report the @*)
    (*@     // existence of a more recent coordinator.                          @*)
    (*@     rank, dec, ok := rp.lastProposal(ts)                                @*)
    (*@     if ok {                                                             @*)
    (*@         if 0 < rank {                                                   @*)
    (*@             // TODO: This would be a performance problem if @pp.rank = 1 (i.e., @*)
    (*@             // txn client's slow-path prepare) since the client would stops its @*)
    (*@             // 2PC on receiving such response. For now the ad-hoc fix is to not @*)
    (*@             // respond to the client in this case, but should figure out a more @*)
    (*@             // efficient design.                                        @*)
    (*@             return tulip.REPLICA_STALE_COORDINATOR                      @*)
    (*@         }                                                               @*)
    (*@         if !dec {                                                       @*)
    (*@             return tulip.REPLICA_FAILED_VALIDATION                      @*)
    (*@         }                                                               @*)
    (*@         return tulip.REPLICA_OK                                         @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_apply (wp_Replica__lastProposal with "Hpsmrkm").
    iIntros (rank dec ok) "[Hpsmrkm %Hok]".
    wp_pures.
    destruct ok; wp_pures.
    { case_bool_decide as Hrank; wp_pures.
      { iApply ("HΦ" $! ReplicaStaleCoordinator). by iFrame "∗ # %". }
      destruct dec; wp_pures; last first.
      { iApply ("HΦ" $! ReplicaFailedValidation).
        iDestruct (big_sepM_lookup with "Hfpw") as "#Hnp".
        { apply Hok. }
        rewrite /fast_proposal_witness.
        assert (Hz : uint.nat rank = O) by word.
        case_decide as Hfast; simpl in Hfast; last word.
        iDestruct "Hnp" as "[Hnp _]".
        by iFrame "∗ # %".
      }
      { iApply ("HΦ" $! ReplicaOK).
        iDestruct (big_sepM_lookup with "Hfpw") as "#Hpv".
        { apply Hok. }
        rewrite /fast_proposal_witness.
        assert (Hz : uint.nat rank = O) by word.
        case_decide as Hfast; simpl in Hfast; last word.
        simpl.
        iDestruct "Hpv" as "[Hprepared Hvalidated]".
        by iFrame "∗ # %".
      }
    }

    (*@     // If the replica has validated this transaction, but no corresponding @*)
    (*@     // prepare proposal entry (as is the case after passing the conditional @*)
    (*@     // above), this means the client has already proceeded to the slow path, and @*)
    (*@     // hence there's nothing more to be done with this fast-prepare.    @*)
    (*@     _, validated := rp.prepm[ts]                                        @*)
    (*@     if validated {                                                      @*)
    (*@         return tulip.REPLICA_STALE_COORDINATOR                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hcpm". wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (prepS validated) "[%Hvalidated HprepmS]".
    wp_pures.
    destruct validated; wp_pures.
    { iApply ("HΦ" $! ReplicaStaleCoordinator). by iFrame "∗ # %". }

    (*@     // Validate timestamps.                                             @*)
    (*@     acquired := rp.acquire(ts, pwrs)                                    @*)
    (*@                                                                         @*)
    iDestruct (safe_txn_pwrs_dom_pwrs with "Hsafepwrs") as %Hdompwrs.
    wp_apply (wp_Replica__acquire with "[$Hpwrs $Hptsmsptsm]").
    { apply Hdompwrs. }
    iIntros (acquired) "[Hpwrs Hptsmsptsm]".

    (*@     // Update prepare status table to record that @ts is prepared or unprepared @*)
    (*@     // at rank 0.                                                       @*)
    (*@     rp.accept(ts, 0, acquired)                                          @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__accept with "Hpsmrkm").
    iIntros "Hpsmrkm".

    (*@     if !acquired {                                                      @*)
    (*@         // Logical actions: Execute() and then Accept(@ts, @0, @false). @*)
    (*@         rp.logAccept(ts, 0, false)                                      @*)
    (*@         return tulip.REPLICA_FAILED_VALIDATION                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_pures.
    destruct acquired; wp_pures; last first.
    { wp_apply wp_Replica__logAccept.
      wp_pures.
      iInv "Hinv" as "> HinvO" "HinvC".
      iNamed "HinvO".
      iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
      iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
      iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
      (* First catching up the consistent log. *)
      destruct Hcloga as [cmdsa ->].
      iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
        as "(Hclog & Hilog & Hgroup & Hrp)".
      iMod (replica_inv_accept ts O false with "[] Hclog Hilog Hrp")
        as "(Hclog & Hilog & Hrp & #Hacc)".
      { apply Hexec. }
      { simpl.
        destruct (rkm !! ts) as [r |] eqn:Hr; last done.
        apply elem_of_dom_2 in Hr.
        by rewrite -not_elem_of_dom Hdompsmrkm in Hok.
      }
      { done. }
      iDestruct ("HrgC" with "Hrp") as "Hrg".
      iDestruct ("HrgsC" with "Hrg") as "Hrgs".
      iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
      iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
      iApply ("HΦ" $! ReplicaFailedValidation).
      iFrame "∗ # %".
      iModIntro.
      iExists ptgsm.
      iSplit.
      { iApply (big_sepM_insert_2 with "[] Hfpw").
        rewrite /fast_proposal_witness /=.
        case_decide; last done.
        iFrame "Hacc".
      }
      iPureIntro.
      split.
      { by rewrite 2!dom_insert_L Hdompsmrkm. }
      split; first done.
      rewrite merge_clog_ilog_snoc_ilog; last done.
      by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
    }
    iDestruct "Hptsmsptsm" as "(Hptsmsptsm & %Hvptsm & %Hvsptsm)".

    (*@     // Record the write set and the participant groups.                 @*)
    (*@     rp.prepm[ts] = pwrs                                                 @*)
    (*@     // rp.ptgsm[ts] = ptgs                                              @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapInsert with "HprepmS"); first done.
    iIntros "HprepmS".

    (*@     // Logical actions: Execute() and then Validate(@ts, @pwrs, @ptgs) and @*)
    (*@     // Accept(@ts, @0, @true).                                          @*)
    (*@     rp.logFastPrepare(ts, pwrs, ptgs)                                   @*)
    (*@                                                                         @*)
    wp_apply wp_Replica__logFastPrepare.
    wp_pures.
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
    (* First catching up the consistent log. *)
    destruct Hcloga as [cmdsa ->].
    iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
      as "(Hclog & Hilog & Hgroup & Hrp)".
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdomprepm.
    iMod (replica_inv_validate _ _ ∅ with "Hsafepwrs Hclog Hilog Hrp")
      as "(Hclog & Hilog & Hrp & #Hvd)".
    { apply Hexec. }
    { do 2 (split; first done).
      apply map_get_false in Hvalidated as [Hnone _].
      symmetry in Hcpmabs.
      rewrite -not_elem_of_dom Hdomprepm not_elem_of_dom in Hnone.
      unshelve epose proof (lookup_kmap_eq_None _ _ _ _ _ Hcpmabs Hnone) as Hcpm.
      apply Hcpm.
      word.
    }
    iMod (replica_inv_accept ts O true with "[] Hclog Hilog Hrp")
      as "(Hclog & Hilog & Hrp & #Hacc)".
    { rewrite merge_clog_ilog_snoc_ilog; last done.
      by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
    }
    { simpl.
      destruct (rkm !! ts) as [r |] eqn:Hr; last done.
      apply elem_of_dom_2 in Hr.
      by rewrite -not_elem_of_dom Hdompsmrkm in Hok.
    }
    { iFrame "Hvd". }
    iDestruct ("HrgC" with "Hrp") as "Hrg".
    iDestruct ("HrgsC" with "Hrg") as "Hrgs".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".

    (*@     return tulip.REPLICA_OK                                             @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! ReplicaOK).
    iDestruct (big_sepM2_insert_2 _ _ _ tsW with "[Hpwrs] Hprepm") as "Hprepm".
    { iFrame "Hpwrs". }
    iAssert ([∗ set] t ∈ dom (<[ts := pwrs]> cpm), is_replica_validated_ts γ gid rid t)%I
      as "Hrpvds'".
    { rewrite dom_insert_L.
      iApply (big_sepS_insert_2 ts with "Hvd Hrpvds").
    }
    iClear "Hrpvds".
    iAssert ([∗ map] t ↦ ps ∈ <[ts := (O, true)]> psm, fast_proposal_witness γ gid rid t ps)%I
      as "Hfpw'".
    { iApply (big_sepM_insert_2 with "[] Hfpw").
      rewrite /fast_proposal_witness /=.
      iFrame "Hvd Hacc".
    }
    iClear "Hfpw".
    iFrame "∗ # %".
    iPureIntro. simpl.
    exists (<[ts := ∅]> ptgsm).
    split.
    { rewrite 2!kmap_insert. f_equal; [word | done]. }
    split.
    { by rewrite 2!dom_insert_L Hdompsmrkm. }
    split; first done.
    do 2 (rewrite merge_clog_ilog_snoc_ilog; last done).
    rewrite /execute_cmds foldl_snoc execute_cmds_unfold.
    by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
  Qed.

End replica.
