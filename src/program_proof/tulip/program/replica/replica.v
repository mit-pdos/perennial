From Perennial.program_proof.tulip.invariance Require Import
  validate execute accept learn local_read.
From Perennial.program_proof Require Import std_proof.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_accept replica_acquire replica_bump_key replica_finalized
  replica_last_proposal replica_lowest_rank replica_readable_key replica_release_key
  replica_writable_key.
From Perennial.program_proof.tulip.program.tuple Require Import tuple.
From Perennial.program_proof.tulip.program.txnlog Require Import txnlog.
From Perennial.program_proof.tulip.program.index Require Import index.

Section replica.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition own_replica_histm (rp : loc) (histm : gmap dbkey dbhist) α : iProp Σ :=
    ([∗ map] k ↦ h ∈ histm, own_phys_hist_half α k h).

  Definition own_replica_with_cloga_no_lsna
    (rp : loc) (cloga : dblog) (gid rid : u64) γ α : iProp Σ :=
    ∃ (cm : gmap nat bool) (histm : gmap dbkey dbhist)
      (cpm : gmap nat dbmap) (ptgsm : gmap nat (gset u64))
      (sptsm ptsm : gmap dbkey nat) (psm : gmap nat (nat * bool)) (rkm : gmap nat nat)
      (clog : dblog) (ilog : list (nat * icommand)),
      let log := merge_clog_ilog cloga ilog in
      "Hcm"         ∷ own_replica_cm rp cm ∗
      "Hhistm"      ∷ own_replica_histm rp histm α ∗
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
      "%Hvcpm"      ∷ ⌜map_Forall (λ _ m, valid_wrs m) cpm⌝ ∗
      "%Hvicmds"    ∷ ⌜Forall (λ nc, (nc.1 <= length cloga)%nat) ilog⌝ ∗
      "%Hexec"      ∷ ⌜execute_cmds log = LocalState cm histm cpm ptgsm sptsm ptsm psm rkm⌝.

  Definition own_replica (rp : loc) (gid rid : u64) γ α : iProp Σ :=
    ∃ (cloga : dblog) (lsna : u64),
      "Hrp"        ∷ own_replica_with_cloga_no_lsna rp cloga gid rid γ α ∗
      "Hlsna"      ∷ rp ↦[Replica :: "lsna"] #lsna ∗
      "%Hlencloga" ∷ ⌜length cloga = uint.nat lsna⌝.

  Definition is_replica_txnlog (rp : loc) gid γ : iProp Σ :=
    ∃ (txnlog : loc),
      "#HtxnlogP" ∷ readonly (rp ↦[Replica :: "txnlog"] #txnlog) ∗
      "#Htxnlog"  ∷ is_txnlog txnlog gid γ.

  Definition is_replica_idx (rp : loc) γ α : iProp Σ :=
    ∃ (idx : loc),
      "#HidxP" ∷ readonly (rp ↦[Replica :: "idx"] #idx) ∗
      "#Hidx"  ∷ is_index idx γ α.

  Definition is_replica (rp : loc) gid rid γ : iProp Σ :=
    ∃ (mu : loc) α,
      "#HmuP"    ∷ readonly (rp ↦[Replica :: "mu"] #mu) ∗
      "#Hlock"   ∷ is_lock tulipNS #mu (own_replica rp gid rid γ α) ∗
      "#Htxnlog" ∷ is_replica_txnlog rp gid γ ∗
      "#Hidx"    ∷ is_replica_idx rp γ α ∗
      "#Hinv"    ∷ know_tulip_inv γ ∗
      "%Hgid"    ∷ ⌜gid ∈ gids_all⌝ ∗
      "%Hrid"    ∷ ⌜rid ∈ rids_all⌝.

  Theorem wp_Replica__logRead (rp : loc) (ts : u64) (key : string) :
    {{{ True }}}
      Replica__logRead #rp #ts #(LitString key)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (rp *Replica) logRead(ts uint64, key string) {                     @*)
    (*@     // TODO: Create an inconsistent log entry for reading @key at @ts.  @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__Read (rp : loc) (tsW : u64) (key : string) gid rid γ :
    let ts := uint.nat tsW in
    ts ≠ O ->
    key ∈ keys_all ->
    key_to_group key = gid ->
    is_replica rp gid rid γ -∗
    {{{ True }}}
      Replica__Read #rp #tsW #(LitString key)
    {{{ (t : u64) (v : dbval) (ok : bool), RET (#t, dbval_to_val v, #ok);
        if ok
        then if decide (uint.nat t = O)
             then is_repl_hist_at γ key (pred ts) v
             else is_repl_hist_at γ key (uint.nat t) v ∗
                  read_promise γ gid rid key (uint.nat t) ts ∗
                  ⌜(uint.nat t < pred ts)⌝
        else True
    }}}.
  Proof.
    iIntros (ts Htsnz Hkey Hkg) "#Hrp".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Read(ts uint64, key string) (uint64, tulip.Value, bool) { @*)
    (*@     tpl := rp.idx.GetTuple(key)                                         @*)
    (*@                                                                         @*)
    iNamed "Hrp". iNamed "Hidx".
    wp_loadField.
    wp_apply (wp_Index__GetTuple with "Hidx"); first apply Hkey.
    iIntros (tpl) "#Htpl".

    (*@     t1, v1 := tpl.ReadVersion(ts)                                       @*)
    (*@                                                                         @*)
    wp_apply (wp_Tuple__ReadVersion_xphys with "Htpl").
    iIntros (t1 v1) "Hread1".
    wp_pures.

    (*@     if t1 == 0 {                                                        @*)
    (*@         // Fast-path read.                                              @*)
    (*@         return 0, v1, true                                              @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Ht1; wp_pures.
    { iApply "HΦ". by case_decide; last inv Ht1. }

    (*@     rp.mu.Lock()                                                        @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hrp]".

    (*@     ok := rp.readableKey(ts, key)                                       @*)
    (*@                                                                         @*)
    do 2 iNamed "Hrp".
    wp_apply (wp_Replica__readableKey with "Hptsmsptsm"); first apply Hkey.
    iIntros (ok) "[Hptsmsptsm %Hreadable]".
    wp_pures.

    (*@     if !ok {                                                            @*)
    (*@         // Trying to read a tuple that is locked by a lower-timestamp   @*)
    (*@         // transaction. This read has to fail because the value to be read is @*)
    (*@         // undetermined---the prepared transaction might or might not commit. @*)
    (*@         rp.mu.Unlock()                                                  @*)
    (*@         return 0, tulip.Value{}, false                                  @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct ok; wp_pures; last first.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗ # %". }
      wp_pures.
      by iApply ("HΦ" $! _ None).
    }

    (*@     t2, v2 := tpl.ReadVersion(ts)                                       @*)
    (*@                                                                         @*)
    assert (is_Some (histm !! key)) as [hist Hhist].
    { unshelve epose proof (execute_cmds_apply_cmds cloga ilog cm histm _) as Happly.
      { by eauto 10. }
      pose proof (apply_cmds_dom _ _ _ Happly) as Hdomhistm.
      by rewrite -elem_of_dom Hdomhistm.
    }
    iDestruct (big_sepM_lookup_acc with "Hhistm") as "[Hhist HhistmC]"; first apply Hhist.
    wp_apply (wp_Tuple__ReadVersion with "Htpl Hhist").
    iIntros (t2 v2) "[Hhist #Hlb]".
    iDestruct ("HhistmC" with "Hhist") as "Hhistm".
    wp_pures.

    (*@     if t2 == 0 {                                                        @*)
    (*@         // Fast-path read.                                              @*)
    (*@         rp.mu.Unlock()                                                  @*)
    (*@         return 0, v2, true                                              @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Ht2; wp_pures.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗ # %". }
      wp_pures.
      iApply "HΦ".
      by case_decide; last inv Ht2.
    }

    (*@     // Slow-path read.                                                  @*)
    (*@     rp.bumpKey(ts, key)                                                 @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__bumpKey with "Hptsmsptsm").
    { clear -Htsnz. word. }
    { apply Hkey. }
    iIntros (spts) "[Hptsmsptsm %Hspts]".

    (*@     // TODO: An optimization is to create a log entry iff the smallest  @*)
    (*@     // preparable timestamp is actually bumped, which can be checked with the @*)
    (*@     // return value of @rp.bumpKey.                                     @*)
    (*@                                                                         @*)
    (*@     // Logical actions: Execute() and then LocalRead(@ts, @key)         @*)
    (*@     rp.logRead(ts, key)                                                 @*)
    (*@                                                                         @*)
    wp_pures.
    wp_apply wp_Replica__logRead.
    iApply fupd_wp.
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
    (* First catching up the consistent log. *)
    destruct Hcloga as [cmdsa ->].
    iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
      as "(Hclog & Hilog & Hgroup & Hrp)".
    iMod (replica_inv_local_read key ts with "Hclog Hilog Hgroup Hrp")
      as "(Hclog & Hilog & Hgroup & Hrp & #Hpromise & #Hrepllb)".
    { apply Hkey. }
    { apply Hkg. }
    { apply Hexec. }
    { simpl.
      rewrite /key_readable in Hreadable.
      destruct (ptsm !! key) as [pts |] eqn:Hpts; rewrite Hpts in Hreadable; last done.
      exists spts, pts.
      do 3 (split; first done).
      clear -Hreadable. word.
    }
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iDestruct ("HrgC" with "Hrp") as "Hrg".
    iDestruct ("HrgsC" with "Hrg") as "Hrgs".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    iModIntro.

    (*@     rp.mu.Unlock()                                                      @*)
    (*@     return t2, v2, true                                                 @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked ∗ # %".
      iPureIntro. simpl.
      exists ptgsm.
      split; first done.
      split.
      { rewrite Forall_forall.
        intros [n c] Hilog. simpl.
        apply elem_of_app in Hilog as [Hilog | Hnewc].
        { rewrite Forall_forall in Hvicmds. by specialize (Hvicmds _ Hilog). }
        rewrite elem_of_list_singleton in Hnewc.
        by inv Hnewc.
      }
      { rewrite merge_clog_ilog_snoc_ilog; last done.
        rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
        erewrite lookup_alter_Some; last apply Hspts.
        f_equal.
      }
    }
    wp_pures.
    iApply "HΦ".
    case_decide as Hnz; first done.
    iDestruct "Hlb" as "[Hlb' %Hv2]".
    clear Ht2.
    destruct Hv2 as (Hv2 & Ht2 & Hlenhist).
    rewrite Ht2.
    iFrame "Hrepllb Hpromise".
    iPureIntro.
    split.
    { by rewrite -last_lookup. }
    { clear -Ht2 Hnz Hlenhist. word. }
  Qed.

  Theorem wp_Replica__multiwrite rp (tsW : u64) pwrsS pwrsL pwrs histm gid γ α :
    let ts := uint.nat tsW in
    let histm' := multiwrite ts pwrs histm in
    valid_pwrs gid pwrs ->
    dom histm = keys_all ->
    safe_extension ts pwrs histm ->
    ([∗ map] k ↦ h ∈ filter_group gid histm', is_repl_hist_lb γ k h) -∗
    is_replica_idx rp γ α -∗
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs ∗ own_replica_histm rp histm α }}}
      Replica__multiwrite #rp #tsW (to_val pwrsS)
    {{{ RET #(); 
        own_dbmap_in_slice pwrsS pwrsL pwrs ∗ own_replica_histm rp histm' α
    }}}.
  Proof.
    iIntros (ts histm' Hvw Hdomhistm Hlenhistm) "#Hrlbs #Hidx".
    iIntros (Φ) "!> [[HpwrsS %Hpwrs] Hhistm] HΦ".
    wp_rec.

    (*@ func (rp *Replica) multiwrite(ts uint64, pwrs []tulip.WriteEntry) {     @*)
    (*@     for _, ent := range pwrs {                                          @*)
    (*@         key := ent.Key                                                  @*)
    (*@         value := ent.Value                                              @*)
    (*@         tpl := rp.idx.GetTuple(key)                                     @*)
    (*@         if value.Present {                                              @*)
    (*@             tpl.AppendVersion(ts, value.Content)                        @*)
    (*@         } else {                                                        @*)
    (*@             tpl.KillVersion(ts)                                         @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iDestruct (own_slice_sz with "HpwrsS") as %Hlenpwrs.
    iDestruct (own_slice_small_acc with "HpwrsS") as "[HpwrsS HpwrsC]".
    set P := (λ (i : u64),
      let pwrs' := list_to_map (take (uint.nat i) pwrsL) in
      own_replica_histm rp (multiwrite ts pwrs' histm) α)%I.
    wp_apply (wp_forSlice P with "[] [$HpwrsS Hhistm]"); last first; first 1 last.
    { (* Loop entry. *)
      subst P. simpl.
      rewrite uint_nat_W64_0 take_0 list_to_map_nil.
      by rewrite multiwrite_empty.
    }
    { (* Loop body. *)
      clear Φ.
      iIntros (i [k v]) "!>".
      iIntros (Φ) "(Hhistm & %Hbound & %Hi) HΦ".
      subst P. simpl.
      iNamed "Hidx".
      wp_loadField.
      (* Prove [k] in the domain of [pwrs] and in [keys_all]. *)
      apply elem_of_list_lookup_2 in Hi as Hpwrsv.
      rewrite -Hpwrs elem_of_map_to_list in Hpwrsv.
      apply elem_of_dom_2 in Hpwrsv as Hdompwrs.
      assert (Hvk : k ∈ keys_all).
      { clear -Hvw Hdompwrs. set_solver. }
      wp_apply (wp_Index__GetTuple with "Hidx"); first apply Hvk.
      iIntros (tpl) "#Htpl".
      (* Obtain proof that the current key [k] has not been written. *)
      pose proof (NoDup_fst_map_to_list pwrs) as Hnd.
      rewrite Hpwrs in Hnd.
      pose proof (list_lookup_fmap fst pwrsL (uint.nat i)) as Hk.
      rewrite Hi /= in Hk.
      pose proof (not_elem_of_take _ _ _ Hnd Hk) as Htake.
      rewrite -fmap_take in Htake.
      apply not_elem_of_list_to_map_1 in Htake as Hnone.
      (* Adjust the goal. *)
      rewrite uint_nat_word_add_S; last by word.
      rewrite (take_S_r _ _ _ Hi) list_to_map_snoc; last done.
      set pwrs' := (list_to_map _) in Hnone *.
      assert (is_Some (histm !! k)) as [h Hh].
      { by rewrite -elem_of_dom Hdomhistm. }
      (* Obtain the length constraint. *)
      rewrite /safe_extension in Hlenhistm.
      set histmwr := filter _ _ in Hlenhistm.
      assert (Hhistmwrk : histmwr !! k = Some h).
      { by apply map_lookup_filter_Some_2. }
      specialize (Hlenhistm _ _ Hhistmwrk). simpl in Hlenhistm.
      (* Obtain the replicated history lb. *)
      assert (Hh' : histm' !! k = Some (last_extend ts h ++ [v])).
      { by rewrite (multiwrite_modified Hpwrsv Hh). }
      iDestruct (big_sepM_lookup _ _ k with "Hrlbs") as "Hrlb".
      { apply map_lookup_filter_Some_2; first apply Hh'. simpl.
        clear -Hdompwrs Hvw. set_solver.
      }
      (* Take the physical history out. *)
      iDestruct (big_sepM_delete with "Hhistm") as "[Hh Hhistm]".
      { rewrite multiwrite_unmodified; [apply Hh | apply Hnone]. }
      destruct v as [s |]; wp_pures.
      { (* Case: [@AppendVersion]. *)
        wp_apply (wp_Tuple__AppendVersion with "Hrlb Htpl Hh").
        { apply Hlenhistm. }
        iIntros "Hh".
        iDestruct (big_sepM_insert_2 with "Hh Hhistm") as "Hhistm".
        rewrite insert_delete_insert /multiwrite.
        erewrite insert_merge_l; last first.
        { by rewrite Hh. }
        iApply "HΦ".
        iFrame "∗ #".
      }
      { (* Case: [@KillVersion]. *)
        wp_apply (wp_Tuple__KillVersion with "Hrlb Htpl Hh").
        { apply Hlenhistm. }
        iIntros "Hh".
        iDestruct (big_sepM_insert_2 with "Hh Hhistm") as "Hhistm".
        rewrite insert_delete_insert /multiwrite.
        erewrite insert_merge_l; last first.
        { by rewrite Hh. }
        iApply "HΦ".
        iFrame "∗ #".
      }
    }
    iIntros "[Hhistm HpwrsS]". subst P. simpl.
    iDestruct ("HpwrsC" with "HpwrsS") as "HpwrsS".
    wp_pures.
    iApply "HΦ".
    rewrite -Hlenpwrs firstn_all -Hpwrs list_to_map_to_list.
    by iFrame.
  Qed.

  Theorem wp_Replica__terminated rp (tsW : u64) cm :
    let ts := uint.nat tsW in
    {{{ own_replica_cm rp cm }}}
      Replica__terminated #rp #tsW
    {{{ RET #(bool_decide (ts ∈ dom cm)); own_replica_cm rp cm }}}.
  Proof.
    iIntros (ts Φ) "Hcm HΦ".
    wp_rec.

    (*@ func (rp *Replica) terminated(ts uint64) bool {                         @*)
    (*@     _, terminated := rp.txntbl[ts]                                      @*)
    (*@     return terminated                                                   @*)
    (*@ }                                                                       @*)
    iNamed "Hcm".
    wp_loadField.
    wp_apply (wp_MapGet with "Htxntbl").
    iIntros (v ok) "[%Hok Htxntbl]".
    wp_pures.
    case_bool_decide as Hts.
    { destruct ok; last first.
      { exfalso.
        apply map_get_false in Hok as [Hnone _].
        apply elem_of_dom in Hts as [b Hb].
        symmetry in Hcmabs.
        pose proof (lookup_kmap_eq_None _ _ _ _ _ Hcmabs Hnone) as Hcontra.
        specialize (Hcontra ts).
        unshelve epose proof (Hcontra _) as Hcmts; first word.
        by rewrite Hb in Hcmts.
      }
      iApply "HΦ". by iFrame "∗ %".
    }
    { destruct ok.
      { exfalso.
        apply map_get_true in Hok.
        apply not_elem_of_dom in Hts.
        pose proof (lookup_kmap_eq_None _ _ _ _ _ Hcmabs Hts) as Hcontra.
        specialize (Hcontra tsW).
        unshelve epose proof (Hcontra _) as Hcmts; first word.
        by rewrite Hok in Hcmts.
      }
      iApply "HΦ". by iFrame "∗ %".
    }
  Qed.

  Theorem wp_Replica__release rp pwrsS pwrsL pwrs ptsm sptsm :
    valid_wrs pwrs ->
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs ∗ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__release #rp (to_val pwrsS)
    {{{ RET #(); 
        own_dbmap_in_slice pwrsS pwrsL pwrs ∗
        own_replica_ptsm_sptsm rp (release pwrs ptsm) sptsm
    }}}.
  Proof.
    iIntros (Hvw Φ) "[[HpwrsS %Hpwrs] Hrp] HΦ".
    wp_rec.
    iDestruct (own_replica_ptsm_sptsm_dom with "Hrp") as %[Hdomptsm Hdomsptsm].

    (*@ func (rp *Replica) release(pwrs []tulip.WriteEntry) {                   @*)
    (*@     for _, ent := range pwrs {                                          @*)
    (*@         key := ent.Key                                                  @*)
    (*@         rp.releaseKey(key)                                              @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iDestruct (own_slice_sz with "HpwrsS") as %Hlenpwrs.
    iDestruct (own_slice_small_acc with "HpwrsS") as "[HpwrsS HpwrsC]".
    set P := (λ (i : u64),
      let pwrs' := list_to_map (take (uint.nat i) pwrsL) in
      own_replica_ptsm_sptsm rp (release pwrs' ptsm) sptsm)%I.
    wp_apply (wp_forSlice P with "[] [$HpwrsS Hrp]"); last first; first 1 last.
    { (* Loop entry. *)
      subst P. simpl.
      rewrite uint_nat_W64_0 take_0 list_to_map_nil.
      by rewrite release_empty.
    }
    { (* Loop body. *)
      clear Φ.
      iIntros (i [k v]) "!>".
      iIntros (Φ) "(Hrp & %Hbound & %Hi) HΦ".
      subst P. simpl.
      wp_pures.
      wp_apply (wp_Replica__releaseKey with "Hrp").
      iIntros "Hrp".
      iApply "HΦ".
      (* Obtain proof that the current key [k] has not been written. *)
      pose proof (NoDup_fst_map_to_list pwrs) as Hnd.
      rewrite Hpwrs in Hnd.
      pose proof (list_lookup_fmap fst pwrsL (uint.nat i)) as Hk.
      rewrite Hi /= in Hk.
      pose proof (not_elem_of_take _ _ _ Hnd Hk) as Htake.
      rewrite -fmap_take in Htake.
      (* Adjust the goal. *)
      rewrite uint_nat_word_add_S; last by word.
      rewrite (take_S_r _ _ _ Hi) list_to_map_snoc; last apply Htake.
      set pwrs' := list_to_map _.
      rewrite /release setts_insert; last first.
      { rewrite -Hpwrs in Hi.
        apply elem_of_list_lookup_2, elem_of_map_to_list, elem_of_dom_2 in Hi.
        clear -Hvw Hi Hdomptsm. set_solver.
      }
      done.
    }
    iIntros "[Hrp HpwrsS]".
    subst P. simpl.
    rewrite -Hlenpwrs firstn_all -Hpwrs list_to_map_to_list.
    iDestruct ("HpwrsC" with "HpwrsS") as "HpwrsS".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_Replica__applyCommit
    rp (tsW : u64) pwrsS pwrsL pwrs cloga gid rid γ α :
    let ts := uint.nat tsW in
    let cloga' := cloga ++ [CmdCommit ts pwrs] in
    valid_pwrs gid pwrs ->
    group_histm_lbs_from_log γ gid cloga' -∗
    is_txn_log_lb γ gid cloga' -∗
    is_replica_idx rp γ α -∗
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs ∗
        own_replica_with_cloga_no_lsna rp cloga gid rid γ α
    }}}
      Replica__applyCommit #rp #tsW (to_val pwrsS)
    {{{ RET #(); 
        own_dbmap_in_slice pwrsS pwrsL pwrs ∗ 
        own_replica_with_cloga_no_lsna rp cloga' gid rid γ α
    }}}.
  Proof.
    iIntros (ts cloga' Hvpwrs) "#Hhistmlb #Hlb' #Hidx".
    iIntros (Φ) "!> [Hpwrs Hrp] HΦ".
    wp_rec.
    (* First establish that applying this commit results does not get stuck. *)
    rewrite /group_histm_lbs_from_log.
    destruct (apply_cmds cloga') as [cm' histm' |] eqn:Happly'; last done.
    (* Also establish connection between executing entire log vs. consistent log. *)
    iNamed "Hrp".
    unshelve epose proof (execute_cmds_apply_cmds cloga ilog cm histm _) as Happly.
    { by eauto 10. }

    (*@ func (rp *Replica) applyCommit(ts uint64, pwrs []tulip.WriteEntry) {    @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be committed. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     committed := rp.terminated(ts)                                      @*)
    (*@     if committed {                                                      @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__terminated with "Hcm").
    iIntros "Hcm".
    case_bool_decide as Hterm; wp_pures.
    { iApply "HΦ".
      apply elem_of_dom in Hterm as [b Hb].
      iFrame "∗ # %".
      iPureIntro. simpl.
      exists ptgsm.
      split.
      { by apply prefix_app_r. }
      rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
      split.
      { eapply Forall_impl; first apply Hvicmds. simpl.
        intros nc Hnc.
        rewrite length_app /=.
        clear -Hnc. lia.
      }
      rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hb.
      destruct b; first done.
      by rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold /apply_commit Happly Hb in Happly'.
    }
    apply not_elem_of_dom in Hterm.
    rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold Happly /= Hterm in Happly'.
    case_decide as Hsafeext; last done.
    symmetry in Happly'. inv Happly'.

    (*@     rp.multiwrite(ts, pwrs)                                             @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__multiwrite with "Hhistmlb Hidx [$Hpwrs $Hhistm]").
    { apply Hvpwrs. }
    { by eapply apply_cmds_dom. }
    { apply Hsafeext. }
    iIntros "[Hpwrs Hhistm]".

    (*@     rp.txntbl[ts] = true                                                @*)
    (*@                                                                         @*)
    iNamed "Hcm".
    wp_loadField.
    wp_apply (wp_MapInsert with "Htxntbl"); first done.
    iIntros "Htxntbl".

    (*@     // With PCR, a replica might receive a commit even if it is not prepared on @*)
    (*@     // this replica.                                                    @*)
    (*@     _, prepared := rp.prepm[ts]                                         @*)
    (*@                                                                         @*)
    iNamed "Hcpm".
    wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (prepS prepared) "[%Hprepared HprepmS]".
    wp_pures.

    (*@     if prepared {                                                       @*)
    (*@         rp.release(pwrs)                                                @*)
    (*@         delete(rp.prepm, ts)                                            @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    destruct prepared; wp_pures.
    { wp_apply (wp_Replica__release with "[$Hpwrs $Hptsmsptsm]").
      { clear -Hvpwrs. set_solver. }
      iIntros "[Hpwrs Hptsmsptsm]".
      wp_loadField.
      wp_apply (wp_MapDelete with "HprepmS").
      iIntros "HprepmS".
      wp_pures.
      iApply "HΦ".
      apply map_get_true in Hprepared.
      iDestruct (big_sepM2_delete_l with "Hprepm") as (m) "(%Hm & _ & Hprepm)".
      { apply Hprepared. }
      iAssert ([∗ set] t ∈ dom (delete ts cpm), is_replica_validated_ts γ gid rid t)%I
        as "#Hrpvds'".
      { rewrite dom_delete_L.
        iDestruct (big_sepS_delete _ _ ts with "Hrpvds") as "[_ ?]"; last done.
        symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hm) as (ts' & Hts' & Hcpmts).
        assert (ts' = ts) as -> by word.
        by apply elem_of_dom.
      }
      iClear "Hrpvds".
      iFrame "∗ # %".
      iPureIntro. simpl.
      exists (<[ts := true]> cm), (delete ts ptgsm).
      split.
      { rewrite 2!kmap_insert. f_equal; [word | done]. }
      split.
      { rewrite 2!kmap_delete. f_equal; [word | done]. }
      split.
      { by apply prefix_app_r. }
      { rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
        split.
        { by apply map_Forall_delete. }
        split.
        { eapply Forall_impl; first apply Hvicmds. simpl.
          intros nc Hnc.
          rewrite length_app /=.
          clear -Hnc. lia.
        }
        symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hm) as (ts' & Hts' & Hcpmts).
        assert (ts' = ts) as -> by word.
        by rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hterm Hcpmts.
      }
    }
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdomprepm.
    iApply "HΦ".
    iFrame "∗ # %".
    iPureIntro. simpl.
    exists (<[ts := true]> cm), ptgsm.
    split.
    { rewrite 2!kmap_insert. f_equal; [word | done]. }
    split.
    { by apply prefix_app_r. }
    { rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
      split.
      { eapply Forall_impl; first apply Hvicmds. simpl.
        intros nc Hnc.
        rewrite length_app /=.
        clear -Hnc. lia.
      }
      apply map_get_false in Hprepared as [Hnone _].
      rewrite -not_elem_of_dom Hdomprepm not_elem_of_dom in Hnone.
      symmetry in Hcpmabs.
      pose proof (lookup_kmap_eq_None _ _ _ _ _  Hcpmabs Hnone) as Hcpmnone.
      specialize (Hcpmnone ts).
      unshelve epose proof (Hcpmnone _) as Hcpmts; first word.
      by rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hterm Hcpmts.
    }
  Qed.

  Theorem wp_Replica__applyAbort rp (tsW : u64) cloga gid rid γ α :
    let ts := uint.nat tsW in
    let cloga' := cloga ++ [CmdAbort ts] in
    not_stuck (apply_cmds cloga') ->
    is_txn_log_lb γ gid cloga' -∗
    {{{ own_replica_with_cloga_no_lsna rp cloga gid rid γ α }}}
      Replica__applyAbort #rp #tsW
    {{{ RET #(); own_replica_with_cloga_no_lsna rp cloga' gid rid γ α }}}.
  Proof.
    iIntros (ts cloga' Hns) "#Hlb'".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.
    (* First establish that applying this commit results does not get stuck. *)
    destruct (apply_cmds cloga') as [cm' histm' |] eqn:Happly'; last done.
    (* Also establish connection between executing entire log vs. consistent log. *)
    iNamed "Hrp".
    unshelve epose proof (execute_cmds_apply_cmds cloga ilog cm histm _) as Happly.
    { by eauto 10. }

    (*@ func (rp *Replica) applyAbort(ts uint64) {                              @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be aborted. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     aborted := rp.terminated(ts)                                        @*)
    (*@     if aborted {                                                        @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__terminated with "Hcm").
    iIntros "Hcm".
    case_bool_decide as Hterm; wp_pures.
    { iApply "HΦ".
      apply elem_of_dom in Hterm as [b Hb].
      iFrame "∗ # %".
      iPureIntro. simpl.
      exists ptgsm.
      split.
      { by apply prefix_app_r. }
      rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
      split.
      { eapply Forall_impl; first apply Hvicmds. simpl.
        intros nc Hnc.
        rewrite length_app /=.
        clear -Hnc. lia.
      }
      rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hb.
      destruct b; last done.
      by rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold /apply_abort Happly Hb in Happly'.
    }
    apply not_elem_of_dom in Hterm.
    (* rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold Happly /= Hterm in Happly'. *)
    (* symmetry in Happly'. inv Happly'. *)

    (*@     rp.txntbl[ts] = false                                               @*)
    (*@                                                                         @*)
    iNamed "Hcm".
    wp_loadField.
    wp_apply (wp_MapInsert with "Htxntbl"); first done.
    iIntros "Htxntbl".

    (*@     // Tuples lock are held iff @prepm[ts] contains something (and so we should @*)
    (*@     // release them by calling @abort).                                 @*)
    (*@     pwrs, prepared := rp.prepm[ts]                                      @*)
    (*@                                                                         @*)
    iNamed "Hcpm".
    wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (prepS prepared) "[%Hprepared HprepmS]".
    wp_pures.

    (*@     if prepared {                                                       @*)
    (*@         rp.release(pwrs)                                                @*)
    (*@         delete(rp.prepm, ts)                                            @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdomprepm.
    destruct prepared; wp_pures.
    { apply map_get_true in Hprepared.
      assert (is_Some (prepm !! tsW)) as [pwrs Hpwrs].
      { by rewrite -elem_of_dom -Hdomprepm elem_of_dom. }
      iDestruct (big_sepM2_delete with "Hprepm") as "[Hpwrs Hprepm]".
      { apply Hprepared. }
      { apply Hpwrs. }
      iDestruct "Hpwrs" as (pwrsL) "Hpwrs".
      wp_apply (wp_Replica__release with "[$Hpwrs $Hptsmsptsm]").
      { symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hpwrs) as (ts' & Hts' & Hcpmts).
        assert (ts' = ts) as -> by word.
        by specialize (Hvcpm _ _ Hcpmts).
      }
      iIntros "[Hpwrs Hptsmsptsm]".
      wp_loadField.
      wp_apply (wp_MapDelete with "HprepmS").
      iIntros "HprepmS".
      wp_pures.
      iApply "HΦ".
      iAssert ([∗ set] t ∈ dom (delete ts cpm), is_replica_validated_ts γ gid rid t)%I
        as "#Hrpvds'".
      { rewrite dom_delete_L.
        iDestruct (big_sepS_delete _ _ ts with "Hrpvds") as "[_ ?]"; last done.
        symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hpwrs) as (ts' & Hts' & Hcpmts).
        assert (ts' = ts) as -> by word.
        by apply elem_of_dom.
      }
      iClear "Hrpvds".
      iFrame "∗ # %".
      iPureIntro. simpl.
      exists (<[ts := false]> cm), (delete ts ptgsm).
      split.
      { rewrite 2!kmap_insert. f_equal; [word | done]. }
      split.
      { rewrite 2!kmap_delete. f_equal; [word | done]. }
      split.
      { by apply prefix_app_r. }
      { rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
        split.
        { by apply map_Forall_delete. }
        split.
        { eapply Forall_impl; first apply Hvicmds. simpl.
          intros nc Hnc.
          rewrite length_app /=.
          clear -Hnc. lia.
        }
        symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hpwrs) as (ts' & Hts' & Hcpmts).
        assert (ts' = ts) as -> by word.
        by rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hterm Hcpmts.
      }
    }
    iApply "HΦ".
    iFrame "∗ # %".
    iPureIntro. simpl.
    exists (<[ts := false]> cm), ptgsm.
    split.
    { rewrite 2!kmap_insert. f_equal; [word | done]. }
    split.
    { by apply prefix_app_r. }
    { rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
      split.
      { eapply Forall_impl; first apply Hvicmds. simpl.
        intros nc Hnc.
        rewrite length_app /=.
        clear -Hnc. lia.
      }
      apply map_get_false in Hprepared as [Hnone _].
      rewrite -not_elem_of_dom Hdomprepm not_elem_of_dom in Hnone.
      symmetry in Hcpmabs.
      pose proof (lookup_kmap_eq_None _ _ _ _ _  Hcpmabs Hnone) as Hcpmnone.
      specialize (Hcpmnone ts).
      unshelve epose proof (Hcpmnone _) as Hcpmts; first word.
      by rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hterm Hcpmts.
    }
  Qed.

  Theorem wp_Replica__apply
    rp cmd pwrsS cloga gid rid γ α :
    let cloga' := cloga ++ [cmd] in
    valid_ccommand gid cmd ->
    group_histm_lbs_from_log γ gid cloga' -∗
    is_txn_log_lb γ gid cloga' -∗
    is_replica_idx rp γ α -∗
    {{{ own_pwrs_slice pwrsS cmd ∗
        own_replica_with_cloga_no_lsna rp cloga gid rid γ α
    }}}
      Replica__apply #rp (ccommand_to_val pwrsS cmd)
    {{{ RET #();
        own_pwrs_slice pwrsS cmd ∗ 
        own_replica_with_cloga_no_lsna rp cloga' gid rid γ α
    }}}.
  Proof.
    iIntros (cloga' Hvcmd) "#Hsafe #Hlb' #Hidx".
    iIntros (Φ) "!> [Hpwrs Hrp] HΦ".
    wp_rec.

    (*@ func (rp *Replica) apply(cmd txnlog.Cmd) {                              @*)
    (*@     if cmd.Kind == 1 {                                                  @*)
    (*@         rp.applyCommit(cmd.Timestamp, cmd.PartialWrites)                @*)
    (*@     } else if cmd.Kind == 2 {                                           @*)
    (*@         rp.applyAbort(cmd.Timestamp)                                    @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_pures.
    destruct cmd eqn:Hcmd; wp_pures.
    { (* Case: CmdCommit. *)
      destruct Hvcmd as [Hvts Hvpwrs].
      iDestruct "Hpwrs" as (pwrsL) "Hpwrs".
      wp_apply (wp_Replica__applyCommit with "[Hsafe] [Hlb'] Hidx [$Hpwrs $Hrp]").
      { apply Hvpwrs. }
      { rewrite uint_nat_W64_of_nat; first done. rewrite /valid_ts in Hvts. word. }
      { rewrite uint_nat_W64_of_nat; first done. rewrite /valid_ts in Hvts. word. }
      iIntros "[Hpwrs Hrp]".
      wp_pures.
      iApply "HΦ".
      rewrite uint_nat_W64_of_nat; last first.
      { rewrite /valid_ts in Hvts. word. }
      by iFrame.
    }
    { (* Case: CmdAbort. *)
      simpl in Hvcmd.
      rewrite /group_histm_lbs_from_log.
      destruct (apply_cmds cloga') as [cpm histm |] eqn:Happly; last done.
      wp_apply (wp_Replica__applyAbort with "[Hlb'] Hrp").
      { rewrite uint_nat_W64_of_nat; first by rewrite Happly. rewrite /valid_ts in Hvcmd. word. }
      { rewrite uint_nat_W64_of_nat; first done. rewrite /valid_ts in Hvcmd. word. }
      iIntros "Hrp".
      wp_pures.
      iApply "HΦ".
      rewrite uint_nat_W64_of_nat; last first.
      { rewrite /valid_ts in Hvcmd. word. }
      by iFrame.
    }
  Qed.

  Theorem wp_Replica__Start rp gid rid γ :
    is_replica rp gid rid γ -∗
    {{{ True }}}
      Replica__Start #rp
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hrp" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Start() {                                            @*)
    (*@     rp.mu.Lock()                                                        @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hrp]".
    wp_pures.

    (*@     for {                                                               @*)
    (*@         // TODO: a more efficient interface would return multiple safe commands @*)
    (*@         // at once (so as to reduce the frequency of acquiring Paxos mutex). @*)
    (*@         // Ghost action: Learn a list of new commands.                  @*)
    (*@         cmd, ok := rp.txnlog.Lookup(rp.lsna)                            @*)
    (*@                                                                         @*)
    set P := (λ b : bool, own_replica rp gid rid γ α ∗ locked #mu)%I.
    wp_apply (wp_forBreak P with "[] [$Hrp $Hlocked]"); last first.
    { (* Get out of an infinite loop. *)
      iIntros "Hrp". wp_pures. by iApply "HΦ".
    }
    clear Φ. iIntros "!>" (Φ) "[Hrp Hlocked] HΦ".
    wp_rec.
    do 2 iNamed "Hrp".
    wp_loadField.

    (*@         cmd, ok := rp.txnlog.Lookup(lsn)                                @*)
    (*@                                                                         @*)
    iNamed "Htxnlog".
    wp_loadField.
    wp_apply (wp_TxnLog__Lookup with "Htxnlog").
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    (* Take the required group invariant. *)
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    (* Separate out the ownership of the Paxos log from others. *)
    iDestruct (group_inv_extract_log_expose_cpool with "Hgroup") as (paxos cpool) "[Hpaxos Hgroup]".
    (* Obtain validity of command input on cpool. *)
    iDestruct (group_inv_impl_valid_ccommand_cpool with "[Hgroup Hpaxos]") as %Hvcmds.
    { iNamed "Hgroup". iFrame. }
    (* Obtain a lower bound before passing it to Paxos. *)
    iDestruct (txn_log_witness with "Hpaxos") as "#Hlb".
    iExists paxos. iFrame.
    iIntros (paxos') "Hpaxos".
    (* Obtain prefix between the old and new logs. *)
    iDestruct (txn_log_prefix with "Hpaxos Hlb") as %Hpaxos.
    destruct Hpaxos as [cmds Hpaxos].
    (* Obtain inclusion between the command pool and the log. *)
    iAssert (⌜cpool_subsume_log cpool paxos'⌝)%I as %Hincl.
    { iNamed "Hgroup".
      by iDestruct (txn_log_cpool_incl with "Hpaxos Hcpool") as %?.
    }
    (* Transfer validity of command input on cpool to log; used when executing @apply. *)
    pose proof (set_Forall_Forall_subsume _ _ _ Hvcmds Hincl) as Hvc.
    (* Obtain prefix between the applied log and the new log; needed later. *)
    iDestruct (txn_log_prefix with "Hpaxos Hclogalb") as %Hloga.
    (* Obtain a witness of the new log; needed later. *)
    iDestruct (txn_log_witness with "Hpaxos") as "#Hlbnew".
    subst paxos'.

    (*@         // Ghost action: Learn a list of new commands.                  @*)
    (*@                                                                         @*)
    iMod (group_inv_learn with "Htxnsys Hkeys Hgroup") as "(Htxnsys & Hkeys & Hgroup)".
    { apply Hincl. }
    iDestruct (group_inv_merge_log_hide_cpool with "Hpaxos Hgroup") as "Hgroup".
    (* Put back the group invariant. *)
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    (* Close the entire invariant. *)
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    iIntros "!>" (cmd ok pwrsS) "[HpwrsS  %Hcmd]".
    wp_pures.

    (*@         if !ok {                                                        @*)
    (*@             // Sleep for 1 ms.                                          @*)
    (*@             rp.mu.Unlock()                                              @*)
    (*@             primitive.Sleep(1 * 1000000)                                @*)
    (*@             rp.mu.Lock()                                                @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    destruct ok; wp_pures; last first.
    { (* Have applied all the commands known to be committed. *)
      wp_loadField.
      iClear "Hlb Hlbnew".
      wp_apply (wp_Mutex__Unlock with "[-HΦ $Hlock $Hlocked]"); first by iFrame "∗ # %".
      wp_apply wp_Sleep.
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hrp]".
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
    (* Obtain a witness for the newly applied log. *)
    iClear "Hlb".
    (* Prove the newly applied log is a prefix of the new log. *)
    assert (Hprefix : prefix (cloga ++ [cmd]) (paxos ++ cmds)).
    { clear -Hloga Hcmd Hlencloga.
      destruct Hloga as [l Hl].
      rewrite Hl.
      apply prefix_app, prefix_singleton.
      rewrite Hl lookup_app_r in Hcmd; last lia.
      by rewrite Hlencloga /= Nat.sub_diag in Hcmd.
    }
    iDestruct (txn_log_lb_weaken (cloga ++ [cmd]) with "Hlbnew") as "#Hlb"; first apply Hprefix.
    (* Obtain lbs of replicated history over the new history map. *)
    iApply fupd_wp.
    iInv "Hinv" as "> HinvO" "HinvC".
    (* Take the required group invariant. *)
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    iDestruct (group_inv_witness_group_histm_lbs_from_log with "Hlb Hgroup") as "#Hhistmlb".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    iModIntro.

    (*@         rp.apply(cmd)                                                   @*)
    (*@                                                                         @*)
    iAssert (own_replica_with_cloga_no_lsna rp cloga gid rid γ α)%I
      with "[Hcm Hhistm Hcpm Hptsmsptsm Hpsmrkm Hclog Hilog]" as "Hrp".
    { iFrame "∗ # %". }
    wp_apply (wp_Replica__apply with "Hhistmlb Hlb Hidx [$HpwrsS $Hrp]").
    { rewrite Forall_forall in Hvc.
      apply Hvc.
      by apply elem_of_list_lookup_2 in Hcmd.
    }
    iIntros "[HpwrsS Hrp]".


    (*@         rp.lsna = std.SumAssumeNoOverflow(rp.lsna, 1)                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply wp_SumAssumeNoOverflow.
    iIntros (Hnoof).
    wp_storeField.

    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame.
    iPureIntro.
    rewrite uint_nat_word_add_S; last word.
    rewrite length_app /= Hlencloga.
    lia.
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
    do 2 iNamed "Hrp". iNamed "Hcm".
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
          destruct Hcmts as (status & Hstcmted & Hstatus).
          destruct status; [done | | done].
          by iDestruct (big_sepM_lookup with "Hsafestm") as "Hcmted"; first apply Hstatus.
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
          destruct Hcmts as (status & Hstabted & Hstatus).
          destruct status; [done | done |].
          by iDestruct (big_sepM_lookup with "Hsafestm") as "Habted"; first apply Hstatus.
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
    do 2 iNamed "Hrp". iNamed "Hcpm".
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
    iDestruct (safe_txn_pwrs_impl_valid_wrs with "Hsafepwrs") as %Hvw.
    iFrame "∗ # %".
    iModIntro.
    iPureIntro. simpl.
    exists (<[ts := ∅]> ptgsm).
    split.
    { rewrite 2!kmap_insert. f_equal; [word | done]. }
    split; first done.
    rewrite merge_clog_ilog_snoc_ilog; last done.
    split.
    { by apply map_Forall_insert_2. }
    split.
    { rewrite Forall_forall.
      intros [n c] Hilog. simpl.
      apply elem_of_app in Hilog as [Hilog | Hnewc].
      { rewrite Forall_forall in Hvicmds. by specialize (Hvicmds _ Hilog). }
      rewrite elem_of_list_singleton in Hnewc.
      by inv Hnewc.
    }
    { by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=. }
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
    do 2 iNamed "Hrp".
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
    { rewrite /accept_requirement.
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
    split.
    { rewrite Forall_forall.
      intros [n c] Hilog. simpl.
      apply elem_of_app in Hilog as [Hilog | Hnewc].
      { rewrite Forall_forall in Hvicmds. by specialize (Hvicmds _ Hilog). }
      rewrite elem_of_list_singleton in Hnewc.
      by inv Hnewc.
    }
    { by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=. }
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
    do 2 iNamed "Hrp".
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
      { rewrite /accept_requirement.
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
      split.
      { rewrite Forall_forall.
        intros [n c] Hilog. simpl.
        apply elem_of_app in Hilog as [Hilog | Hnewc].
        { rewrite Forall_forall in Hvicmds. by specialize (Hvicmds _ Hilog). }
        rewrite elem_of_list_singleton in Hnewc.
        by inv Hnewc.
      }
      { by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=. }
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
    { rewrite /accept_requirement.
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
    iDestruct (safe_txn_pwrs_impl_valid_wrs with "Hsafepwrs") as %Hvw.
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
    split.
    { by apply map_Forall_insert_2. }
    split.
    { rewrite Forall_forall.
      intros [n c] Hilog. simpl.
      apply elem_of_app in Hilog as [Hilog | Hnewc].
      { apply elem_of_app in Hilog as [Hilog | Hnewc].
        { rewrite Forall_forall in Hvicmds. by specialize (Hvicmds _ Hilog). }
        rewrite elem_of_list_singleton in Hnewc.
        by inv Hnewc.
      }
      rewrite elem_of_list_singleton in Hnewc.
      by inv Hnewc.
    }
    { by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=. }
  Qed.

End replica.
