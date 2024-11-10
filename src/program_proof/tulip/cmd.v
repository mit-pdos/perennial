From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import
  extend nonexpanding_merge.
From Perennial.program_proof.tulip Require Import base stability.

Section validate.
  Definition validate_key (tid : nat) (ov : option dbval) (ovl : option (list bool)) :=
    match ov, ovl with
    | Some _, Some vl => Some (extend tid false vl ++ [true])
    | None, Some _ => ovl
    | _, _ => None
    end.

  Lemma validate_key_nonexpanding ts :
    mergef_nonexpanding (validate_key ts).
  Proof. intros ov ovl. by destruct ov, ovl. Qed.

  Definition validate (tid : nat) (wrs : dbmap) (kvdm : gmap dbkey (list bool)) :=
    merge (validate_key tid) wrs kvdm.

  Lemma validate_dom {tid wrs kvdm} :
    dom (validate tid wrs kvdm) = dom kvdm.
  Proof.
    apply gmap_nonexpanding_merge_dom, validate_key_nonexpanding.
  Qed.

  Lemma validate_unmodified {tid wrs kvdm key} :
    wrs !! key = None ->
    (validate tid wrs kvdm) !! key = kvdm !! key.
  Proof.
    intros Hnone.
    rewrite /validate lookup_merge Hnone /=.
    by destruct (kvdm !! key).
  Qed.

  Lemma validate_modified {tid wrs kvdm key vl} :
    key ∈ dom wrs ->
    kvdm !! key = Some vl ->
    (validate tid wrs kvdm) !! key = Some (extend tid false vl ++ [true]).
  Proof.
    intros Hdomwrs Hvl.
    apply elem_of_dom in Hdomwrs as [v Hv].
    by rewrite /validate lookup_merge Hv Hvl /=.
  Qed.

End validate.

Section setts.
  Definition setts_key (tid : nat) (wr : option dbval) (ots : option nat) :=
    match wr, ots with
    | None, Some ts => Some ts
    | Some _, Some _ => Some tid
    | _, _ => None
    end.

  Lemma setts_key_nonexpanding ts :
    mergef_nonexpanding (setts_key ts).
  Proof. intros x y. by destruct x, y as [t |]. Qed.

  Definition setts (tid : nat) (wrs : dbmap) (tpls : gmap dbkey nat) :=
    merge (setts_key tid) wrs tpls.

  Lemma setts_dom {tid wrs tss} :
    dom (setts tid wrs tss) = dom tss.
  Proof.
    apply gmap_nonexpanding_merge_dom, setts_key_nonexpanding.
  Qed.

  Lemma setts_unmodified {tid wrs tss key} :
    wrs !! key = None ->
    (setts tid wrs tss) !! key = tss !! key.
  Proof.
    intros Hnone.
    rewrite /setts lookup_merge Hnone /=.
    by destruct (tss !! key).
  Qed.

  Lemma setts_modified {tid wrs tsm key} :
    key ∈ dom wrs ->
    key ∈ dom tsm ->
    (setts tid wrs tsm) !! key = Some tid.
  Proof.
    intros Hdomwrs Hdomtsm.
    apply elem_of_dom in Hdomwrs as [v Hv].
    apply elem_of_dom in Hdomtsm as [ts Hts].
    by rewrite /setts lookup_merge Hv Hts /=.
  Qed.

  Lemma setts_difference_distr {tid wrs tss tssd} :
    setts tid wrs (tss ∖ tssd) =
    setts tid wrs tss ∖ setts tid wrs tssd.
  Proof. apply gmap_nonexpanding_merge_difference_distr, setts_key_nonexpanding. Qed.
  
  Lemma setts_mono tid wrs tss1 tss2 :
    tss1 ⊆ tss2 ->
    setts tid wrs tss1 ⊆ setts tid wrs tss2.
  Proof. apply gmap_nonexpanding_merge_mono, setts_key_nonexpanding. Qed.
  
  Lemma setts_filter_group_commute tid wrs tss gid :
    setts tid wrs (filter_group gid tss) = filter_group gid (setts tid wrs tss).
  Proof.
    set P := (λ x, key_to_group x = gid).
    pose proof (setts_key_nonexpanding tid) as Hne.
    by apply (gmap_nonexpanding_merge_filter_commute P wrs tss) in Hne.
  Qed.

  Lemma setts_empty tid tss :
    setts tid ∅ tss = tss.
  Proof.
    apply map_eq. intros k.
    rewrite lookup_merge lookup_empty /=.
    by destruct (tss !! k).
  Qed.
End setts.

Definition acquire := setts.

Section release.
  Definition release wrs tpls := setts O wrs tpls.

  Lemma release_dom {wrs tss} :
    dom (release wrs tss) = dom tss.
  Proof.
    apply gmap_nonexpanding_merge_dom, setts_key_nonexpanding.
  Qed.

  Lemma release_unmodified {wrs tss key} :
    wrs !! key = None ->
    (release wrs tss) !! key = tss !! key.
  Proof.
    intros Hnone.
    rewrite /release lookup_merge Hnone /=.
    by destruct (tss !! key).
  Qed.

  Lemma release_modified {wrs tsm key} :
    key ∈ dom wrs ->
    key ∈ dom tsm ->
    (release wrs tsm) !! key = Some O.
  Proof.
    intros Hdomwrs Hdomtsm.
    apply elem_of_dom in Hdomwrs as [v Hv].
    apply elem_of_dom in Hdomtsm as [ts Hts].
    by rewrite /release lookup_merge Hv Hts /=.
  Qed.

  Lemma release_difference_distr {wrs tss tssd} :
    release wrs (tss ∖ tssd) =
    release wrs tss ∖ release wrs tssd.
  Proof. apply gmap_nonexpanding_merge_difference_distr, setts_key_nonexpanding. Qed.
  
  Lemma release_mono wrs tss1 tss2 :
    tss1 ⊆ tss2 ->
    release wrs tss1 ⊆ release wrs tss2.
  Proof. apply gmap_nonexpanding_merge_mono, setts_key_nonexpanding. Qed.
  
  Lemma release_filter_group_commute wrs tss gid :
    release wrs (filter_group gid tss) = filter_group gid (release wrs tss).
  Proof.
    set P := (λ x, key_to_group x = gid).
    pose proof (setts_key_nonexpanding O) as Hne.
    by apply (gmap_nonexpanding_merge_filter_commute P wrs tss) in Hne.
  Qed.

  Lemma release_empty tss :
    release ∅ tss = tss.
  Proof.
    apply map_eq. intros k.
    rewrite lookup_merge lookup_empty /=.
    by destruct (tss !! k).
  Qed.
End release.

Section multiwrite.

  Definition multiwrite_key_tpl (tid : nat) (wr : option dbval) (hist : dbhist) :=
    match wr with
    | Some v => last_extend tid hist ++ [v]
    | None => hist
    end.

  Definition multiwrite_key (tid : nat) (wr : option dbval) (ohist : option dbhist) :=
    match ohist with
    | Some hist => Some (multiwrite_key_tpl tid wr hist)
    | None => None
    end.

  Lemma multiwrite_key_nonexpanding ts :
    mergef_nonexpanding (multiwrite_key ts).
  Proof. intros x y. by destruct x, y as [h |]. Qed.

  Definition multiwrite (tid : nat) (wrs : dbmap) (hists : gmap dbkey dbhist) :=
    merge (multiwrite_key tid) wrs hists.

  Lemma multiwrite_dom {tid wrs hists} :
    dom (multiwrite tid wrs hists) = dom hists.
  Proof. apply gmap_nonexpanding_merge_dom, multiwrite_key_nonexpanding. Qed.

  (* TODO: better naming would be [lookup_multiwrite_notin]. *)
  Lemma multiwrite_unmodified {tid wrs hists key} :
    wrs !! key = None ->
    (multiwrite tid wrs hists) !! key = hists !! key.
  Proof.
    intros Hlookup.
    rewrite lookup_merge Hlookup /=.
    by destruct (hists !! key).
  Qed.

  (* TODO: better naming would be [lookup_multiwrite]. *)
  Lemma multiwrite_modified {tid wrs hists key value hist} :
    wrs !! key = Some value ->
    hists !! key = Some hist ->
    (multiwrite tid wrs hists) !! key = Some (last_extend tid hist ++ [value]).
  Proof.
    intros Hvalue Hhist.
    by rewrite lookup_merge Hvalue Hhist /=.
  Qed.

  Lemma multiwrite_difference_distr {tid wrs hists histsd} :
    multiwrite tid wrs (hists ∖ histsd) =
    multiwrite tid wrs hists ∖ multiwrite tid wrs histsd.
  Proof. apply gmap_nonexpanding_merge_difference_distr, multiwrite_key_nonexpanding. Qed.
  
  Lemma multiwrite_mono tid wrs hists1 hists2 :
    hists1 ⊆ hists2 ->
    multiwrite tid wrs hists1 ⊆ multiwrite tid wrs hists2.
  Proof. apply gmap_nonexpanding_merge_mono, multiwrite_key_nonexpanding. Qed.
  
  Lemma multiwrite_filter_group_commute tid wrs hists gid :
    multiwrite tid wrs (filter_group gid hists) = filter_group gid (multiwrite tid wrs hists).
  Proof.
    set P := (λ x, key_to_group x = gid).
    pose proof (multiwrite_key_nonexpanding tid) as Hne.
    by apply (gmap_nonexpanding_merge_filter_commute P wrs hists) in Hne.
  Qed.

  Lemma multiwrite_empty tid hists :
    multiwrite tid ∅ hists = hists.
  Proof.
    apply map_eq. intros k.
    rewrite lookup_merge lookup_empty /=.
    by destruct (hists !! k) eqn:Hk.
  Qed.

End multiwrite.

Section apply_cmds.

  (** Group state. *)

  Inductive gpst :=
  | State (cm : gmap nat bool) (hists : gmap dbkey dbhist)
  | Stuck.

  Definition not_stuck st := st ≠ Stuck.

  Definition apply_commit st (tid : nat) (pwrs : dbmap) :=
    match st with
    | State cm hists =>
        match cm !! tid with
        | Some true => st
        | Some false => Stuck
        | _ => State (<[tid := true]> cm) (multiwrite tid pwrs hists)
        end
    | Stuck => Stuck
    end.

  Definition apply_abort st (tid : nat) :=
    match st with
    | State cm hists =>
        match cm !! tid with
        | Some true => Stuck
        | Some false => st
        | _ => State (<[tid := false]> cm) hists
        end
    | Stuck => Stuck
    end.

  Definition apply_cmd st (cmd : ccommand) :=
    match cmd with
    | CmdCommit tid pwrs => apply_commit st tid pwrs
    | CmdAbort tid => apply_abort st tid
    end.

  Definition init_hists : gmap dbkey dbhist := gset_to_gmap [None] keys_all.

  Definition init_gpst :=
    State ∅ init_hists.

  Definition apply_cmds (cmds : list ccommand) :=
    foldl apply_cmd init_gpst cmds.

  Lemma apply_cmds_unfold cmds :
    foldl apply_cmd init_gpst cmds = apply_cmds cmds.
  Proof. done. Qed.

  Lemma foldl_apply_cmd_from_stuck l :
    foldl apply_cmd Stuck l = Stuck.
  Proof. by induction l as [| c l IH]; last destruct c. Qed.

  Lemma apply_cmds_not_stuck l1 l2 :
    prefix l1 l2 ->
    not_stuck (apply_cmds l2) ->
    not_stuck (apply_cmds l1).
  Proof.
    intros [l Happ] Hns.
    destruct (apply_cmds l1) eqn:Hl1; first done.
    by rewrite Happ /apply_cmds foldl_app apply_cmds_unfold Hl1 foldl_apply_cmd_from_stuck in Hns.
  Qed.

  Lemma apply_cmds_snoc (cmds : list ccommand) (cmd : ccommand) :
    apply_cmds (cmds ++ [cmd]) = apply_cmd (apply_cmds cmds) cmd.
  Proof. by rewrite /apply_cmds foldl_snoc. Qed.

  Lemma apply_cmds_dom_nonexpanding l1 l2 :
    ∀ stm1 stm2 tpls1 tpls2,
    apply_cmds l1 = State stm1 tpls1 ->
    apply_cmds (l1 ++ l2) = State stm2 tpls2 ->
    dom tpls2 = dom tpls1.
  Proof.
    generalize dependent l1.
    induction l2 as [| x l2 IH]; intros l1 stm1 stm2 tpls1 tpls2 Hrsm1 Hrsm2.
    { rewrite app_nil_r Hrsm1 in Hrsm2. by inversion Hrsm2. }
    rewrite cons_middle app_assoc in Hrsm2.
    destruct (apply_cmds (l1 ++ [x])) as [stm' tpls' |] eqn:Hrsm; last first.
    { rewrite /apply_cmds in Hrsm.
      by rewrite /apply_cmds foldl_app Hrsm foldl_apply_cmd_from_stuck in Hrsm2.
    }
    replace (dom tpls1) with (dom tpls'); first by eapply IH.
    destruct x eqn:Hx; rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm1 /= in Hrsm.
    { (* Case [CmdCommit]. *)
      destruct (stm1 !! tid) as [st |]; last first.
      { inv Hrsm. apply multiwrite_dom. }
      by destruct st; inv Hrsm.
    }
    { (* Case [CmdAbort]. *)
      destruct (stm1 !! tid) as [st |]; last by inv Hrsm.
      by destruct st; inv Hrsm.
    }
  Qed.

  Lemma apply_cmds_dom log :
    ∀ cm histm,
    apply_cmds log = State cm histm ->
    dom histm = keys_all.
  Proof.
    intros cm histm Hrsm.
    replace keys_all with (dom init_hists); last first.
    { apply dom_gset_to_gmap. }
    by eapply (apply_cmds_dom_nonexpanding [] log).
  Qed.

  Lemma apply_cmds_mono_cm {log logp cm cmp histm histmp} :
    prefix logp log ->
    apply_cmds log = State cm histm ->
    apply_cmds logp = State cmp histmp ->
    cmp ⊆ cm.
  Admitted.

  Lemma apply_cmds_mono_histm {log logp cm cmp histm histmp} :
    prefix logp log ->
    apply_cmds log = State cm histm ->
    apply_cmds logp = State cmp histmp ->
    map_Forall2 (λ _ h hp, prefix hp h) histm histmp.
  Admitted.

End apply_cmds.

Section execute_cmds.

  (** Replica state. *)

  Inductive rpst :=
  | LocalState
      (cm : gmap nat bool) (hists : gmap dbkey dbhist) (cpm : gmap nat dbmap)
      (ptgsm : gmap nat (gset u64)) (sptsm ptsm : gmap dbkey nat)
      (bm : gmap nat ballot) (ladm : gmap nat nat)
  | LocalStuck.

  Definition not_local_stuck st := st ≠ LocalStuck.

  Definition execute_commit st (tid : nat) (pwrs : dbmap) :=
    match st with
    | LocalState cm hists cpm ptgsm sptsm ptsm bm ladm =>
        match cm !! tid with
        | Some true => st
        | Some false => LocalStuck
        | None => match cpm !! tid with
                 | Some _ => LocalState
                              (<[tid := true]> cm) (multiwrite tid pwrs hists)
                              (delete tid cpm) (delete tid ptgsm) sptsm (release pwrs ptsm)
                              bm ladm
                 | None => LocalState
                            (<[tid := true]> cm) (multiwrite tid pwrs hists)
                            cpm ptgsm sptsm ptsm bm ladm
                 end
        end
    | LocalStuck => LocalStuck
    end.

  Definition execute_abort st (tid : nat) :=
    match st with
    | LocalState cm hists cpm ptgsm sptsm ptsm bm ladm =>
        match cm !! tid with
        | Some true => LocalStuck
        | Some false => st
        | None => match cpm !! tid with
                 | Some pwrs => LocalState
                                 (<[tid := false]> cm) hists (delete tid cpm)
                                 (delete tid ptgsm) sptsm (release pwrs ptsm) bm ladm
                 | None => LocalState (<[tid := false]> cm) hists cpm ptgsm sptsm ptsm bm ladm
                 end
        end
    | LocalStuck => LocalStuck
    end.

  Definition execute_acquire st (tid : nat) (pwrs : dbmap) (ptgs : gset u64) :=
    match st with
    | LocalState cm hists cpm ptgsm sptsm ptsm bm ladm =>
        LocalState
          cm hists (<[tid := pwrs]> cpm) (<[tid := ptgs]> ptgsm)
          (setts (S tid) pwrs sptsm) (acquire tid pwrs ptsm) bm ladm
    | LocalStuck => LocalStuck
    end.

  Definition execute_read st (tid : nat) (key : dbkey) :=
    match st with
    | LocalState cm hists cpm ptgsm sptsm ptsm bm ladm =>
        LocalState
          cm hists cpm ptgsm (alter (λ spts, (spts `max` tid)%nat) key sptsm) ptsm bm ladm
    | LocalStuck => LocalStuck
    end.

  Definition execute_advance st (tid : nat) (rank : nat) :=
    match st with
    | LocalState cm hists cpm ptgsm sptsm ptsm bm ladm =>
        LocalState
          cm hists cpm ptgsm sptsm ptsm
          (alter (λ l, extend tid Reject l) tid bm) ladm
    | LocalStuck => LocalStuck
    end.

  Definition execute_accept st (tid : nat) (rank : nat) (pdec : bool) :=
    match st with
    | LocalState cm hists cpm ptgsm sptsm ptsm bm ladm =>
        LocalState
          cm hists cpm ptgsm sptsm ptsm
          (alter (λ l, extend tid Reject l ++ [Accept pdec]) tid bm)
          (<[tid := rank]> ladm)
    | LocalStuck => LocalStuck
    end.

  Definition execute_cmd st (cmd : command) :=
    match cmd with
    | CCmd cmd => match cmd with
                 | CmdCommit tid pwrs => execute_commit st tid pwrs
                 | CmdAbort tid => execute_abort st tid
                 end
    | ICmd cmd => match cmd with
                 | CmdAcquire tid pwrs ptgs => execute_acquire st tid pwrs ptgs
                 | CmdRead tid key => execute_read st tid key
                 | CmdAdvance tid rank => execute_advance st tid rank
                 | CmdAccept tid rank pdec => execute_accept st tid rank pdec
                 end
    end.

  Definition init_sptsm : gmap dbkey nat := gset_to_gmap 1%nat keys_all.
  Definition init_ptsm : gmap dbkey nat := gset_to_gmap O%nat keys_all.
  Definition init_rpst :=
    LocalState ∅ init_hists ∅ ∅ init_sptsm init_ptsm ∅ ∅.

  Definition execute_cmds (cmds : list command) :=
    foldl execute_cmd init_rpst cmds.

  Lemma execute_cmds_snoc (cmds : list command) (cmd : command) :
    execute_cmds (cmds ++ [cmd]) = execute_cmd (execute_cmds cmds) cmd.
  Proof. by rewrite /execute_cmds foldl_snoc. Qed.

  Lemma execute_cmds_dom_histm {log cm histm cpm ptgsm sptsm ptsm bm ladm} :
    execute_cmds log = LocalState cm histm cpm ptgsm sptsm ptsm bm ladm ->
    dom histm = keys_all.
  Proof.
  Admitted.

  Lemma execute_cmds_hist_not_nil {log cm histm cpm ptgsm sptsm ptsm bm ladm} :
    execute_cmds log = LocalState cm histm cpm ptgsm sptsm ptsm bm ladm ->
    map_Forall (λ _ h, h ≠ []) histm.
  Admitted.

End execute_cmds.

Section merge_clog_ilog.
  Definition merge_clog_ilog (clog : list ccommand) (ilog : list (nat * icommand)) : list command.
  Admitted.

  Lemma merge_clog_ilog_snoc_clog clog ilog ccmd :
    Forall (λ nc, (nc.1 ≤ length clog)%nat) ilog ->
    merge_clog_ilog (clog ++ [ccmd]) ilog =
    merge_clog_ilog clog ilog ++ [CCmd ccmd].
  Admitted.

  Lemma merge_clog_ilog_snoc_ilog clog ilog lsn icmd :
    (length clog ≤ lsn)%nat ->
    merge_clog_ilog clog (ilog ++ [(lsn, icmd)]) =
    merge_clog_ilog clog ilog ++ [ICmd icmd].
  Admitted.

  Lemma execute_cmds_apply_cmds clog ilog cm histm :
    let log := merge_clog_ilog clog ilog in
    (∃ cpm ptgsm sptsm ptsm bm ladm,
        execute_cmds log = LocalState cm histm cpm ptgsm sptsm ptsm bm ladm) ->
    apply_cmds clog = State cm histm.
  Admitted.
End merge_clog_ilog.
