From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import
  extend nonexpanding_merge fin_maps.
From Perennial.program_proof.tulip Require Import base stability encode.

(* TODO: rename this to recovery.v for consistency with paxos. *)

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

  Lemma setts_insert ts wrs tsm k v :
    k ∈ dom tsm ->
    setts ts (<[k := v]> wrs) tsm = <[k := ts]> (setts ts wrs tsm).
  Proof.
    intros Hk. apply elem_of_dom in Hk as [t Ht].
    symmetry.
    apply insert_merge_l.
    by rewrite /= Ht.
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

  Definition safe_extension (ts : nat) (pwrs : dbmap) (histm : gmap dbkey dbhist) :=
    map_Forall (λ _ l, (length l ≤ ts)%nat) (filter (λ x, x.1 ∈ dom pwrs) histm).

  Definition apply_commit st (tid : nat) (pwrs : dbmap) :=
    match st with
    | State cm histm =>
        match cm !! tid with
        | Some true => st
        | Some false => Stuck
        | _ => if decide (safe_extension tid pwrs histm)
              then State (<[tid := true]> cm) (multiwrite tid pwrs histm)
              else Stuck
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
      { case_decide; last done. inv Hrsm. apply multiwrite_dom. }
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
  Proof.
    intros [l ->].
    generalize dependent histmp.
    generalize dependent cmp.
    generalize dependent logp.
    induction l as [| c l IH]; intros logp cmp histmp Happly Happlyp.
    { rewrite app_nil_r Happlyp in Happly. by inv Happly. }
    rewrite cons_middle app_assoc in Happly.
    destruct (apply_cmds (logp ++ [c])) as [cm' hist' |] eqn:Hrsm; last first.
    { rewrite /apply_cmds foldl_app apply_cmds_unfold Hrsm in Happly.
      by rewrite foldl_apply_cmd_from_stuck in Happly.
    }
    trans cm'; last first.
    { eapply IH; [apply Happly | apply Hrsm]. }
    destruct c as [ts pwrs | ts].
    { rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold Happlyp /apply_commit in Hrsm.
      destruct (cmp !! ts) eqn:Hcmpts.
      { by destruct b; first inv Hrsm. }
      { case_decide; last done. inv Hrsm. by apply insert_subseteq. }
    }
    { rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold Happlyp /apply_abort in Hrsm.
      destruct (cmp !! ts) eqn:Hcmpts.
      { by destruct b; last inv Hrsm. }
      { inv Hrsm. by apply insert_subseteq. }
    }
  Qed.

  Lemma apply_cmds_mono_histm {log logp cm cmp histm histmp} :
    prefix logp log ->
    apply_cmds log = State cm histm ->
    apply_cmds logp = State cmp histmp ->
    map_Forall2 (λ _ h hp, prefix hp h) histm histmp.
  Proof.
    intros [l ->].
    generalize dependent histmp.
    generalize dependent cmp.
    generalize dependent logp.
    induction l as [| c l IH]; intros logp cmp histmp Happly Happlyp.
    { rewrite app_nil_r Happlyp in Happly.
      inv Happly.
      rewrite map_Forall2_forall.
      split; last done.
      intros k x y Hx Hy.
      rewrite Hx in Hy. by inv Hy.
    }
    rewrite cons_middle app_assoc in Happly.
    destruct (apply_cmds (logp ++ [c])) as [cm' hist' |] eqn:Hrsm; last first.
    { rewrite /apply_cmds foldl_app apply_cmds_unfold Hrsm in Happly.
      by rewrite foldl_apply_cmd_from_stuck in Happly.
    }
    specialize (IH _ _ _ Happly Hrsm).
    rewrite map_Forall2_forall.
    split; last first.
    { by rewrite (apply_cmds_dom _ _ _ Happly) (apply_cmds_dom _ _ _ Happlyp). }
    intros k l1 l2 Hl1 Hl2.
    destruct c as [ts pwrs | ts].
    { rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold Happlyp /apply_commit in Hrsm.
      destruct (cmp !! ts).
      { destruct b; last done.
        symmetry in Hrsm. inv Hrsm.
        apply (map_Forall2_lookup_Some _ _ _ _ _ _ Hl1 Hl2 IH).
      }
      { case_decide; last done. inv Hrsm.
        destruct (pwrs !! k) as [v |] eqn:Hpwrsk.
        { pose proof (@multiwrite_modified ts _ _ _ _ _ Hpwrsk Hl2) as Hl2'.
          pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hl1 Hl2' IH) as Hprefix.
          simpl in Hprefix.
          etrans; last apply Hprefix.
          apply prefix_app_r, last_extend_prefix.
        }
        { rewrite -(@multiwrite_unmodified ts _ _ _ Hpwrsk) in Hl2.
          apply (map_Forall2_lookup_Some _ _ _ _ _ _ Hl1 Hl2 IH).
        }
      }
    }
    { rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold Happlyp /apply_abort in Hrsm.
      destruct (cmp !! ts) eqn:Hcmpts.
      { destruct b; first done.
        symmetry in Hrsm. inv Hrsm.
        apply (map_Forall2_lookup_Some _ _ _ _ _ _ Hl1 Hl2 IH).
      }
      { symmetry in Hrsm. inv Hrsm.
        apply (map_Forall2_lookup_Some _ _ _ _ _ _ Hl1 Hl2 IH).
      }
    }
  Qed.

  Lemma apply_cmds_hist_not_nil {log cm histm} :
    apply_cmds log = State cm histm ->
    map_Forall (λ _ h, h ≠ []) histm.
  Proof.
    intros Happly k h Hh Hnil.
    assert (Hinit : apply_cmds [] = init_gpst) by done.
    unshelve epose proof (apply_cmds_mono_histm _ Happly Hinit) as Hprefix.
    { apply prefix_nil. }
    apply map_Forall2_forall in Hprefix as [Hprefix Hdom].
    assert (is_Some (init_hists !! k)) as [h' Hh'].
    { by rewrite -elem_of_dom -Hdom elem_of_dom. }
    specialize (Hprefix _ _ _ Hh Hh').
    apply lookup_gset_to_gmap_Some in Hh' as [_ <-].
    subst h.
    by eapply prefix_nil_not.
  Qed.

End apply_cmds.

Section execute_cmds.

  (** Replica state. *)

  Inductive rpst :=
  | LocalState
      (cm : gmap nat bool) (hists : gmap dbkey dbhist) (cpm : gmap nat dbmap)
      (ptgsm : gmap nat (gset u64)) (sptsm ptsm : gmap dbkey nat)
      (psm : gmap nat (nat * bool)) (rkm : gmap nat nat)
  | LocalStuck.

  Definition not_local_stuck st := st ≠ LocalStuck.

  Definition execute_commit st (tid : nat) (pwrs : dbmap) :=
    match st with
    | LocalState cm histm cpm ptgsm sptsm ptsm psm rkm =>
        match cm !! tid with
        | Some true => st
        | Some false => LocalStuck
        | None => if decide (safe_extension tid pwrs histm)
                 then match cpm !! tid with
                      | Some _ => LocalState
                                   (<[tid := true]> cm) (multiwrite tid pwrs histm)
                                   (delete tid cpm) (delete tid ptgsm) sptsm (release pwrs ptsm)
                                   psm rkm
                      | None => LocalState
                                 (<[tid := true]> cm) (multiwrite tid pwrs histm)
                                 cpm ptgsm sptsm ptsm psm rkm
                      end
                 else LocalStuck
        end
    | LocalStuck => LocalStuck
    end.

  Definition execute_abort st (tid : nat) :=
    match st with
    | LocalState cm hists cpm ptgsm sptsm ptsm psm rkm =>
        match cm !! tid with
        | Some true => LocalStuck
        | Some false => st
        | None => match cpm !! tid with
                 | Some pwrs => LocalState
                                 (<[tid := false]> cm) hists (delete tid cpm)
                                 (delete tid ptgsm) sptsm (release pwrs ptsm) psm rkm
                 | None => LocalState (<[tid := false]> cm) hists cpm ptgsm sptsm ptsm psm rkm
                 end
        end
    | LocalStuck => LocalStuck
    end.

  Definition execute_acquire st (tid : nat) (pwrs : dbmap) (ptgs : txnptgs) :=
    match st with
    | LocalState cm hists cpm ptgsm sptsm ptsm psm rkm =>
        LocalState
          cm hists (<[tid := pwrs]> cpm) (<[tid := ptgs]> ptgsm)
          (setts tid pwrs sptsm) (acquire tid pwrs ptsm) psm rkm
    | LocalStuck => LocalStuck
    end.

  Definition execute_read st (tid : nat) (key : dbkey) :=
    match st with
    | LocalState cm hists cpm ptgsm sptsm ptsm psm rkm =>
        LocalState
          cm hists cpm ptgsm (alter (λ spts, (spts `max` pred tid)%nat) key sptsm) ptsm psm rkm
    | LocalStuck => LocalStuck
    end.

  Definition init_psm (tid : nat) (psm : gmap nat (nat * bool)) :=
    match psm !! tid with
    | Some _ => psm
    | None => <[tid := (O, false)]> psm
    end.

  Definition execute_advance st (tid : nat) (rank : nat) :=
    match st with
    | LocalState cm hists cpm ptgsm sptsm ptsm psm rkm =>
        LocalState cm hists cpm ptgsm sptsm ptsm (init_psm tid psm) (<[tid := rank]> rkm)
    | LocalStuck => LocalStuck
    end.

  Definition execute_accept st (tid : nat) (rank : nat) (pdec : bool) :=
    match st with
    | LocalState cm hists cpm ptgsm sptsm ptsm psm rkm =>
        LocalState
          cm hists cpm ptgsm sptsm ptsm (<[tid := (rank, pdec)]> psm) (<[tid := S rank]> rkm)
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
                 (* TODO: switch these two to be consistent *)
                 | CmdRead tid key => execute_read st tid key
                 | CmdAdvance tid rank => execute_advance st tid rank
                 | CmdAccept tid rank pdec => execute_accept st tid rank pdec
                 end
    end.

  Definition init_sptsm : gmap dbkey nat := gset_to_gmap O keys_all.
  Definition init_ptsm : gmap dbkey nat := gset_to_gmap O keys_all.
  Definition init_rpst :=
    LocalState ∅ init_hists ∅ ∅ init_sptsm init_ptsm ∅ ∅.

  Definition execute_cmds (cmds : list command) :=
    foldl execute_cmd init_rpst cmds.

  Lemma execute_cmds_unfold cmds :
    foldl execute_cmd init_rpst cmds = execute_cmds cmds.
  Proof. done. Qed.

  Lemma execute_cmds_snoc (cmds : list command) (cmd : command) :
    execute_cmds (cmds ++ [cmd]) = execute_cmd (execute_cmds cmds) cmd.
  Proof. by rewrite /execute_cmds foldl_snoc. Qed.

End execute_cmds.

Section merge_clog_ilog.

  Definition merge_until_ilog_step
    (clog : list ccommand) (nl : nat * list command) (icmd : nat * icommand) :=
    ((nl.1 `max` icmd.1)%nat, nl.2 ++ (subslice nl.1 icmd.1 (CCmd <$> clog)) ++ [ICmd icmd.2]).

  Definition merge_until_ilog clog ilog :=
    foldl (merge_until_ilog_step clog) (O, []) ilog.

  Lemma merge_until_ilog_def clog ilog :
    merge_until_ilog clog ilog = foldl (merge_until_ilog_step clog) (O, []) ilog.
  Proof. done. Qed.

  Lemma merge_until_ilog_step_skip clog nl icmd ccmd :
    (icmd.1 ≤ length clog)%nat ->
    merge_until_ilog_step (clog ++ [ccmd]) nl icmd =
    merge_until_ilog_step clog nl icmd.
  Proof.
    intros Hlenclog.
    rewrite /merge_until_ilog_step.
    do 3 f_equal.
    rewrite 2!subslice_def.
    by rewrite fmap_app take_app_le; last rewrite length_fmap.
  Qed.

  Lemma merge_until_ilog_skip_raw clog ilog1 ilog2 ccmd :
    Forall (λ nc, (nc.1 ≤ length clog)%nat) ilog2 ->
    merge_until_ilog (clog ++ [ccmd]) ilog1 = merge_until_ilog clog ilog1 ->
    merge_until_ilog (clog ++ [ccmd]) (ilog1 ++ ilog2) =
    merge_until_ilog clog (ilog1 ++ ilog2).
  Proof.
    intros Hlen.
    generalize dependent ilog1.
    induction ilog2 as [| icmd ilog IH]; intros ilog1 Heq.
    { by rewrite app_nil_r. }
    apply Forall_cons in Hlen as [Hicmd Hilog].
    rewrite (cons_middle _ ilog1) app_assoc.
    rewrite IH; [done | done |].
    rewrite /merge_until_ilog 2!foldl_snoc.
    rewrite merge_until_ilog_step_skip; last done.
    by rewrite -2!merge_until_ilog_def Heq.
  Qed.

  Lemma merge_until_ilog_skip clog ilog ccmd :
    Forall (λ nc, (nc.1 ≤ length clog)%nat) ilog ->
    merge_until_ilog (clog ++ [ccmd]) ilog = merge_until_ilog clog ilog.
  Proof.
    intros Hlen.
    by apply (merge_until_ilog_skip_raw clog [] ilog ccmd).
  Qed.

  Lemma merge_until_ilog_le_raw clog ilog1 ilog2 x :
    Forall (λ nc, (nc.1 ≤ x)%nat) ilog2 ->
    ((merge_until_ilog clog ilog1).1 ≤ x)%nat ->
    ((merge_until_ilog clog (ilog1 ++ ilog2)).1 ≤ x)%nat.
  Proof.
    generalize dependent ilog1.
    induction ilog2 as [| icmd ilog IH]; intros ilog1 Hle Hilog1.
    { by rewrite app_nil_r. }
    apply Forall_cons in Hle as [Hicmd Hilog].
    rewrite (cons_middle _ ilog1) app_assoc.
    apply IH; first done.
    rewrite /merge_until_ilog foldl_snoc -merge_until_ilog_def /merge_until_ilog_step /=.
    lia.
  Qed.

  Lemma merge_until_ilog_le clog ilog x :
    Forall (λ nc, (nc.1 ≤ x)%nat) ilog ->
    ((merge_until_ilog clog ilog).1 ≤ x)%nat.
  Proof.
    intros Hle.
    apply (merge_until_ilog_le_raw clog [] ilog x); first done.
    simpl.
    lia.
  Qed.

  Definition merge_clog_ilog clog ilog :=
    let (n, log) := merge_until_ilog clog ilog in
    log ++ drop n (CCmd <$> clog).

  Lemma merge_clog_ilog_nil :
    merge_clog_ilog [] [] = [].
  Proof. by rewrite /merge_clog_ilog /merge_until_ilog /=. Qed.

  Lemma merge_clog_ilog_snoc_clog clog ilog ccmd :
    Forall (λ nc, (nc.1 ≤ length clog)%nat) ilog ->
    merge_clog_ilog (clog ++ [ccmd]) ilog =
    merge_clog_ilog clog ilog ++ [CCmd ccmd].
  Proof.
    intros Hlen.
    rewrite /merge_clog_ilog merge_until_ilog_skip; last done.
    pose proof (merge_until_ilog_le clog _ _ Hlen) as Hle.
    set nl := merge_until_ilog _ _ in Hle *.
    destruct nl as [n l] eqn:Hnl.
    rewrite fmap_app drop_app_le; last first.
    { by rewrite length_fmap. }
    by rewrite app_assoc.
  Qed.

  Lemma merge_clog_ilog_snoc_ilog clog ilog lsn icmd :
    (length clog ≤ lsn)%nat ->
    merge_clog_ilog clog (ilog ++ [(lsn, icmd)]) =
    merge_clog_ilog clog ilog ++ [ICmd icmd].
  Proof.
    intros Hlsn.
    rewrite {1}/merge_clog_ilog /merge_until_ilog foldl_snoc /=.
    set trailing := drop _ _.
    assert (trailing = []) as ->.
    { subst trailing.
      apply drop_ge.
      rewrite length_fmap.
      lia.
    }
    rewrite app_nil_r app_assoc.
    f_equal.
    rewrite /merge_clog_ilog -merge_until_ilog_def.
    set nl := merge_until_ilog _ _.
    destruct nl as [n l].
    simpl.
    f_equal.
    by rewrite subslice_def take_ge; last rewrite length_fmap.
  Qed.

  Definition execute_apply_consistent clog ilog :=
    ∀ cm histm,
    let log := merge_clog_ilog clog ilog in
    (∃ cpm ptgsm sptsm ptsm psm rkm,
        execute_cmds log = LocalState cm histm cpm ptgsm sptsm ptsm psm rkm) ->
    apply_cmds clog = State cm histm.

  Definition is_ccmd (c : command) :=
    match c with
    | CCmd _ => True
    | _ => False
    end.

  #[global]
  Instance is_ccmd_decision c :
    Decision (is_ccmd c).
  Proof. destruct c; apply _. Defined.

  Definition filter_ccmd (log : list command) :=
    filter (λ c, is_ccmd c) log.

  Definition rpst_to_gpst st :=
    match st with
    | LocalState cm histm _ _ _ _ _ _ => State cm histm
    | _ => Stuck
    end.

  Lemma rpst_to_gpst_execute_ccmds_raw log1 log2 :
    rpst_to_gpst (execute_cmds log1) = rpst_to_gpst (execute_cmds (filter_ccmd log1)) ->
    rpst_to_gpst (execute_cmds (log1 ++ log2)) =
    rpst_to_gpst (execute_cmds (filter_ccmd (log1 ++ log2))).
  Proof.
    generalize dependent log1.
    induction log2 as [| cmd log IH]; intros log1 Heq.
    { by rewrite app_nil_r. }
    rewrite cons_middle app_assoc.
    apply IH.
    destruct cmd.
    { rewrite /filter_ccmd filter_app filter_cons /= filter_nil.
      rewrite /execute_cmds 2!foldl_snoc 2!execute_cmds_unfold.
      destruct (execute_cmds _).
      { destruct (execute_cmds _); last done.
        symmetry in Heq. inv Heq.
        destruct cmd; simpl.
        { destruct (cm !! tid); first by destruct b.
          case_decide; last done.
          destruct (cpm !! tid).
          { by destruct (cpm0 !! tid). }
          { by destruct (cpm0 !! tid). }
        }
        { destruct (cm !! tid); first by destruct b.
          destruct (cpm !! tid).
          { by destruct (cpm0 !! tid). }
          { by destruct (cpm0 !! tid). }
        }
      }
      { by destruct (execute_cmds _). }
    }
    { rewrite /filter_ccmd filter_app filter_cons /= filter_nil app_nil_r -Heq.
      rewrite /execute_cmds foldl_snoc execute_cmds_unfold.
      by destruct cmd; destruct (execute_cmds log1).
    }
  Qed.

  Lemma rpst_to_gpst_execute_ccmds log :
    rpst_to_gpst (execute_cmds log) =
    rpst_to_gpst (execute_cmds (filter_ccmd log)).
  Proof. by apply (rpst_to_gpst_execute_ccmds_raw [] log). Qed.

  Lemma filter_merged_cmds_raw clog ilog1 ilog2 :
    filter_ccmd (merge_clog_ilog clog ilog1) = CCmd <$> clog ->
    filter_ccmd (merge_clog_ilog clog (ilog1 ++ ilog2)) = CCmd <$> clog.
  Proof.
    generalize dependent ilog1.
    induction ilog2 as [| icmd ilog IH]; intros ilog1 Heq.
    { by rewrite app_nil_r. }
    rewrite cons_middle app_assoc.
    apply IH.
    rewrite /merge_clog_ilog in Heq.
    destruct (merge_until_ilog clog ilog1) as [n l] eqn:Hnl.
    rewrite /merge_clog_ilog /merge_until_ilog foldl_snoc -merge_until_ilog_def Hnl /=.
    rewrite -{3}Heq.
    destruct (decide (icmd.1 ≤ n)%nat) as [Hle | Hgt].
    { replace (_ `max` _)%nat with n by lia.
      rewrite /filter_ccmd !filter_app.
      f_equal.
      rewrite subslice_none; last apply Hle.
      by rewrite filter_cons /= filter_nil app_nil_r.
    }
    replace (_ `max` _)%nat with icmd.1 by lia.
    rewrite /filter_ccmd !filter_app.
    rewrite filter_cons /= filter_nil app_nil_r -app_assoc.
    f_equal.
    rewrite -filter_app.
    f_equal.
    rewrite subslice_def.
    apply drop_take_drop.
    lia.
  Qed.

  Lemma filter_merged_cmds clog ilog :
    filter_ccmd (merge_clog_ilog clog ilog) = CCmd <$> clog.
  Proof.
    apply (filter_merged_cmds_raw clog [] ilog).
    rewrite /merge_clog_ilog /= drop_0.
    rewrite /filter_ccmd list_filter_all; first done.
    intros i c Hc.
    by apply list_lookup_fmap_Some in Hc as (x & -> & _).
  Qed.

  Lemma rpst_to_gpst_execute_cmds_raw clog1 clog2 :
    rpst_to_gpst (execute_cmds (CCmd <$> clog1)) = apply_cmds clog1 ->
    rpst_to_gpst (execute_cmds (CCmd <$> clog1 ++ clog2)) = apply_cmds (clog1 ++ clog2).
  Proof.
    generalize dependent clog1.
    induction clog2 as [| ccmd clog IH]; intros clog1 Hcst.
    { by rewrite app_nil_r. }
    rewrite cons_middle app_assoc.
    apply IH.
    rewrite fmap_app /execute_cmds foldl_snoc execute_cmds_unfold.
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold.
    rewrite -Hcst.
    destruct ccmd.
    { rewrite /= /apply_commit.
      destruct (execute_cmds _); last done.
      simpl.
      destruct (cm !! tid).
      { by destruct b. }
      case_decide; last done.
      by destruct (cpm !! tid).
    }
    { rewrite /= /apply_abort.
      destruct (execute_cmds _); last done.
      simpl.
      destruct (cm !! tid).
      { by destruct b. }
      by destruct (cpm !! tid).
    }
  Qed.

  Lemma rpst_to_gpst_execute_cmds clog :
    rpst_to_gpst (execute_cmds (CCmd <$> clog)) = apply_cmds clog.
  Proof. by apply (rpst_to_gpst_execute_cmds_raw [] clog). Qed.

  Lemma rpst_to_gpst_execute_merged_cmds clog ilog :
    rpst_to_gpst (execute_cmds (merge_clog_ilog clog ilog)) = apply_cmds clog.
  Proof.
    rewrite rpst_to_gpst_execute_ccmds filter_merged_cmds.
    apply rpst_to_gpst_execute_cmds.
  Qed.

  Lemma execute_cmds_apply_cmds clog ilog cm histm :
    let log := merge_clog_ilog clog ilog in
    (∃ cpm ptgsm sptsm ptsm psm rkm,
        execute_cmds log = LocalState cm histm cpm ptgsm sptsm ptsm psm rkm) ->
    apply_cmds clog = State cm histm.
  Proof.
    intros log Hexec.
    destruct Hexec as (cpm & ptgsm & sptsm & ptsm & psm & rkm & Hexec).
    by rewrite -(rpst_to_gpst_execute_merged_cmds _ ilog) Hexec.
  Qed.

End merge_clog_ilog.

Section encode.

  Definition encode_tulip_read (ts : u64) (key : byte_string) (data : byte_string) :=
    data = u64_le (U64 0) ++ u64_le ts ++ encode_string key.

  Definition encode_tulip_acquire
    (ts : u64) (pwrs : dbmap) (ptgs : txnptgs) (data : byte_string) :=
    ∃ mdata gdata, data = u64_le (U64 1) ++ u64_le ts ++ mdata ++ gdata ∧
                   encode_dbmap pwrs mdata ∧
                   encode_txnptgs ptgs gdata.

  Definition encode_tulip_advance (ts rank : u64) (data : byte_string) :=
    data = u64_le (U64 2) ++ u64_le ts ++ u64_le rank.

  Definition encode_tulip_accept (ts rank : u64) (pdec : bool) (data : byte_string) :=
    data = u64_le (U64 3) ++ u64_le ts ++ u64_le rank ++ [if pdec then W8 1 else W8 0].

  Definition encode_lsn_icommand (lsn : u64) (icmd : icommand) (data : byte_string) :=
    ∃ cmddata, data = u64_le lsn ++ cmddata ∧
               match icmd with
               | CmdRead ts key => encode_tulip_read ts key cmddata
               | CmdAcquire ts pwrs ptgs => encode_tulip_acquire ts pwrs ptgs cmddata
               | CmdAdvance ts rank => encode_tulip_advance ts rank cmddata
               | CmdAccept ts rank pdec => encode_tulip_accept ts rank pdec cmddata
               end.

  Lemma encode_lsn_icommand_not_nil lsn icmd :
    not (encode_lsn_icommand lsn icmd []).
  Proof.
    intros Henc.
    destruct Henc as (cmddata & Happ & _).
    apply (f_equal length) in Happ.
    revert Happ. len.
  Qed.

End encode.
