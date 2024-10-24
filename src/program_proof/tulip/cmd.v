From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import
  extend nonexpanding_merge.
From Perennial.program_proof.tulip Require Import base.

Section validate.
  Definition validate_key (tid : nat) (wr : option dbval) (tpl : option dbtpl) :=
    match wr, tpl with
    | Some _, Some (vs, tsprep) => Some (bool_decide (lockable tid vs tsprep))
    | Some _, None => Some false
    | _, _ => None
    end.

  Definition validate (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
    map_fold (λ _, andb) true (merge (validate_key tid) wrs tpls).

  Lemma map_fold_andb_true `{Countable K} (m : gmap K bool) :
    map_fold (λ _, andb) true m = true <-> map_Forall (λ _ b, b = true) m.
  Proof.
    split.
    - intros Hfold k b Hkb.
      destruct b; first done.
      exfalso.
      induction m as [| x v m Hnone IHm] using map_ind; first done.
      rewrite map_fold_insert_L in Hfold; last first.
      { done. }
      { intros _ _ b1 b2 b3 _ _ _. by rewrite andb_comm -andb_assoc (andb_comm b3). }
      destruct (decide (x = k)) as [-> | Hne].
      { rewrite lookup_insert in Hkb. inversion Hkb. subst v. done. }
      rewrite lookup_insert_ne in Hkb; last done.
      destruct v; last done.
      rewrite andb_true_l in Hfold.
      by apply IHm.
    - intros Hall.
      induction m as [| x v m Hnone IHm] using map_ind; first done.
      rewrite map_fold_insert_L; last first.
      { done. }
      { intros _ _ b1 b2 b3 _ _ _. by rewrite andb_comm -andb_assoc (andb_comm b3). }
      rewrite map_Forall_insert in Hall; last done.
      destruct Hall as [-> Hall].
      by apply IHm.
  Qed.

  Lemma validate_true_lockable {tid wrs tpls} key tpl :
    is_Some (wrs !! key) ->
    tpls !! key = Some tpl ->
    validate tid wrs tpls = true ->
    lockable tid tpl.1 tpl.2.
  Proof.
    intros [v Hv] Htpl Hvd.
    destruct tpl as [h t].
    rewrite /validate map_fold_andb_true in Hvd.
    specialize (Hvd key false).
    rewrite lookup_merge Hv Htpl /= in Hvd.
    case_bool_decide; [done | naive_solver].
  Qed.

  Lemma validate_true_subseteq_dom tid wrs tpls :
    validate tid wrs tpls = true ->
    dom wrs ⊆ dom tpls.
  Proof.
    intros Hvd.
    intros key Hkey.
    rewrite /validate map_fold_andb_true in Hvd.
    specialize (Hvd key false).
    rewrite elem_of_dom in Hkey. destruct Hkey as [v Hv].
    destruct (decide (key ∈ dom tpls)) as [? | Hnotin]; first done.
    rewrite not_elem_of_dom in Hnotin.
    rewrite lookup_merge Hv Hnotin /= in Hvd.
    naive_solver.
  Qed.

  Lemma validate_true_exists {tid wrs tpls} key :
    is_Some (wrs !! key) ->
    validate tid wrs tpls = true ->
    ∃ tpl, tpls !! key = Some tpl ∧ lockable tid tpl.1 tpl.2.
  Proof.
    intros [v Hv] Hvd.
    pose proof (validate_true_subseteq_dom _ _ _ Hvd) as Hdom.
    apply elem_of_dom_2 in Hv as Hkey.
    specialize (Hdom _ Hkey).
    rewrite elem_of_dom in Hdom.
    destruct Hdom as [tpl Htpl].
    exists tpl.
    split; first done.
    by eapply validate_true_lockable.
  Qed.

  Lemma validate_false {tid wrs tpls} key tpl :
    is_Some (wrs !! key) ->
    tpls !! key = Some tpl ->
    ¬ lockable tid tpl.1 tpl.2 ->
    validate tid wrs tpls = false.
  Proof.
    intros [v Hv] Htpl Hfail.
    rewrite -not_true_iff_false.
    intros Hvd.
    rewrite map_fold_andb_true in Hvd.
    specialize (Hvd key false). simpl in Hvd.
    destruct tpl as [hist tsprep].
    rewrite lookup_merge Hv Htpl /= in Hvd.
    case_bool_decide; [done | naive_solver].
  Qed.

  Lemma validate_empty tid tpls :
    validate tid ∅ tpls = true.
  Proof.
    rewrite map_fold_andb_true.
    intros k b Hkb.
    rewrite lookup_merge lookup_empty /= in Hkb.
    by destruct (tpls !! k).
  Qed.

End validate.

Section acquire.
  Definition acquire_key (tid : nat) (wr : option dbval) (ots : option nat) :=
    match wr, ots with
    | None, Some ts => Some ts
    | Some _, Some _ => Some tid
    | _, _ => None
    end.

  Lemma acquire_key_nonexpanding ts :
    mergef_nonexpanding (acquire_key ts).
  Proof. intros x y. by destruct x, y as [t |]. Qed.

  Definition acquire (tid : nat) (wrs : dbmap) (tpls : gmap dbkey nat) :=
    merge (acquire_key tid) wrs tpls.

  Lemma acquire_dom {tid wrs tss} :
    dom (acquire tid wrs tss) = dom tss.
  Proof.
    apply gmap_nonexpanding_merge_dom, acquire_key_nonexpanding.
  Qed.

  Lemma acquire_unmodified {tid wrs tss key} :
    wrs !! key = None ->
    (acquire tid wrs tss) !! key = tss !! key.
  Proof.
    intros Hnone.
    rewrite /acquire lookup_merge Hnone /=.
    by destruct (tss !! key).
  Qed.

  Lemma acquire_modified {tid wrs tss key} :
    is_Some (wrs !! key) ->
    is_Some (tss !! key) ->
    (acquire tid wrs tss) !! key = Some tid.
  Proof.
    intros [v Hv] [ts Hts].
    by rewrite /acquire lookup_merge Hv Hts /=.
  Qed.

  Lemma acquire_difference_distr {tid wrs tss tssd} :
    acquire tid wrs (tss ∖ tssd) =
    acquire tid wrs tss ∖ acquire tid wrs tssd.
  Proof. apply gmap_nonexpanding_merge_difference_distr, acquire_key_nonexpanding. Qed.
  
  Lemma acquire_mono tid wrs tss1 tss2 :
    tss1 ⊆ tss2 ->
    acquire tid wrs tss1 ⊆ acquire tid wrs tss2.
  Proof. apply gmap_nonexpanding_merge_mono, acquire_key_nonexpanding. Qed.
  
  Lemma acquire_filter_group_commute tid wrs tss gid :
    acquire tid wrs (filter_group gid tss) = filter_group gid (acquire tid wrs tss).
  Proof.
    set P := (λ x, key_to_group x = gid).
    pose proof (acquire_key_nonexpanding tid) as Hne.
    by apply (gmap_nonexpanding_merge_filter_commute P wrs tss) in Hne.
  Qed.

  Lemma acquire_empty tid tss :
    acquire tid ∅ tss = tss.
  Proof.
    apply map_eq. intros k.
    rewrite lookup_merge lookup_empty /=.
    by destruct (tss !! k).
  Qed.
End acquire.

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

Section release.
  Definition release_key (wr : option dbval) (ots : option nat) :=
    match wr, ots with
    | None, Some _ => ots
    | Some _, Some _ => Some O
    | _, _ => None
    end.

  Lemma release_key_nonexpanding :
    mergef_nonexpanding release_key.
  Proof. intros x y. by destruct x, y as [t |]. Qed.

  Definition release (wrs : dbmap) (tss : gmap dbkey nat) :=
    merge release_key wrs tss.

  Lemma release_unmodified {wrs tss key} :
    wrs !! key = None ->
    (release wrs tss) !! key = tss !! key.
  Proof.
    intros Hlookup.
    rewrite lookup_merge Hlookup /=.
    by destruct (tss !! key) as [t |] eqn:Ht.
  Qed.

  Lemma release_modified {wrs ptsm key} :
    key ∈ dom wrs ->
    key ∈ dom ptsm ->
    (release wrs ptsm) !! key = Some O.
  Proof.
    intros Hwrs Hptsm.
    apply elem_of_dom in Hwrs as [v Hv].
    apply elem_of_dom in Hptsm as [t Ht].
    by rewrite lookup_merge Hv Ht /=.
  Qed.

  Lemma release_dom {wrs tss} :
    dom (release wrs tss) = dom tss.
  Proof. apply gmap_nonexpanding_merge_dom, release_key_nonexpanding. Qed.

  Lemma release_difference_distr {wrs tss tssd} :
    release wrs (tss ∖ tssd) =
    release wrs tss ∖ release wrs tssd.
  Proof. apply gmap_nonexpanding_merge_difference_distr, release_key_nonexpanding. Qed.

  Lemma release_mono wrs tss1 tss2 :
    tss1 ⊆ tss2 ->
    release wrs tss1 ⊆ release wrs tss2.
  Proof. apply gmap_nonexpanding_merge_mono, release_key_nonexpanding. Qed.

  Lemma release_filter_group_commute wrs tss gid :
    release wrs (filter_group gid tss) = filter_group gid (release wrs tss).
  Proof.
    set P := (λ x, key_to_group x = gid).
    pose proof release_key_nonexpanding as Hne.
    by apply (gmap_nonexpanding_merge_filter_commute P wrs tss) in Hne.
  Qed.

  (* Lemma release_acquire_inverse tid wrs tss : *)
  (*   validate tid wrs tss = true -> *)
  (*   release wrs (acquire tid wrs tss) = tss. *)
  (* Proof. *)
  (*   intros Hvd. *)
  (*   apply map_eq. intros k. *)
  (*   rewrite /release lookup_merge /acquire lookup_merge. *)
  (*   destruct (wrs !! k) as [v |] eqn:Hv, *)
  (*              (tss !! k) as [[h t] |] eqn:Hts; rewrite Hv; [| done | done | done]. *)
  (*   (* not sure why [rewrite Hv] is required. *) *)
  (*   rewrite /validate map_fold_andb_true in Hvd. *)
  (*   specialize (Hvd k false). *)
  (*   rewrite lookup_merge Hv Hts /= in Hvd. *)
  (*   case_bool_decide as Hlock; last naive_solver. *)
  (*   destruct Hlock as [Ht _]. *)
  (*   by subst t. *)
  (* Qed. *)

  Lemma release_empty tss :
    release ∅ tss = tss.
  Proof.
    apply map_eq. intros k.
    rewrite lookup_merge lookup_empty /=.
    by destruct (tss !! k) eqn:Hk.
  Qed.

End release.

Section apply_cmds.

  (** Replica state. *)
  Inductive rpst :=
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

  Definition apply_cmd st (cmd : command) :=
    match cmd with
    | CmdCommit tid pwrs => apply_commit st tid pwrs
    | CmdAbort tid => apply_abort st tid
    end.

  Definition init_hists : gmap dbkey dbhist := gset_to_gmap [None] keys_all.

  Definition init_rpst :=
    State ∅ init_hists.

  Definition apply_cmds (cmds : list command) :=
    foldl apply_cmd init_rpst cmds.

  Lemma apply_cmds_unfold cmds :
    foldl apply_cmd init_rpst cmds = apply_cmds cmds.
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
    ∀ stm tpls,
    apply_cmds log = State stm tpls ->
    dom tpls = keys_all.
  Proof.
    intros stm tpls Hrsm.
    replace keys_all with (dom init_hists); last first.
    { apply dom_gset_to_gmap. }
    by eapply (apply_cmds_dom_nonexpanding [] log).
  Qed.

End apply_cmds.
