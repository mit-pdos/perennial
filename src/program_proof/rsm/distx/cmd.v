From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.distx Require Import base.
From Perennial.program_proof.rsm.pure Require Import
  extend nonexpanding_merge.

(** Definition of [read]. *)

Definition read (tid : nat) (hist : dbhist) (tsprep : nat) :=
  let hist' := if decide (readable tid hist tsprep)
               then last_extend tid hist
               else hist in
  (hist', tsprep).

(** Definition and properties of [validate]. *)

Definition validate_key (tid : nat) (wr : option dbval) (tpl : option dbtpl) :=
  match wr, tpl with
  | Some _, Some (vs, tsprep) => Some (bool_decide (lockable tid vs tsprep))
  | Some _, None => Some false
  | _, _ => None
  end.

Definition validate (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  map_fold (λ _, andb) true (merge (validate_key tid) wrs tpls).

Lemma map_fold_andb_true `{Countable K} (m : gmap K bool) :
  map_fold (λ _, andb) true m = true <->
  map_Forall (λ _ b, b = true) m.
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
    { rewrite lookup_insert_eq in Hkb. inversion Hkb. subst v. done. }
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

(** Definition and properties of [acquire]. *)

Definition acquire_key (tid : nat) (wr : option dbval) (tpl : option dbtpl) :=
  match wr, tpl with
  | None, Some (vs, tsprep) => Some (vs, tsprep)
  | Some _, Some (vs, _) => Some (vs, tid)
  | _, _ => None
  end.

Definition acquire (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  merge (acquire_key tid) wrs tpls.

Lemma acquire_dom {tid wrs tpls} :
  dom (acquire tid wrs tpls) = dom tpls.
Proof.
  apply gmap_nonexpanding_merge_dom.
  intros x y.
  destruct x, y as [[h t] |]; done.
Qed.

Lemma acquire_unmodified {tid wrs tpls key} :
  wrs !! key = None ->
  (acquire tid wrs tpls) !! key = tpls !! key.
Proof.
  intros Hnone.
  rewrite /acquire lookup_merge Hnone /=.
  by destruct (tpls !! key) as [[h t] |].
Qed.

Lemma acquire_modified {tid wrs tpls key tpl} :
  is_Some (wrs !! key) ->
  tpls !! key = Some tpl ->
  (acquire tid wrs tpls) !! key = Some (tpl.1, tid).
Proof.
  intros [v Hv] Htpl. destruct tpl as [h t].
  by rewrite /acquire lookup_merge Hv Htpl /=.
Qed.

Lemma acquire_empty tid tpls :
  acquire tid ∅ tpls = tpls.
Proof.
  apply map_eq. intros k.
  rewrite lookup_merge lookup_empty /=.
  by destruct (tpls !! k) as [[h t] |] eqn:Hk.
Qed.

(** Definition and properties of [multiwirte]. *)

Definition multiwrite_key_tpl (tid : nat) (wr : option dbval) (tpl : dbtpl) :=
  match wr with
  | Some v => (last_extend tid tpl.1 ++ [v], O)
  | None => tpl
  end.

Definition multiwrite_key (tid : nat) (wr : option dbval) (tpl : option dbtpl) :=
  match tpl with
  | Some tpl => Some (multiwrite_key_tpl tid wr tpl)
  | None => None
  end.

Lemma multiwrite_key_nonexpanding ts :
  mergef_nonexpanding (multiwrite_key ts).
Proof. intros x y. by destruct x, y as [[h t] |]. Qed.

Definition multiwrite (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  merge (multiwrite_key tid) wrs tpls.

Lemma multiwrite_dom {tid wrs tpls} :
  dom (multiwrite tid wrs tpls) = dom tpls.
Proof. apply gmap_nonexpanding_merge_dom, multiwrite_key_nonexpanding. Qed.

(* TODO: better naming would be [lookup_multiwrite_notin]. *)
Lemma multiwrite_unmodified {tid wrs tpls key} :
  wrs !! key = None ->
  (multiwrite tid wrs tpls) !! key = tpls !! key.
Proof.
  intros Hlookup.
  rewrite lookup_merge Hlookup /=.
  by destruct (tpls !! key) as [t |] eqn:Ht.
Qed.

(* TODO: better naming would be [lookup_multiwrite]. *)
Lemma multiwrite_modified {tid wrs tpls key value tpl} :
  wrs !! key = Some value ->
  tpls !! key = Some tpl ->
  (multiwrite tid wrs tpls) !! key = Some (last_extend tid tpl.1 ++ [value], O).
Proof.
  intros Hvalue Htpl.
  by rewrite lookup_merge Hvalue Htpl /=.
Qed.

Lemma multiwrite_difference_distr {tid wrs tpls tplsd} :
  multiwrite tid wrs (tpls ∖ tplsd) =
  multiwrite tid wrs tpls ∖ multiwrite tid wrs tplsd.
Proof. apply gmap_nonexpanding_merge_difference_distr, multiwrite_key_nonexpanding. Qed.
  
Lemma multiwrite_mono tid wrs tpls1 tpls2 :
  tpls1 ⊆ tpls2 ->
  multiwrite tid wrs tpls1 ⊆ multiwrite tid wrs tpls2.
Proof. apply gmap_nonexpanding_merge_mono, multiwrite_key_nonexpanding. Qed.
  
Lemma multiwrite_tpls_group_commute tid wrs tpls gid :
  multiwrite tid wrs (tpls_group gid tpls) = tpls_group gid (multiwrite tid wrs tpls).
Proof.
  set P := (λ x, key_to_group x = gid).
  pose proof (multiwrite_key_nonexpanding tid) as Hne.
  by apply (gmap_nonexpanding_merge_filter_commute P wrs tpls) in Hne.
Qed.

Lemma multiwrite_empty tid tpls :
  multiwrite tid ∅ tpls = tpls.
Proof.
  apply map_eq. intros k.
  rewrite lookup_merge lookup_empty /=.
  by destruct (tpls !! k) eqn:Hk.
Qed.

(** Definition and properties of [release]. *)

Definition release_key (wr : option dbval) (tpl : option dbtpl) :=
  match wr, tpl with
  | None, Some _ => tpl
  | Some _, Some (vs, _) => Some (vs, O)
  | _, _ => None
  end.

Lemma release_key_nonexpanding :
  mergef_nonexpanding release_key.
Proof. intros x y. by destruct x, y as [[h t] |]. Qed.

Definition release (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  merge release_key wrs tpls.

Lemma release_unmodified {wrs tpls key} :
  wrs !! key = None ->
  (release wrs tpls) !! key = tpls !! key.
Proof.
  intros Hlookup.
  rewrite lookup_merge Hlookup /=.
  by destruct (tpls !! key) as [t |] eqn:Ht.
Qed.

Lemma release_modified {wrs tpls key tpl} :
  is_Some (wrs !! key) ->
  tpls !! key = Some tpl ->
  (release wrs tpls) !! key = Some (tpl.1, O).
Proof.
  intros [v Hv] Htpl.
  destruct tpl as [hist ts].
  by rewrite lookup_merge Hv Htpl /=.
Qed.

Lemma release_dom {wrs tpls} :
  dom (release wrs tpls) = dom tpls.
Proof. apply gmap_nonexpanding_merge_dom, release_key_nonexpanding. Qed.

Lemma release_difference_distr {wrs tpls tplsd} :
  release wrs (tpls ∖ tplsd) =
  release wrs tpls ∖ release wrs tplsd.
Proof. apply gmap_nonexpanding_merge_difference_distr, release_key_nonexpanding. Qed.

Lemma release_mono wrs tpls1 tpls2 :
  tpls1 ⊆ tpls2 ->
  release wrs tpls1 ⊆ release wrs tpls2.
Proof. apply gmap_nonexpanding_merge_mono, release_key_nonexpanding. Qed.

Lemma release_tpls_group_commute wrs tpls gid :
  release wrs (tpls_group gid tpls) = tpls_group gid (release wrs tpls).
Proof.
  set P := (λ x, key_to_group x = gid).
  pose proof release_key_nonexpanding as Hne.
  by apply (gmap_nonexpanding_merge_filter_commute P wrs tpls) in Hne.
Qed.

Lemma release_acquire_inverse tid wrs tpls :
  validate tid wrs tpls = true ->
  release wrs (acquire tid wrs tpls) = tpls.
Proof.
  intros Hvd.
  apply map_eq. intros k.
  rewrite /release lookup_merge /acquire lookup_merge.
  destruct (wrs !! k) as [v |] eqn:Hv,
           (tpls !! k) as [[h t] |] eqn:Htpl; rewrite Hv; [| done | done | done].
  (* not sure why [rewrite Hv] is required. *)
  rewrite /validate map_fold_andb_true in Hvd.
  specialize (Hvd k false).
  rewrite lookup_merge Hv Htpl /= in Hvd.
  case_bool_decide as Hlock; last naive_solver.
  destruct Hlock as [Ht _].
  by subst t.
Qed.

Lemma release_empty tpls :
  release ∅ tpls = tpls.
Proof.
  apply map_eq. intros k.
  rewrite lookup_merge lookup_empty /=.
  by destruct (tpls !! k) eqn:Hk.
Qed.

(** Replica state. *)

Inductive rpst :=
| State (txns : gmap nat txnst) (tpls : gmap dbkey dbtpl)
| Stuck.

Definition not_stuck st := st ≠ Stuck.

(** Command semantics. *)

Definition apply_prepare st (tid : nat) (wrs : dbmap) :=
  match st with
  | State stm tpls =>
      match stm !! tid with
      | Some _ => st
      | None =>  match validate tid wrs tpls with
                | true => State (<[tid := StPrepared wrs]> stm) (acquire tid wrs tpls)
                | false => State (<[tid := StAborted]> stm) tpls
                end
      end
  | Stuck => Stuck
  end.

Definition apply_commit st (tid : nat) :=
  match st with
  | State stm tpls =>
      match stm !! tid with
      | Some StCommitted => st
      | Some (StPrepared wrs) => State (<[tid := StCommitted]> stm) (multiwrite tid wrs tpls)
      | _ => Stuck
      end
  | Stuck => Stuck
  end.

Definition apply_abort st (tid : nat) :=
  match st with
  | State stm tpls =>
      match stm !! tid with
      | Some StAborted => st
      | Some (StPrepared wrs) => State (<[ tid := StAborted ]> stm) (release wrs tpls)
      | None => State (<[ tid := StAborted ]> stm) tpls
      | _ => Stuck
      end
  | Stuck => Stuck
  end.

Definition apply_read st (tid : nat) (key : dbkey) :=
  match st with
  | State stm tpls =>
      match tpls !! key with
      | Some (vs, tsprep) => State stm (<[ key := (read tid vs tsprep) ]> tpls)
      | None => Stuck
      end
  | Stuck => Stuck
  end.

Definition valid_ts_of_command (c : command) :=
  match c with
  | CmdCmt ts => valid_ts ts
  | CmdAbt ts => valid_ts ts
  | CmdPrep ts _ => valid_ts ts
  | CmdRead ts _ => valid_ts ts
  end.

Definition apply_cmd st (cmd : command) :=
  match cmd with
  | CmdPrep tid wrs => apply_prepare st tid wrs
  | CmdCmt tid => apply_commit st tid
  | CmdAbt tid => apply_abort st tid
  | CmdRead tid key => apply_read st tid key
  end.

Definition init_rpst :=
  State ∅ (gset_to_gmap ([None], O) keys_all).

Definition apply_cmds (cmds : list command) :=
  foldl apply_cmd init_rpst cmds.

(** Lemmas. *)
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

Lemma foldl_apply_cmd_from_stm_present l :
  ∀ stm1 stm2 tpls1 tpls2 ts,
  foldl apply_cmd (State stm1 tpls1) l = State stm2 tpls2 ->
  is_Some (stm1 !! ts) ->
  is_Some (stm2 !! ts).
Proof.
  induction l as [| c l IH]; intros stm1 stm2 tpls1 tpls2 ts Hl Hstm1; simpl in Hl.
  { inversion Hl. by subst stm2. }
  destruct (apply_cmd _ _) as [stm tpls |] eqn:Heq; last first.
  { by rewrite foldl_apply_cmd_from_stuck in Hl. }
  eapply IH; first apply Hl.
  destruct c; simpl in Heq.
  { destruct (tpls1 !! key) as [[vs tsprep] |]; inversion Heq.
    by subst stm.
  }
  { destruct (stm1 !! tid).
    { inversion Heq. by subst stm. }
    by destruct (validate _ _ _); inversion Heq;
      rewrite lookup_insert_is_Some; destruct (decide (tid = ts)); auto.
  }
  { destruct (stm1 !! tid); last done.
    destruct t; inversion Heq.
    { by rewrite lookup_insert_is_Some; destruct (decide (tid = ts)); auto. }
    { by subst stm. }
  }
  { destruct (stm1 !! tid); last first.
    { inversion Heq.
      by rewrite lookup_insert_is_Some; destruct (decide (tid = ts)); auto.
    }
    destruct t; inversion Heq.
    { by rewrite lookup_insert_is_Some; destruct (decide (tid = ts)); auto. }
    { by subst stm. }
  }
Qed.

Lemma apply_cmds_elem_of_prepare l :
  ∀ stm tpls ts pwrs,
  apply_cmds l = State stm tpls ->
  CmdPrep ts pwrs ∈ l ->
  is_Some (stm !! ts).
Proof.
  intros stm tpls ts pwrs Hrsm Hprep.
  rewrite list_elem_of_lookup in Hprep.
  destruct Hprep as [i Hprep].
  apply take_drop_middle in Hprep.
  rewrite -Hprep /apply_cmds foldl_app in Hrsm.
  destruct (foldl _ init_rpst) as [stm' tpls' |]; last first.
  { by rewrite foldl_apply_cmd_from_stuck in Hrsm. }
  simpl in Hrsm.
  destruct (stm' !! ts) eqn:Hstm.
  { eapply foldl_apply_cmd_from_stm_present; first apply Hrsm.
    by rewrite Hstm.
  }
  destruct (validate _ _ _).
  { eapply foldl_apply_cmd_from_stm_present; first apply Hrsm.
    by rewrite lookup_insert_eq.
  }
  { eapply foldl_apply_cmd_from_stm_present; first apply Hrsm.
    by rewrite lookup_insert_eq.
  }
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
  { (* Case [CmdRead]. *)
    rewrite /apply_read in Hrsm.
    destruct (tpls1 !! key) as [[vs tsprep] |] eqn:Htpls1; last by inversion Hrsm.
    inversion Hrsm. subst tpls'.
    rewrite dom_insert_L.
    apply elem_of_dom_2 in Htpls1.
    set_solver.
  }
  { (* Case [CmdPrep]. *)
    rewrite /apply_prepare in Hrsm.
    destruct (stm1 !! tid); first by inversion Hrsm.
    destruct (validate _ _ _); last by inversion Hrsm.
    inversion Hrsm.
    apply acquire_dom.
  }
  { (* Case [CmdCmt]. *)
    rewrite /apply_commit in Hrsm.
    destruct (stm1 !! tid) as [st |]; last done.
    destruct st; [| by inversion Hrsm | done].
    inversion Hrsm. subst tpls'.
    apply multiwrite_dom.
  }
  { (* Case [CmdAbt]. *)
    rewrite /apply_abort in Hrsm.
    destruct (stm1 !! tid) as [st |]; last by inversion Hrsm.
    destruct st; [| done | by inversion Hrsm].
    inversion Hrsm. subst tpls'.
    apply release_dom.
  }
Qed.

Lemma apply_cmds_dom log :
  ∀ stm tpls,
  apply_cmds log = State stm tpls ->
  dom tpls = keys_all.
Proof.
  intros stm tpls Hrsm.
  replace keys_all with (dom (gset_to_gmap ([None : dbval], O) keys_all)); last first.
  { apply dom_gset_to_gmap. }
  by eapply (apply_cmds_dom_nonexpanding [] log).
Qed.

(** RSM invariants: the top-level ones are [pts_consistency] and
[tpls_well_formed]. Note: RSM invariants can either be defined as properties
about [apply_cmds], or explicit invariants materialized in [group_inv]. The
first form gives a minimal set of invariants and allow replicas to deduce those
properties, but the proofs can be a bit repetitive and hard to comprehend. The
second form is more verbose (and weaker since it does not directly allows
replica to deduce the invariants), but might yield more informative lemmas and
proofs. Some of these lemmas about [apply_cmds] are indeed used in the replica
proof, so it seems like the first approach is preferred. *)

Definition pts_consistent log :=
  ∀ stm tpls ts pwrs key tpl,
  apply_cmds log = State stm tpls ->
  stm !! ts = Some (StPrepared pwrs) ->
  tpls !! key = Some tpl ->
  key ∈ dom pwrs ->
  tpl.2 = ts.

Definition pwrs_disjoint log :=
  ∀ stm tpls ts1 ts2 pwrs1 pwrs2,
  apply_cmds log = State stm tpls ->
  ts1 ≠ ts2 ->
  stm !! ts1 = Some (StPrepared pwrs1) ->
  stm !! ts2 = Some (StPrepared pwrs2) ->
  dom pwrs1 ## dom pwrs2.

Definition pts_nonzero log :=
  ∀ stm tpls ts pwrs,
  apply_cmds log = State stm tpls ->
  stm !! ts = Some (StPrepared pwrs) ->
  ts ≠ O.

Definition pwrs_valid gid log :=
  ∀ stm tpls ts pwrs,
  apply_cmds log = State stm tpls ->
  stm !! ts = Some (StPrepared pwrs) ->
  valid_pwrs gid pwrs.

Definition tpls_well_formed log :=
  ∀ stm tpls key tpl,
  apply_cmds log = State stm tpls ->
  tpls !! key = Some tpl ->
  tpl.2 ≠ O ->
  (length tpl.1 ≤ tpl.2)%nat.

Definition valid_pts_of_command c :=
  match c with
  | CmdPrep tid _ => valid_ts tid
  | _ => True
  end.

Definition valid_pwrs_of_command gid c :=
  match c with
  | CmdPrep _ pwrs => valid_pwrs gid pwrs
  | _ => True
  end.

Definition valid_key_of_command gid c :=
  match c with
  | CmdRead _ key => valid_key key ∧ key_to_group key = gid
  | _ => True
  end.

Definition valid_command gid c :=
  valid_ts_of_command c ∧ valid_pwrs_of_command gid c ∧ valid_key_of_command gid c.

Lemma tpls_well_formed_snoc l c :
  tpls_well_formed l ->
  tpls_well_formed (l ++ [c]).
Proof.
  intros Hwf.
  intros stmc tplsc keyx tplx Happly Htpl Hnz.
  destruct c; rewrite /apply_cmds foldl_snoc /= in Happly.
  { (* Case: [CmdRead] *)
    rewrite /apply_read in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (tpls !! key) as [[vs tsprep] |] eqn:Ht; inversion Happly.
    subst stmc tplsc.
    rewrite /read in Htpl.
    case_decide as Htsprep; last first.
    { (* Case: Fail to extend the tuple. *)
      rewrite insert_id in Htpl; last done.
      by eapply Hwf.
    }
    (* Case: Successfully extend the tuple. *)
    destruct (decide (keyx = key)) as [-> | Hne]; last first.
    { rewrite lookup_insert_ne in Htpl; last done.
      by eapply Hwf.
    }
    rewrite lookup_insert_eq in Htpl.
    inversion Htpl. subst tplx. simpl. simpl in Hnz.
    destruct Htsprep as [? | Htsprep]; first done.
    destruct (last_extend_length_eq_n_or_same tid vs) as [-> | ->]; first lia.
    by eapply (Hwf _ _ _ (vs, tsprep)).
  }
  { (* Case: [CmdPrep] *)
    rewrite /apply_prepare in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid).
    { (* Case: Status in table; no-op. *) inversion Happly. subst tplsc. by eapply Hwf. }
    destruct (validate _ _ _) eqn:Hvd; inversion Happly; subst stmc tplsc; last first.
    { (* Case: Fail to acquire lock. *) by eapply Hwf. }
    (* Case: Successfully acquire lock. *)
    destruct (wrs !! keyx) as [v |] eqn:Hwrs; last first.
    { rewrite acquire_unmodified in Htpl; last done.
      by eapply Hwf.
    }
    unshelve epose proof (validate_true_exists keyx _ Hvd) as ([h t] & Hht & [_ Hlen]); first done.
    rewrite /acquire lookup_merge Hwrs Hht /= in Htpl.
    by inversion Htpl.
  }
  { (* Case: [CmdCmt] *)
    rewrite /apply_commit in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid) as [st |] eqn:Htid; last congruence.
    destruct st as [wrs | |]; inversion Happly; subst tplsc; last by eapply Hwf.
    (* Case: Prepared. *)
    destruct (wrs !! keyx) as [v |] eqn:Hwrs; last first.
    { rewrite multiwrite_unmodified in Htpl; last done.
      by eapply Hwf.
    }
    rewrite /multiwrite lookup_merge Hwrs /= in Htpl.
    destruct (tpls !! keyx) as [[h t] |]; inversion Htpl.
    by subst tplx.
  }
  { (* Case: [CmdAbt] *)
    rewrite /apply_abort in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid) as [st |] eqn:Htid; last first.
    { (* Case: Direct abort (i.e., not prepared yet). *)
      inversion Happly. subst tplsc.
      by eapply Hwf.
    }
    destruct st; inversion Happly; subst stmc tplsc; last by eapply Hwf.
    (* Case: Prepared then abort. *)
    destruct (wrs !! keyx) as [v |] eqn:Hwrs; last first.
    { rewrite release_unmodified in Htpl; last done.
      by eapply Hwf.
    }
    rewrite /release lookup_merge Hwrs /= in Htpl.
    destruct (tpls !! keyx) as [[h t] |]; inversion Htpl.
    by subst tplx.
  }
Qed.

Lemma tpls_well_formed_nil :
  tpls_well_formed [].
Proof.
  intros stm tpls key tpl Happly Htpl Hnz.
  rewrite /apply_cmds /= /init_rpst in Happly.
  inversion Happly. subst tpls.
  rewrite lookup_gset_to_gmap_Some in Htpl.
  destruct Htpl as [_ Htpl].
  by subst tpl.
Qed.

Lemma tpls_well_formedness_step l1 l2 :
  tpls_well_formed l1 ->
  tpls_well_formed (l1 ++ l2).
Proof.
  generalize dependent l1.
  induction l2 as [| c l2 IH].
  { intros l1. by rewrite app_nil_r. }
  intros l1 Hwf.
  rewrite cons_middle app_assoc.
  by apply IH, tpls_well_formed_snoc.
Qed.

Lemma tpls_well_formedness l :
  tpls_well_formed l.
Proof. apply (tpls_well_formedness_step [] l), tpls_well_formed_nil. Qed.

Lemma pwrs_valid_snoc gid l c :
  valid_pwrs_of_command gid c ->
  pwrs_valid gid l ->
  pwrs_valid gid (l ++ [c]).
Proof.
  intros Hc Hpwrs.
  intros stmc tplsc ts pwrs Happly Hstm.
  destruct c; rewrite /apply_cmds foldl_snoc /= in Happly.
  { (* Case: [CmdRead] *)
    rewrite /apply_read in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (tpls !! key) as [[vs tsprep] |]; inversion Happly.
    subst stmc tplsc.
    by eapply Hpwrs.
  }
  { (* Case: [CmdPrep] *)
    rewrite /apply_prepare in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid).
    { (* Case: Status in table; no-op. *)
      inversion Happly. subst stmc tplsc.
      by eapply Hpwrs.
    }
    destruct (validate _ _ _); inversion Happly; subst stmc tplsc; last first.
    { (* Case: Fail to acquire lock. *)
      destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert_eq in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hpwrs.
    }
    (* Case: Successfully acquire lock. *)
    destruct (decide (ts = tid)) as [-> | Hne]; last first.
    { rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hpwrs.
    }
    rewrite lookup_insert_eq in Hstm.
    inversion Hstm.
    by subst wrs.
  }
  { (* Case: [CmdCmt] *)
    rewrite /apply_commit in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid) as [st |] eqn:Htid; last congruence.
    destruct st as [wrs | |]; last congruence.
    { (* Case: Prepared. *)
      inversion Happly. subst stmc tplsc.
      destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert_eq in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hpwrs.
    }
    { (* Case: Already committed; no-op. *)
      inversion Happly. subst stmc tplsc.
      by eapply Hpwrs.
    }
  }
  { (* Case: [CmdAbt] *)
    rewrite /apply_abort in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid) as [st |] eqn:Htid; last first.
    { (* Case: Direct abort (i.e., not prepared yet). *)
      inversion Happly. subst stmc tplsc.
      destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert_eq in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hpwrs.
    }
    destruct st; inversion Happly; subst stmc tplsc; last by eapply Hpwrs.
    (* Case: Prepared then abort. *)
    destruct (decide (ts = tid)) as [-> | Hne].
    { by rewrite lookup_insert_eq in Hstm. }
    rewrite lookup_insert_ne in Hstm; last done.
    by eapply Hpwrs.
  }
Qed.

Lemma pwrs_valid_nil gid :
  pwrs_valid gid [].
Proof.
  intros stm tpls ts pwrs Happly Hpwrs.
  rewrite /apply_cmds /= /init_rpst in Happly.
  set_solver.
Qed.

Lemma pwrs_validity_step gid l1 l2 :
  Forall (λ c, valid_pwrs_of_command gid c) l2 ->
  pwrs_valid gid l1 ->
  pwrs_valid gid (l1 ++ l2).
Proof.
  intros Hpwrs.
  generalize dependent l1.
  induction l2 as [| c l2 IH].
  { intros l1. by rewrite app_nil_r. }
  rewrite Forall_cons in Hpwrs. destruct Hpwrs as [Hc Hl2].
  intros l1 Hvd.
  rewrite cons_middle app_assoc.
  by apply IH, pwrs_valid_snoc.
Qed.

Lemma pwrs_validity gid l :
  Forall (λ c, valid_pwrs_of_command gid c) l ->
  pwrs_valid gid l.
Proof.
  intros Hpwrs.
  apply (pwrs_validity_step gid [] l); [done | apply pwrs_valid_nil].
Qed.

Lemma pts_nonzero_snoc l c :
  valid_pts_of_command c ->
  pts_nonzero l ->
  pts_nonzero (l ++ [c]).
Proof.
  intros Hpts Hnz.
  rewrite /pts_nonzero in Hnz.
  intros stmc tplsc ts wrsx Happly Hstm.
  destruct c; rewrite /apply_cmds foldl_snoc /= in Happly.
  { rewrite /apply_read in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    by destruct (tpls !! key) as [[vs tsprep] |];
    inversion Happly; subst stmc tplsc; eapply Hnz.
  }
  { simpl in Hpts.
    rewrite /apply_prepare in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid).
    { inversion Happly. subst stmc tplsc.
      by eapply Hnz.
    }
    destruct (validate _ _ _); inversion Happly; subst stmc tplsc; last first.
    { destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert_eq in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hnz.
    }
    rewrite /valid_ts in Hpts.
    destruct (decide (ts = tid)) as [-> | Hne]; first lia.
    rewrite lookup_insert_ne in Hstm; last done.
    by eapply Hnz.
  }
  { rewrite /apply_commit in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid) as [st |] eqn:Htid; last congruence.
    destruct st as [wrs | |]; inversion Happly; subst stmc tplsc.
    { destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert_eq in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hnz.
    }
    by eapply Hnz.
  }
  { rewrite /apply_abort in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid) as [st |] eqn:Htid; last first.
    { inversion Happly; subst stmc tplsc.
      { destruct (decide (ts = tid)) as [-> | Hne].
        { by rewrite lookup_insert_eq in Hstm. }
        rewrite lookup_insert_ne in Hstm; last done.
        by eapply Hnz.
      }
    }
    destruct st; inversion Happly; subst stmc tplsc.
    { destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert_eq in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hnz.
    }
    by eapply Hnz.
  }
Qed.

Lemma pts_consistent_snoc l c :
  pts_nonzero l ->
  (* TODO: check if we really need [pwrs_disjoint]. *)
  pwrs_disjoint l ->
  pts_consistent l ->
  pts_consistent (l ++ [c]).
Proof.
  intros Hnz Hdisj Hcst.
  rewrite /pts_consistent in Hcst.
  intros stmc tplsc ts wrsx keyx tpl Happly Hstm Htpls Hkey.
  destruct c; rewrite /apply_cmds foldl_snoc /= in Happly.
  { (* Case: [CmdRead] *)
    rewrite /apply_read in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (tpls !! key) as [[vs tsprep] |] eqn:Htpl; last done.
    inversion Happly; subst stmc tplsc.
    destruct (decide (keyx = key)) as [-> | Hne]; last first.
    { rewrite lookup_insert_ne in Htpls; last done. by eapply Hcst. }
    rewrite lookup_insert_eq /read in Htpls.
    specialize (Hcst _ _ _ _ _ _ Heq Hstm Htpl Hkey).
    simpl in Hcst.
    case_decide; by inversion Htpls.
  }
  { (* Case: [CmdPrep] *)
    rewrite /apply_prepare in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid).
    { (* Case: Status in table; no-op. *)
      inversion Happly. subst stmc tplsc.
      by eapply Hcst.
    }
    destruct (validate _ _ _) eqn:Hvd; inversion Happly; subst stmc tplsc; last first.
    { (* Case: Fail to acquire lock. *)
      destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert_eq in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hcst.
    }
    (* Case: Successfully acquire lock. *)
    destruct (decide (ts = tid)) as [-> | Hne]; last first.
    { (* Case: Not modify [key]. *)
      rewrite lookup_insert_ne in Hstm; last done.
      erewrite acquire_unmodified in Htpls; last first.
      { (* Prove [wrs] does not modify [key]. *)
        destruct (wrs !! keyx) as [v |] eqn:Hv; last done.
        unshelve epose proof (@validate_true_exists tid wrs tpls keyx _ Hvd) as ([h t] & Hht & [Hz _]).
        { done. }
        specialize (Hcst _ _ _ _ _ _ Heq Hstm Hht Hkey). subst ts.
        by specialize (Hnz _ _ _ _ Heq Hstm).
      }
      by eapply Hcst.
    }
    (* Case: Modify [key]. *)
    rewrite lookup_insert_eq in Hstm.
    inversion Hstm. subst wrsx.
    destruct (tpls !! keyx) as [tpl' |] eqn:Ht; last first.
    { rewrite elem_of_dom in Hkey.
      destruct Hkey as [v Hv].
      by rewrite /acquire lookup_merge Ht Hv /= in Htpls.
    }
    rewrite (acquire_modified _ Ht) in Htpls; last by rewrite -elem_of_dom.
    by inversion Htpls.
  }
  { (* Case: [CmdCmt] *)
    rewrite /apply_commit in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid) as [st |] eqn:Htid; last congruence.
    destruct st as [wrs | |]; last congruence.
    { (* Case: Prepared. *)
      inversion Happly. subst stmc tplsc.
      destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert_eq in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      specialize (Hdisj _ _ _ _ _ _ Heq Hne Hstm Htid).
      (* Solved with [Hkey] and [Hdisj]. *)
      assert (Hnotin : keyx ∉ dom wrs) by set_solver.
      rewrite multiwrite_unmodified in Htpls; last by rewrite not_elem_of_dom in Hnotin.
      by eapply Hcst.
    }
    { (* Case: Already committed; no-op. *)
      inversion Happly. subst stmc tplsc.
      by eapply Hcst.
    }
  }
  { (* Case: [CmdAbt] *)
    rewrite /apply_abort in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid) as [st |] eqn:Htid; last first.
    { (* Case: Direct abort (i.e., not prepared yet). *)
      inversion Happly. subst stmc tplsc.
      destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert_eq in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hcst.
    }
    destruct st; inversion Happly; subst stmc tplsc; last by eapply Hcst.
    (* Case: Prepared then abort. *)
    destruct (decide (ts = tid)) as [-> | Hne].
    { by rewrite lookup_insert_eq in Hstm. }
    rewrite lookup_insert_ne in Hstm; last done.
    specialize (Hdisj _ _ _ _ _ _ Heq Hne Hstm Htid).
    (* Solved with [Hkey] and [Hdisj]. *)
    assert (Hnotin : keyx ∉ dom wrs) by set_solver.
    rewrite release_unmodified in Htpls; last by rewrite not_elem_of_dom in Hnotin.
    by eapply Hcst.
  }
Qed.

Lemma pwrs_disjoint_snoc l c :
  pts_nonzero l ->
  pts_consistent l ->
  pwrs_disjoint l ->
  pwrs_disjoint (l ++ [c]).
Proof.
  intros Hnz Hcst Hdisj.
  rewrite /pwrs_disjoint in Hdisj.
  intros stmc tplsc ts1 ts2 wrs1 wrs2 Happly Hne Hstm1 Hstm2.
  destruct c; rewrite /apply_cmds foldl_snoc /= in Happly.
  { (* Case: [CmdRead] *)
    rewrite /apply_read in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    by destruct (tpls !! key) as [[vs tsprep] |];
      inversion Happly; subst stmc tplsc; eapply Hdisj.
  }
  { (* Case: [CmdPrep] *)
    rewrite /apply_prepare in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid).
    { (* Case: Status in table; no-op. *)
      inversion Happly. subst stmc tplsc.
      by eapply Hdisj.
    }
    destruct (validate _ _ _) eqn:Hvd; inversion Happly; subst stmc tplsc; last first.
    { (* Case: Fail to acquire lock. *)
      destruct (decide (tid = ts1)) as [-> | Hne1].
      { by rewrite lookup_insert_eq in Hstm1. }
      destruct (decide (tid = ts2)) as [-> | Hne2].
      { by rewrite lookup_insert_eq in Hstm2. }
      rewrite lookup_insert_ne in Hstm1; last done.
      rewrite lookup_insert_ne in Hstm2; last done.
      (* Remove them to make automation choose the right hypothesis. *)
      clear Hne1 Hne2.
      by eapply Hdisj.
    }
    (* Case: Successfully acquire lock. *)
    destruct (decide (tid = ts1)) as [-> | Hne1].
    { rewrite lookup_insert_eq in Hstm1.
      inversion Hstm1. subst wrs.
      rewrite lookup_insert_ne in Hstm2; last done.
      intros k Hwrs1 Hwrs2.
      rewrite elem_of_dom in Hwrs1.
      destruct (validate_true_exists _ Hwrs1 Hvd) as ([h t] & Hht & [Hz _]).
      specialize (Hcst _ _ _ _ _ _ Heq Hstm2 Hht Hwrs2). subst ts2.
      by specialize (Hnz _ _ _ _ Heq Hstm2).
    }
    destruct (decide (tid = ts2)) as [-> | Hne2].
    { (* symmetric to above *)
      rewrite lookup_insert_eq in Hstm2.
      inversion Hstm2. subst wrs.
      rewrite lookup_insert_ne in Hstm1; last done.
      intros k Hwrs1 Hwrs2.
      rewrite elem_of_dom in Hwrs2.
      destruct (validate_true_exists _ Hwrs2 Hvd) as ([h t] & Hht & [Hz _]).
      specialize (Hcst _ _ _ _ _ _ Heq Hstm1 Hht Hwrs1). subst ts1.
      by specialize (Hnz _ _ _ _ Heq Hstm1).
    }
    rewrite lookup_insert_ne in Hstm1; last done.
    rewrite lookup_insert_ne in Hstm2; last done.
    clear Hne1 Hne2.
    by eapply Hdisj.
  }
  { (* Case: [CmdCmt] *)
    rewrite /apply_commit in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid) as [st |] eqn:Htid; last congruence.
    destruct st as [wrs | |];
      inversion Happly; subst stmc tplsc; last by eapply Hdisj.
    destruct (decide (tid = ts1)) as [-> | Hne1].
    { by rewrite lookup_insert_eq in Hstm1. }
    destruct (decide (tid = ts2)) as [-> | Hne2].
    { by rewrite lookup_insert_eq in Hstm2. }
    rewrite lookup_insert_ne in Hstm1; last done.
    rewrite lookup_insert_ne in Hstm2; last done.
    clear Hne1 Hne2.
    by eapply Hdisj.
  }
  { (* Case: [CmdAbt] *)
    rewrite /apply_abort in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid) as [st |] eqn:Htid; last first.
    { inversion Happly; subst stmc tplsc.
      destruct (decide (tid = ts1)) as [-> | Hne1].
      { by rewrite lookup_insert_eq in Hstm1. }
      destruct (decide (tid = ts2)) as [-> | Hne2].
      { by rewrite lookup_insert_eq in Hstm2. }
      rewrite lookup_insert_ne in Hstm1; last done.
      rewrite lookup_insert_ne in Hstm2; last done.
      clear Hne1 Hne2.
      by eapply Hdisj.
    }
    destruct st; inversion Happly; subst stmc tplsc.
    { destruct (decide (tid = ts1)) as [-> | Hne1].
      { by rewrite lookup_insert_eq in Hstm1. }
      destruct (decide (tid = ts2)) as [-> | Hne2].
      { by rewrite lookup_insert_eq in Hstm2. }
      rewrite lookup_insert_ne in Hstm1; last done.
      rewrite lookup_insert_ne in Hstm2; last done.
      clear Hne1 Hne2.
      by eapply Hdisj.
    }
    by eapply Hdisj.
  }
Qed.

Lemma pts_nonzero_nil :
  pts_nonzero [].
Proof.
  intros stm tpls ts wrs Happly Hstm.
  rewrite /apply_cmds /= /init_rpst in Happly.
  set_solver.
Qed.

Lemma pts_consistent_nil :
  pts_consistent [].
Proof.
  intros stm tpls ts wrs key tpl Happly Hstm Htpls Hkey.
  rewrite /apply_cmds /= /init_rpst in Happly.
  set_solver.
Qed.

Lemma pwrs_disjoint_nil :
  pwrs_disjoint [].
Proof.
  intros stmc tplsc ts1 ts2 wrs1 wrs2 Happly Hne Hts1 Hts2.
  rewrite /apply_cmds /= /init_rpst in Happly.
  set_solver.
Qed.

Lemma pts_consistency_step l1 l2 :
  Forall (λ c, valid_pts_of_command c) l2 ->
  pts_nonzero l1 ->
  pwrs_disjoint l1 ->
  pts_consistent l1 ->
  pts_consistent (l1 ++ l2).
Proof.
  intros Hpts.
  generalize dependent l1.
  induction l2 as [| c l2 IH].
  { intros l1. by rewrite app_nil_r. }
  rewrite Forall_cons in Hpts. destruct Hpts as [Hc Hl2].
  intros l1 Hnz Hdisj Hcst.
  rewrite cons_middle app_assoc.
  apply IH; first done.
  { by apply pts_nonzero_snoc. }
  { by apply pwrs_disjoint_snoc. }
  { by apply pts_consistent_snoc. }
Qed.

Lemma pts_consistency l :
  Forall (λ c, valid_pts_of_command c) l ->
  pts_consistent l.
Proof.
  intros Hpts.
  apply (pts_consistency_step [] l); first done.
  { apply pts_nonzero_nil. }
  { apply pwrs_disjoint_nil. }
  { apply pts_consistent_nil. }
Qed.
