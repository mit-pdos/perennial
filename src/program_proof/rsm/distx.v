From Perennial.program_proof Require Export grove_prelude.
From Perennial.program_logic Require Export atomic. (* prefer the ncfupd atomics *)

Definition dbkey := string.
Definition dbval := option string.
Definition dbhist := list dbval.
Definition dbtpl := (dbhist * nat)%type.
Definition dbmod := (dbkey * dbval)%type.
(* Canonical Structure dbvalO := leibnizO dbval. *)
Definition dbmap := gmap dbkey dbval.
Definition dbkmod := gmap nat dbval.

Definition dbval_to_val (v : dbval) : val :=
  match v with
  | Some s => (#true, (#(LitString s), #()))
  | None => (#false, (zero_val stringT, #()))
  end.

Definition fstring := {k : string | (String.length k < 2 ^ 64)%nat}.

#[local]
Instance fstring_finite :
  finite.Finite fstring.
Admitted.

(* Definition keys_all : gset string := fin_to_set fstring. *)
Definition keys_all : gset string.
Admitted.

Definition groupid := nat.
Definition gids_all := seq 0 2.

Definition key_to_group (key : dbkey) : groupid.
Admitted.

Definition wrs_group gid (wrs : dbmap) :=
  filter (λ x, key_to_group x.1 = gid) wrs.

Definition valid_ts (ts : nat) := ts ≠ O.

Definition valid_wrs (wrs : dbmap) := dom wrs ⊆ keys_all.

Definition key_in_group (gid : groupid) (key : dbkey) :=
  key_to_group key = gid.

Definition wrs_in_group (gid : groupid) (wrs : dbmap) :=
  set_Forall (λ k, key_in_group gid k) (dom wrs).

Definition tpls_group gid (tpls : gmap dbkey dbtpl) :=
  filter (λ x, key_to_group x.1 = gid) tpls.

Lemma tpls_group_dom {gid tpls0 tpls1} :
  dom tpls0 = dom tpls1 ->
  dom (tpls_group gid tpls0) = dom (tpls_group gid tpls1).
Proof.
Admitted.

Definition keys_group gid (keys : gset dbkey) :=
  filter (λ x, key_to_group x = gid) keys.

Definition keys_except_group gid (keys : gset dbkey) :=
  filter (λ x, key_to_group x ≠ gid) keys.

Lemma keys_group_tpls_group_dom {gid keys tpls} :
  dom tpls = keys ↔
  dom (tpls_group gid tpls) = keys_group gid keys.
Admitted.

Lemma key_to_group_tpls_group key gid tpls :
  key ∈ dom (tpls_group gid tpls) ->
  key_to_group key = gid.
Admitted.

(* Participant groups. *)
Definition ptgroups (keys : gset dbkey) : gset groupid :=
  set_map key_to_group keys.

Lemma elem_of_ptgroups key keys :
  key ∈ keys ->
  key_to_group key ∈ ptgroups keys.
Proof. apply elem_of_map_2. Qed.

Lemma wrs_group_elem_of_ptgroups gid pwrs wrs :
  pwrs ≠ ∅ ->
  pwrs = wrs_group gid wrs ->
  gid ∈ ptgroups (dom wrs).
Proof.
  intros Hnz Hpwrs.
  apply map_choose in Hnz.
  destruct Hnz as (k & v & Hkv).
  rewrite /ptgroups elem_of_map.
  exists k.
  rewrite Hpwrs map_lookup_filter_Some /= in Hkv.
  destruct Hkv as [Hkv Hgid].
  split; first done.
  by eapply elem_of_dom_2.
Qed.

Inductive command :=
| CmdPrep (tid : nat) (wrs : dbmap)
| CmdCmt (tid : nat)
| CmdAbt (tid : nat)
| CmdRead (tid : nat) (key : dbkey).

#[local]
Instance command_eq_decision :
  EqDecision command.
Proof. solve_decision. Qed.

#[local]
Instance command_countable :
  Countable command.
Admitted.

Definition dblog := list command.

(* Transaction status on replica *)
Inductive txnst :=
| StPrepared (wrs : dbmap)
| StCommitted
| StAborted.

Definition txnst_to_u64 (s : txnst) :=
  match s with
  | StPrepared wrs => (U64 1)
  | StCommitted => (U64 2)
  | StAborted => (U64 3)
  end.

(* Transaction result *)
Inductive txnres :=
| ResCommitted (wrs : dbmap)
| ResAborted.

(* Replica state *)
Inductive rpst :=
| State (txns : gmap nat txnst) (tpls : gmap dbkey dbtpl)
| Stuck.

Inductive acquiring :=
| Acquired (tpls : gmap dbkey dbtpl)
| NotAcquired.

Definition validate_key (tid : nat) (wr : option dbval) (tpl : option dbtpl) :=
  match wr, tpl with
  | Some _, Some (vs, tsprep) => Some (bool_decide (tsprep = O ∧ length vs ≤ tid)%nat)
  | _, _ => None
  end.

Definition validate (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  map_fold (λ _, andb) true (merge (validate_key tid) wrs tpls).

Lemma validate_true {tid wrs tpls key} :
  is_Some (wrs !! key) ->
  validate tid wrs tpls = true ->
  ∃ l, tpls !! key = Some (l, O) ∧ (length l ≤ tid)%nat.
Admitted.

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
Admitted.

Lemma acquire_unmodified {tid wrs tpls key} :
  wrs !! key = None ->
  (acquire tid wrs tpls) !! key = tpls !! key.
Admitted.

Lemma acquire_modified {tid wrs tpls key tpl} :
  is_Some (wrs !! key) ->
  tpls !! key = Some tpl ->
  (acquire tid wrs tpls) !! key = Some (tpl.1, tid).
Admitted.

Definition try_acquire (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  if validate tid wrs tpls then Acquired (acquire tid wrs tpls) else NotAcquired.

Definition apply_prepare st (tid : nat) (wrs : dbmap) :=
  match st with
  | State stm tpls =>
      match stm !! tid with
      | Some _ => st
      | None =>  match try_acquire tid wrs tpls with
                | Acquired tpls' => State (<[ tid := StPrepared wrs ]> stm) tpls'
                | NotAcquired => State (<[ tid := StAborted ]> stm) tpls
                end
      end
  | Stuck => Stuck
  end.

(* TODO: reorder [x] and [n]. *)
Definition extend {X} (x : X) (n : nat) (l : list X) :=
  l ++ replicate (n - length l) x.

(* TODO *)
Definition last_extend {A} (n : nat) (l : list A) := l.

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

Definition multiwrite (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  merge (multiwrite_key tid) wrs tpls.

Lemma multiwrite_dom {tid wrs tpls} :
  dom (multiwrite tid wrs tpls) = dom tpls.
Admitted.

Lemma multiwrite_unmodified {tid wrs tpls key} :
  wrs !! key = None ->
  (multiwrite tid wrs tpls) !! key = tpls !! key.
Proof.
  intros Hlookup.
  rewrite lookup_merge Hlookup /=.
  by destruct (tpls !! key) as [t |] eqn:Ht.
Qed.

Lemma multiwrite_tuples_empty tid wrs :
  multiwrite tid wrs ∅ = ∅.
Proof.
  apply map_eq. intros k.
  rewrite lookup_merge lookup_empty.
  by destruct (wrs !! k) as [v |] eqn:Hv; rewrite Hv.
Qed.

Lemma multiwrite_lookup_Some tid wrs tpls k t :
  tpls !! k = Some t ->
  multiwrite tid wrs tpls !! k = Some (multiwrite_key_tpl tid (wrs !! k) t).
Proof.
  intros Hlookup.
  rewrite lookup_merge Hlookup.
  by destruct (wrs !! k) as [y |] eqn:Hy; rewrite Hy /=.
Qed.

Lemma multiwrite_lookup_None tid wrs tpls k :
  tpls !! k = None ->
  multiwrite tid wrs tpls !! k = None.
Proof.
  intros Hlookup.
  rewrite lookup_merge Hlookup.
  by destruct (wrs !! k) as [y |] eqn:Hy; rewrite Hy /=.
Qed.

Lemma multiwrite_difference_distr {tid wrs tpls tplsd} :
  multiwrite tid wrs (tpls ∖ tplsd) =
  multiwrite tid wrs tpls ∖ multiwrite tid wrs tplsd.
Proof.
  apply map_eq. intros k.
  destruct (tpls !! k) as [v |] eqn:Hv.
  - destruct (tplsd !! k) as [vd |] eqn:Hvd.
    + rewrite multiwrite_lookup_None; last by rewrite lookup_difference Hvd.
      rewrite lookup_difference.
      by erewrite multiwrite_lookup_Some.
    + rewrite lookup_merge lookup_difference Hvd Hv.
      rewrite lookup_difference multiwrite_lookup_None; last done.
      by rewrite lookup_merge Hv.
  - destruct (tplsd !! k) as [vd |] eqn:Hvd.
    + rewrite multiwrite_lookup_None; last by rewrite lookup_difference Hvd.
      rewrite lookup_difference.
      by erewrite multiwrite_lookup_Some.
    + rewrite multiwrite_lookup_None; last by rewrite lookup_difference Hvd Hv.
      apply (multiwrite_lookup_None tid wrs) in Hvd.
      by rewrite lookup_difference Hvd multiwrite_lookup_None.
Qed.

Lemma multiwrite_mono tid wrs tpls0 tpls1 :
  tpls0 ⊆ tpls1 ->
  multiwrite tid wrs tpls0 ⊆ multiwrite tid wrs tpls1.
Proof.
  intros Hsubseteq.
  rewrite map_subseteq_spec.
  intros k t Htpls0.
  destruct (tpls0 !! k) as [v |] eqn:Hv; last first.
  { apply (multiwrite_lookup_None tid wrs) in Hv. congruence. }
  rewrite map_subseteq_spec in Hsubseteq.
  specialize (Hsubseteq _ _ Hv).
  rewrite lookup_merge Hv in Htpls0.
  by rewrite lookup_merge Hsubseteq.
Qed.

Lemma multiwrite_tpls_group_commute tid wrs tpls gid :
  multiwrite tid wrs (tpls_group gid tpls) = tpls_group gid (multiwrite tid wrs tpls).
Proof.
  induction tpls as [| k t m Hlookup IH] using map_ind.
  { by rewrite /tpls_group map_filter_empty multiwrite_tuples_empty map_filter_empty. }
  rewrite /multiwrite /tpls_group.
  rewrite /multiwrite /tpls_group in IH.
  destruct (decide (key_to_group k = gid)) as [Heq | Hne].
  - rewrite map_filter_insert_True; last done.
    erewrite <- insert_merge_r; last done.
    erewrite <- insert_merge_r; last done.
    rewrite map_filter_insert_True; last done.
    by rewrite IH.
  - rewrite map_filter_insert_False; last done.
    rewrite delete_notin; last done.
    erewrite <- insert_merge_r; last done.
    rewrite map_filter_insert_False; last done.
    rewrite delete_notin; last by eapply multiwrite_lookup_None in Hlookup.
    by rewrite IH.
Qed.

Definition apply_commit st (tid : nat) :=
  match st with
  | State stm tpls =>
      match stm !! tid with
      | Some StCommitted => st
      | Some (StPrepared wrs) => State (<[ tid := StCommitted ]> stm) (multiwrite tid wrs tpls)
      | _ => Stuck
      end
  | Stuck => Stuck
  end.

Definition release_key (tid : nat) (wr : option dbval) (tpl : option dbtpl) :=
  match wr, tpl with
  | None, Some _ => tpl
  | Some _, Some (vs, _) => Some (vs, O)
  | _, _ => None
  end.

Definition release (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  merge (release_key tid) wrs tpls.

Lemma release_unmodified {tid wrs tpls key} :
  wrs !! key = None ->
  (release tid wrs tpls) !! key = tpls !! key.
Proof.
  intros Hlookup.
  rewrite lookup_merge Hlookup /=.
  by destruct (tpls !! key) as [t |] eqn:Ht.
Qed.

Definition apply_abort st (tid : nat) :=
  match st with
  | State stm tpls =>
      match stm !! tid with
      | Some StAborted => st
      | Some (StPrepared wrs) => State (<[ tid := StAborted ]> stm) (release tid wrs tpls)
      | None => State (<[ tid := StAborted ]> stm) tpls
      | _ => Stuck
      end
  | Stuck => Stuck
  end.

Definition read (tid : nat) (vs : list dbval) (tsprep : nat) :=
  if decide (tsprep = 0 ∨ tid < tsprep)%nat
  then (last_extend tid vs, tsprep)
  else (vs, tsprep).

Definition apply_read st (tid : nat) (key : dbkey) :=
  match st with
  | State stm tpls =>
      match tpls !! key with
      | Some (vs, tsprep) => State stm (<[ key := (read tid vs tsprep) ]> tpls)
      | None => st
      end
  | Stuck => Stuck
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

Lemma apply_cmds_dom log :
  ∀ stm tpls,
  apply_cmds log = State stm tpls ->
  dom tpls = keys_all.
Admitted.

(** Note: RSM invariants can either be defined as properties about [apply_cmds],
or explicit invariants materialized in [group_inv]. The first form gives a
minimal set of invariants and allow replicas to deduce those properties (not
sure if the second matters), but the proofs can be a bit repetitive and hard to
comprehend. The second form is more verbose (and weaker since it does not
directly allows replica to deduce the invariants), but might yield more
informative lemmas and proofs. *)

Definition pts_consistent log :=
  ∀ stm tpls ts wrs key tpl,
  apply_cmds log = State stm tpls ->
  stm !! ts = Some (StPrepared wrs) ->
  tpls !! key = Some tpl ->
  key ∈ dom wrs ->
  tpl.2 = ts.

Definition pts_disjoint log :=
  ∀ stm tpls ts1 ts2 wrs1 wrs2,
  apply_cmds log = State stm tpls ->
  ts1 ≠ ts2 ->
  stm !! ts1 = Some (StPrepared wrs1) ->
  stm !! ts2 = Some (StPrepared wrs2) ->
  dom wrs1 ## dom wrs2.

Definition pts_nonzero log :=
  ∀ stm tpls ts wrs,
  apply_cmds log = State stm tpls ->
  stm !! ts = Some (StPrepared wrs) ->
  ts ≠ O.

Definition pwrs_valid gid log :=
  ∀ stm tpls ts wrs,
  apply_cmds log = State stm tpls ->
  stm !! ts = Some (StPrepared wrs) ->
  valid_wrs wrs ∧ wrs_in_group gid wrs.

Definition valid_pts c :=
  match c with
  | CmdPrep tid wrs => valid_ts tid
  | _ => True
  end.

Definition valid_pwrs gid c :=
  match c with
  | CmdPrep tid wrs => valid_wrs wrs ∧ wrs_in_group gid wrs
  | _ => True
  end.

Lemma pts_nonzero_snoc l c :
  valid_pts c ->
  pts_nonzero l ->
  pts_nonzero (l ++ [c]).
Proof.
  intros Hpts Hnz.
  rewrite /pts_nonzero in Hnz.
  intros stmc tplsc ts wrsx Happly Hstm.
  destruct c; rewrite /apply_cmds foldl_snoc /= in Happly.
  { simpl in Hpts.
    rewrite /apply_prepare in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid).
    { inversion Happly. subst stmc tplsc.
      by eapply Hnz.
    }
    destruct (try_acquire _ _ _) as [tpls' |] eqn:Hacq;
      inversion Happly; subst stmc tplsc; last first.
    { destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hnz.
    }
    destruct (decide (ts = tid)) as [-> | Hne]; first done.
    rewrite lookup_insert_ne in Hstm; last done.
    by eapply Hnz.
  }
  { rewrite /apply_commit in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid) as [st |] eqn:Htid; last congruence.
    destruct st as [wrs | |]; inversion Happly; subst stmc tplsc.
    { destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert in Hstm. }
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
        { by rewrite lookup_insert in Hstm. }
        rewrite lookup_insert_ne in Hstm; last done.
        by eapply Hnz.
      }
    }
    destruct st; inversion Happly; subst stmc tplsc.
    { destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hnz.
    }
    by eapply Hnz.
  }
  { rewrite /apply_read in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    by destruct (tpls !! key) as [[vs tsprep] |];
    inversion Happly; subst stmc tplsc; eapply Hnz.
  }
Qed.

Lemma pts_consistent_snoc l c :
  pts_nonzero l ->
  pts_disjoint l ->
  pts_consistent l ->
  pts_consistent (l ++ [c]).
Proof.
  intros Hnz Hdisj Hcst.
  rewrite /pts_consistent in Hcst.
  intros stmc tplsc ts wrsx keyx tpl Happly Hstm Htpls Hkey.
  destruct c; rewrite /apply_cmds foldl_snoc /= in Happly.
  { (* Case: [CmdPrep] *)
    rewrite /apply_prepare in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid).
    { (* Case: Status in table; no-op. *)
      inversion Happly. subst stmc tplsc.
      by eapply Hcst.
    }
    destruct (try_acquire _ _ _) as [tpls' |] eqn:Hacq;
      inversion Happly; subst stmc tplsc; last first.
    { (* Case: Fail to acquire lock. *)
      destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hcst.
    }
    (* Case: Successfully acquire lock. *)
    rewrite /try_acquire in Hacq.
    destruct (validate _ _ _) eqn:Hvd; last done.
    inversion Hacq. subst tpls'.
    destruct (decide (ts = tid)) as [-> | Hne]; last first.
    { (* Case: Not modify [key]. *)
      rewrite lookup_insert_ne in Hstm; last done.
      erewrite acquire_unmodified in Htpls; last first.
      { (* Prove [wrs] does not modify [key]. *)
        destruct (wrs !! keyx) as [v |] eqn:Hv; last done.
        unshelve epose proof (@validate_true tid wrs tpls keyx _ Hvd) as [h [Ht _]].
        { done. }
        specialize (Hcst _ _ _ _ _ _ Heq Hstm Ht Hkey).
        by specialize (Hnz _ _ _ _ Heq Hstm).
      }
      by eapply Hcst.
    }
    (* Case: Modify [key]. *)
    rewrite lookup_insert in Hstm.
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
      { by rewrite lookup_insert in Hstm. }
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
      { by rewrite lookup_insert in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hcst.
    }
    destruct st; inversion Happly; subst stmc tplsc; last by eapply Hcst.
    (* Case: Prepared then abort. *)
    destruct (decide (ts = tid)) as [-> | Hne].
    { by rewrite lookup_insert in Hstm. }
    rewrite lookup_insert_ne in Hstm; last done.
    specialize (Hdisj _ _ _ _ _ _ Heq Hne Hstm Htid).
    (* Solved with [Hkey] and [Hdisj]. *)
    assert (Hnotin : keyx ∉ dom wrs) by set_solver.
    rewrite release_unmodified in Htpls; last by rewrite not_elem_of_dom in Hnotin.
    by eapply Hcst.
  }
  { (* Case: [CmdRead] *)
    rewrite /apply_read in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (tpls !! key) as [[vs tsprep] |] eqn:Htpl;
      inversion Happly; subst stmc tplsc; last by eapply Hcst.
    destruct (decide (keyx = key)) as [-> | Hne]; last first.
    { rewrite lookup_insert_ne in Htpls; last done. by eapply Hcst. }
    rewrite lookup_insert /read in Htpls.
    specialize (Hcst _ _ _ _ _ _ Heq Hstm Htpl Hkey).
    simpl in Hcst.
    case_decide; by inversion Htpls.
  }
Qed.

Lemma pts_disjoint_snoc l c :
  pts_nonzero l ->
  pts_consistent l ->
  pts_disjoint l ->
  pts_disjoint (l ++ [c]).
Proof.
  intros Hnz Hcst Hdisj.
  rewrite /pts_disjoint in Hdisj.
  intros stmc tplsc ts1 ts2 wrs1 wrs2 Happly Hne Hstm1 Hstm2.
  destruct c; rewrite /apply_cmds foldl_snoc /= in Happly.
  { (* Case: [CmdPrep] *)
    rewrite /apply_prepare in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    destruct (stm !! tid).
    { (* Case: Status in table; no-op. *)
      inversion Happly. subst stmc tplsc.
      by eapply Hdisj.
    }
    destruct (try_acquire _ _ _) as [tpls' |] eqn:Hacq;
      inversion Happly; subst stmc tplsc; last first.
    { (* Case: Fail to acquire lock. *)
      destruct (decide (tid = ts1)) as [-> | Hne1].
      { by rewrite lookup_insert in Hstm1. }
      destruct (decide (tid = ts2)) as [-> | Hne2].
      { by rewrite lookup_insert in Hstm2. }
      rewrite lookup_insert_ne in Hstm1; last done.
      rewrite lookup_insert_ne in Hstm2; last done.
      (* Remove them to make automation choose the right hypothesis. *)
      clear Hne1 Hne2.
      by eapply Hdisj.
    }
    (* Case: Successfully acquire lock. *)
    rewrite /try_acquire in Hacq.
    destruct (validate _ _ _) eqn:Hvd; last done.
    inversion Hacq. subst tpls'.
    destruct (decide (tid = ts1)) as [-> | Hne1].
    { rewrite lookup_insert in Hstm1.
      inversion Hstm1. subst wrs.
      rewrite lookup_insert_ne in Hstm2; last done.
      intros k Hwrs1 Hwrs2.
      rewrite elem_of_dom in Hwrs1.
      destruct (validate_true Hwrs1 Hvd) as (h & Htpls & _).
      specialize (Hcst _ _ _ _ _ _ Heq Hstm2 Htpls Hwrs2).
      by specialize (Hnz _ _ _ _ Heq Hstm2).
    }
    destruct (decide (tid = ts2)) as [-> | Hne2].
    { (* symmetric to above *)
      rewrite lookup_insert in Hstm2.
      inversion Hstm2. subst wrs.
      rewrite lookup_insert_ne in Hstm1; last done.
      intros k Hwrs1 Hwrs2.
      rewrite elem_of_dom in Hwrs2.
      destruct (validate_true Hwrs2 Hvd) as (h & Htpls & _).
      specialize (Hcst _ _ _ _ _ _ Heq Hstm1 Htpls Hwrs1).
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
    { by rewrite lookup_insert in Hstm1. }
    destruct (decide (tid = ts2)) as [-> | Hne2].
    { by rewrite lookup_insert in Hstm2. }
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
      { by rewrite lookup_insert in Hstm1. }
      destruct (decide (tid = ts2)) as [-> | Hne2].
      { by rewrite lookup_insert in Hstm2. }
      rewrite lookup_insert_ne in Hstm1; last done.
      rewrite lookup_insert_ne in Hstm2; last done.
      clear Hne1 Hne2.
      by eapply Hdisj.
    }
    destruct st; inversion Happly; subst stmc tplsc.
    { destruct (decide (tid = ts1)) as [-> | Hne1].
      { by rewrite lookup_insert in Hstm1. }
      destruct (decide (tid = ts2)) as [-> | Hne2].
      { by rewrite lookup_insert in Hstm2. }
      rewrite lookup_insert_ne in Hstm1; last done.
      rewrite lookup_insert_ne in Hstm2; last done.
      clear Hne1 Hne2.
      by eapply Hdisj.
    }
    by eapply Hdisj.
  }
  { (* Case: [CmdRead] *)
    rewrite /apply_read in Happly.
    destruct (foldl _ _ _) as [stm tpls |] eqn:Heq; last congruence.
    by destruct (tpls !! key) as [[vs tsprep] |];
      inversion Happly; subst stmc tplsc; eapply Hdisj.
  }
Qed.

Lemma pts_nonzero_empty :
  pts_nonzero [].
Proof.
  intros stm tpls ts wrs Happly Hstm.
  rewrite /apply_cmds /= /init_rpst in Happly.
  set_solver.
Qed.

Lemma pts_consistent_empty :
  pts_consistent [].
Proof.
  intros stm tpls ts wrs key tpl Happly Hstm Htpls Hkey.
  rewrite /apply_cmds /= /init_rpst in Happly.
  set_solver.
Qed.

Lemma pts_disjoint_empty :
  pts_disjoint [].
Proof.
  intros stmc tplsc ts1 ts2 wrs1 wrs2 Happly Hne Hts1 Hts2.
  rewrite /apply_cmds /= /init_rpst in Happly.
  set_solver.
Qed.

Lemma pts_consistency_step l1 l2 :
  Forall (λ c, valid_pts c) l2 ->
  pts_nonzero l1 ->
  pts_disjoint l1 ->
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
  { by apply pts_disjoint_snoc. }
  { by apply pts_consistent_snoc. }
Qed.

Lemma pts_consistency l :
  Forall (λ c, valid_pts c) l ->
  pts_consistent l.
Proof.
  intros Hpts.
  apply (pts_consistency_step [] l); first done.
  { apply pts_nonzero_empty. }
  { apply pts_disjoint_empty. }
  { apply pts_consistent_empty. }
Qed.

Lemma pwrs_validity gid l :
  Forall (λ c, valid_pwrs gid c) l ->
  pwrs_valid gid l.
Proof.
Admitted.

Lemma set_Forall_Forall_subsume `{Countable A} (l : list A) (s : gset A) P :
  set_Forall P s ->
  Forall (λ x, x ∈ s) l ->
  Forall P l.
Proof. do 2 rewrite Forall_forall. intros HP Hl x Hin. by auto. Qed.

(* TODO: probably don't need these. *)
Definition apply_cmds_stm (cmds : list command) :=
  match apply_cmds cmds with
  | State stm _ => Some stm
  | _ => None
  end.

Lemma apply_cmd_stuck log :
  foldl apply_cmd Stuck log = Stuck.
Admitted.

Lemma txnst_committed_mono_apply_cmd log ts :
  ∀ stm stm' tpls tpls',
  stm !! ts = Some StCommitted ->
  foldl apply_cmd (State stm tpls) log = State stm' tpls' ->
  stm' !! ts = Some StCommitted.
Proof.
  induction log as [| c log' IH].
  { intros stm stm' tpls tpls' Hcmt Happly. inversion Happly. by subst stm'. }
  intros stm stm' tpls tpls' Hcmt Happly.
  destruct c as [tid wrs | tid | tid |tid key]; simpl in Happly.
  { (* Case: [CmdPrep] *)
    destruct (decide (tid = ts)) as [-> | Hneq].
    { rewrite Hcmt in Happly. by eapply IH. }
    destruct (stm !! tid).
    { by eapply IH. }
    destruct (try_acquire _ _ _).
    { eapply IH; last apply Happly. by rewrite lookup_insert_ne. }
    eapply IH; last apply Happly. by rewrite lookup_insert_ne.
  }
  { (* Case: [CmdCmt] *)
    destruct (decide (tid = ts)) as [-> | Hneq].
    { rewrite Hcmt in Happly. by eapply IH. }
    destruct (stm !! tid).
    { destruct t.
      { eapply IH; last apply Happly. by rewrite lookup_insert_ne. }
      { by eapply IH. }
      by rewrite apply_cmd_stuck in Happly.
    }
    by rewrite apply_cmd_stuck in Happly.
  }
  { (* Case: [CmdAbt] *)
    destruct (decide (tid = ts)) as [-> | Hneq].
    { rewrite Hcmt in Happly. by rewrite apply_cmd_stuck in Happly. }
    destruct (stm !! tid).
    { destruct t.
      { eapply IH; last apply Happly. by rewrite lookup_insert_ne. }
      { by rewrite apply_cmd_stuck in Happly. }
      by eapply IH.
    }
    eapply IH; last apply Happly. by rewrite lookup_insert_ne.
  }
  { (* Case: [CmdRead] *)
    destruct (tpls !! key) as [[vs tsprep] |]; by eapply IH.
  }
Qed.

Lemma apply_cmds_txnst_mono {cmds ts} :
  ∀ cmdsp stm stmp,
  prefix cmdsp cmds ->
  apply_cmds_stm cmds = Some stm ->
  apply_cmds_stm cmdsp = Some stmp ->
  stm !! ts = None ->
  stmp !! ts = None.
Proof.
  induction cmds as [| c l IH].
  { admit. }
  intros cmdsp stm stmp Hprefix Hcmds Hcmdsp Hstm.
  rewrite /apply_cmds_stm /apply_cmds in Hcmds.
  simpl in Hcmds.
Admitted.
(* TODO: probably don't need these. *)
  
Inductive action :=
| ActCmt (tid : nat) (wrs : dbmap)
| ActRead (tid : nat) (key : dbkey).

Definition diff_by_cmtd
  (repl cmtd : list dbval) (tmods : dbkmod) (ts : nat) :=
  match tmods !! ts with
  | Some v => cmtd = last_extend ts repl ++ [v]
  | None => (∃ ts', repl = last_extend ts' cmtd) ∧
           (ts ≠ O -> length repl ≤ ts)%nat
  end.

Definition diff_by_lnrz (cmtd lnrz : list dbval) (txns : dbkmod) : Prop.
Admitted.

Definition conflict_free (acts : list action) (txns : gmap nat dbmap) : Prop.
Admitted.

Definition conflict_past (acts_future acts_past : list action) (txns : gmap nat dbmap) : Prop.
Admitted.

Definition repl_impl_cmtd (acts : list action) (cmds : list command) :=
  ∀ ts, CmdCmt ts ∈ cmds → ∃ wrs, ActCmt ts wrs ∈ acts.

Definition cmtd_impl_prep (resm : gmap nat txnres) (wrsm : gmap nat dbmap) :=
  ∀ ts, match resm !! ts with
        | Some (ResCommitted wrs) => wrsm !! ts = Some wrs
        | _ => True
        end.

Definition past_commit (acts : list action) (resm : gmap nat txnres) :=
  ∀ ts wrs, ActCmt ts wrs ∈ acts → resm !! ts = Some (ResCommitted wrs).

(* TODO: define this in terms of [hist_repl_at]. *)
Definition has_extended ts key log :=
  match apply_cmds log with
  | State _ tpls => match tpls !! key with
                   | Some (vs, _) => (ts < length vs)%nat
                   | _ => False
                   end
  | _ => False
  end.

Definition past_read (acts : list action) (log : list command) :=
  ∀ ts key, ActRead ts key ∈ acts → has_extended ts key log.

Definition log_txnst (ts : nat) (st : txnst) (log : dblog) :=
  match apply_cmds log with
  | State stm _ => stm !! ts = Some st
  | _ => False
  end.

Definition lookup_twice
  {V} `{Countable K1} `{Countable K2}
  (m : gmap K1 (gmap K2 V)) (k1 : K1) (k2 : K2) :=
  match m !! k1 with
  | Some im => im !! k2
  | None => None
  end.

Definition tmods_kmods_consistent (tmods : gmap nat dbmap) (kmods : gmap dbkey dbkmod) :=
  ∀ t k, lookup_twice tmods t k = lookup_twice kmods k t.

Definition res_to_tmod (res : txnres) :=
  match res with
  | ResCommitted wrs => Some wrs
  | ResAborted => None
  end.

Definition resm_to_tmods (resm : gmap nat txnres) :=
  omap res_to_tmod resm.

Lemma tmods_present_kmod_absent tmods kmods kmod ts wrs key :
  tmods !! ts = Some wrs ->
  wrs !! key = None ->
  kmods !! key = Some kmod ->
  tmods_kmods_consistent tmods kmods ->
  kmod !! ts = None.
Proof.
  intros Htmods Hwrs Hkmods Hc.
  specialize (Hc ts key).
  by rewrite /lookup_twice Htmods Hkmods Hwrs in Hc.
Qed.

Lemma tmods_present_kmod_present tmods kmods kmod ts wrs key value :
  tmods !! ts = Some wrs ->
  wrs !! key = Some value ->
  kmods !! key = Some kmod ->
  tmods_kmods_consistent tmods kmods ->
  kmod !! ts = Some value.
Proof.
  intros Htmods Hwrs Hkmods Hc.
  specialize (Hc ts key).
  by rewrite /lookup_twice Htmods Hkmods Hwrs in Hc.
Qed.

Lemma tmods_absent_kmod_absent tmods kmods kmod ts key :
  tmods !! ts = None ->
  kmods !! key = Some kmod ->
  tmods_kmods_consistent tmods kmods ->
  kmod !! ts = None.
Proof.
  intros Htmods Hkmods Hc.
  specialize (Hc ts key).
  by rewrite /lookup_twice Htmods Hkmods in Hc.
Qed.

Lemma resm_cmted_kmod_absent resm kmods kmod ts wrs key :
  resm !! ts = Some (ResCommitted wrs) ->
  wrs !! key = None ->
  kmods !! key = Some kmod ->
  tmods_kmods_consistent (resm_to_tmods resm) kmods ->
  kmod !! ts = None.
Proof.
  intros Hresm Hwrs Hkmods Hc.
  set tmods := (resm_to_tmods _) in Hc.
  assert (Htmods : tmods !! ts = Some wrs).
  { rewrite lookup_omap_Some. by exists (ResCommitted wrs). }
  by eapply tmods_present_kmod_absent.
Qed.

Lemma resm_cmted_kmod_present resm kmods kmod ts wrs key value :
  resm !! ts = Some (ResCommitted wrs) ->
  wrs !! key = Some value ->
  kmods !! key = Some kmod ->
  tmods_kmods_consistent (resm_to_tmods resm) kmods ->
  kmod !! ts = Some value.
Proof.
  intros Hresm Hwrs Hkmods Hc.
  set tmods := (resm_to_tmods _) in Hc.
  assert (Htmods : tmods !! ts = Some wrs).
  { rewrite lookup_omap_Some. by exists (ResCommitted wrs). }
  by eapply tmods_present_kmod_present.
Qed.

Lemma resm_abted_kmod_absent resm kmods kmod ts key :
  resm !! ts = Some ResAborted ->
  kmods !! key = Some kmod ->
  tmods_kmods_consistent (resm_to_tmods resm) kmods ->
  kmod !! ts = None.
Proof.
  intros Hresm Hkmods Hc.
  set tmods := (resm_to_tmods _) in Hc.
  assert (Htmods : tmods !! ts = None).
  { by rewrite lookup_omap Hresm /=. }
  by eapply tmods_absent_kmod_absent.
Qed.

Lemma resm_absent_kmod_absent resm kmods kmod ts key :
  resm !! ts = None ->
  kmods !! key = Some kmod ->
  tmods_kmods_consistent (resm_to_tmods resm) kmods ->
  kmod !! ts = None.
Proof.
  intros Hresm Hkmods Hc.
  set tmods := (resm_to_tmods _) in Hc.
  assert (Htmods : tmods !! ts = None).
  { by rewrite lookup_omap Hresm /=. }
  by eapply tmods_absent_kmod_absent.
Qed.

(* TODO: move to distx_inv_proof.v once stable. *)
Lemma diff_by_cmtd_inv_learn_prepare repl cmtd kmod ts :
  kmod !! O = None ->
  (length repl ≤ ts)%nat ->
  kmod !! ts = None ->
  diff_by_cmtd repl cmtd kmod O ->
  diff_by_cmtd repl cmtd kmod ts.
Proof.
  intros Hz Hlen Hts Hdiff.
  rewrite /diff_by_cmtd Hz in Hdiff.
  destruct Hdiff as [[tsrd Hextend] _].
  rewrite /diff_by_cmtd Hts.
  by split; first eauto.
Qed.

Lemma diff_by_cmtd_inv_learn_commit repl cmtd kmod ts v :
  kmod !! O = None ->
  (* (length repl ≤ ts)%nat -> *)
  kmod !! ts = Some v ->
  diff_by_cmtd repl cmtd kmod ts ->
  diff_by_cmtd (last_extend ts repl ++ [v]) cmtd kmod O.
Proof.
  intros Hz Hv Hdiff.
  rewrite /diff_by_cmtd Hv in Hdiff.
  rewrite /diff_by_cmtd Hz.
  split; last done.
  by exists ts.
Qed.
(* TODO: move to distx_inv_proof.v once stable. *)

(* TODO: move to distx_own.v once stable. *)
Class distx_ghostG (Σ : gFunctors).

Record distx_names := {}.

(* TODO: consider decomposing them into smaller pieces. *)
Section ghost.
  Context `{!distx_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : distx_names).

  Definition db_ptsto γ (k : dbkey) (v : dbval) : iProp Σ.
  Admitted.

  Definition db_ptstos γ (m : dbmap) : iProp Σ :=
    [∗ map] k ↦ v ∈ m, db_ptsto γ k v.

  Definition hist_repl_half γ (k : dbkey) (l : dbhist) : iProp Σ.
  Admitted.

  Definition hist_repl_at γ (k : dbkey) (ts : nat) (v : dbval) : iProp Σ.
  Admitted.

  Definition hist_lnrz_half γ (k : dbkey) (l : dbhist) : iProp Σ.
  Admitted.

  Definition hist_lnrz_at γ (k : dbkey) (ts : nat) (v : dbval) : iProp Σ.
  Admitted.

  Definition ts_repl_half γ (k : dbkey) (ts : nat) : iProp Σ.
  Admitted.

  Definition tuple_repl_half γ (k : dbkey) (t : dbtpl) : iProp Σ :=
    hist_repl_half γ k t.1 ∗ ts_repl_half γ k t.2.

  Lemma tuple_repl_agree {γ k t0 t1} :
    tuple_repl_half γ k t0 -∗
    tuple_repl_half γ k t1 -∗
    ⌜t1 = t0⌝.
  Admitted.

  Lemma tuple_repl_big_agree {γ tpls0 tpls1} :
    dom tpls0 = dom tpls1 ->
    ([∗ map] k ↦ tpl ∈ tpls0, tuple_repl_half γ k tpl) -∗
    ([∗ map] k ↦ tpl ∈ tpls1, tuple_repl_half γ k tpl) -∗
    ⌜tpls1 = tpls0⌝.
  Admitted.
  
  Lemma tuple_repl_update {γ k t0 t1} t' :
    tuple_repl_half γ k t0 -∗
    tuple_repl_half γ k t1 ==∗
    tuple_repl_half γ k t' ∗ tuple_repl_half γ k t'.
  Admitted.

  Lemma tuple_repl_big_update {γ tpls} tpls' :
    dom tpls = dom tpls' ->
    ([∗ map] k ↦ tpl ∈ tpls, tuple_repl_half γ k tpl) -∗
    ([∗ map] k ↦ tpl ∈ tpls, tuple_repl_half γ k tpl) ==∗
    ([∗ map] k ↦ tpl ∈ tpls', tuple_repl_half γ k tpl) ∗
    ([∗ map] k ↦ tpl ∈ tpls', tuple_repl_half γ k tpl).
  Admitted.

  (* Transaction result map RA. *)
  Definition txnres_auth γ (resm : gmap nat txnres) : iProp Σ.
  Admitted.

  Definition txnres_receipt γ (ts : nat) (res : txnres) : iProp Σ.
  Admitted.

  #[global]
  Instance txnres_receipt_persistent γ ts res :
    Persistent (txnres_receipt γ ts res).
  Admitted.

  Definition txnres_cmt γ ts wrs :=
    txnres_receipt γ ts (ResCommitted wrs).

  Definition txnres_abt γ ts :=
    txnres_receipt γ ts ResAborted.

  Lemma txnres_insert {γ resm} ts res :
    resm !! ts = None ->
    txnres_auth γ resm ==∗
    txnres_auth γ (<[ts := res]> resm).
  Admitted.

  Lemma txnres_witness γ resm ts res :
    resm !! ts = Some res ->
    txnres_auth γ resm -∗
    txnres_receipt γ ts res.
  Admitted.

  Lemma txnres_lookup γ resm ts res :
    txnres_auth γ resm -∗
    txnres_receipt γ ts res -∗
    ⌜resm !! ts = Some res⌝.
  Admitted.

  (* Transaction write-set map RA. *)
  Definition txnwrs_auth γ (wrsm : gmap nat dbmap) : iProp Σ.
  Admitted.

  Definition txnwrs_receipt γ (ts : nat) (wrs : dbmap) : iProp Σ.
  Admitted.

  #[global]
  Instance txnwrs_receipt_persistent γ ts wrs  :
    Persistent (txnwrs_receipt γ ts wrs).
  Admitted.

  (* Custom transaction status RA. *)
  Definition txnst_auth γ (gid : groupid) (stm : gmap nat txnst) : iProp Σ.
  Admitted.

  Definition txnst_lb γ (gid : groupid) (ts : nat) (st : txnst) : iProp Σ.
  Admitted.

  #[global]
  Instance txnst_lb_persistent γ gid ts st :
    Persistent (txnst_lb γ gid ts st).
  Admitted.

  Lemma txnst_prepare {γ gid stm} ts wrs :
    stm !! ts = None ->
    txnst_auth γ gid stm ==∗
    txnst_auth γ gid (<[ts := StPrepared wrs]> stm).
  Admitted.

  Lemma txnst_commit {γ gid stm} ts wrs :
    stm !! ts = Some (StPrepared wrs) ->
    txnst_auth γ gid stm ==∗
    txnst_auth γ gid (<[ts := StCommitted]> stm).
  Admitted.

  Lemma txnst_abort {γ gid stm} ts wrs :
    stm !! ts = Some (StPrepared wrs) ->
    txnst_auth γ gid stm ==∗
    txnst_auth γ gid (<[ts := StAborted]> stm).
  Admitted.

  Lemma txnst_direct_abort {γ gid stm} ts :
    stm !! ts = None ->
    txnst_auth γ gid stm ==∗
    txnst_auth γ gid (<[ts := StAborted]> stm).
  Admitted.

  Lemma txnst_witness γ gid stm ts st :
    stm !! ts = Some st ->
    txnst_auth γ gid stm -∗
    txnst_lb γ gid ts st.
  Admitted.

  Lemma txnst_absent_false γ gid stm ts st :
    stm !! ts = None ->
    txnst_auth γ gid stm -∗
    txnst_lb γ gid ts st -∗
    False.
  Admitted.

  Lemma txnst_lookup γ gid stm ts st :
    txnst_auth γ gid stm -∗
    txnst_lb γ gid ts st -∗
    ⌜stm !! ts = Some st⌝.
  Admitted.

  Definition kmods_lnrz γ (kmods : gmap dbkey dbkmod) : iProp Σ.
  Admitted.

  Definition kmod_lnrz γ (k : dbkey) (kmod : dbkmod) : iProp Σ.
  Admitted.

  Definition kmods_cmtd γ (kmods : gmap dbkey dbkmod) : iProp Σ.
  Admitted.

  Definition kmod_cmtd γ (k : dbkey) (kmod : dbkmod) : iProp Σ.
  Admitted.

  Lemma kmods_cmtd_lookup {γ kmods k kmod} :
    kmods_cmtd γ kmods -∗
    kmod_cmtd γ k kmod -∗
    ⌜kmods !! k = Some kmod⌝.
  Admitted.

  Definition clog_half γ (gid : groupid) (log : dblog) : iProp Σ.
  Admitted.

  Definition clog_lb γ (gid : groupid) (log : dblog) : iProp Σ.
  Admitted.

  Definition clog_lbs γ (logs : gmap groupid dblog) : iProp Σ :=
    [∗ map] gid ↦ log ∈ logs, clog_lb γ gid log.

  Definition cpool_half γ (gid : groupid) (pool : gset command) : iProp Σ.
  Admitted.

  Definition cmd_receipt γ (gid : groupid) (lsn : nat) (term : nat) (c : command) : iProp Σ.
  Admitted.
  
  Definition ts_auth γ (ts : nat) : iProp Σ.
  Admitted.

  Definition ts_lb γ (ts : nat) : iProp Σ.
  Admitted.

  #[global]
  Instance ts_lb_persistent γ ts :
    Persistent (ts_lb γ ts).
  Admitted.

  Definition txn_proph γ (acts : list action) : iProp Σ.
  Admitted.

End ghost.

Section spec.
  Context `{!distx_ghostG Σ}.

  Definition group_txnst γ gid ts st : iProp Σ :=
    ∃ log, clog_lb γ gid log ∧ ⌜log_txnst ts st log⌝.

End spec.

Section sep.
  Context {PROP : bi}.

  Lemma big_sepM_impl_dom_eq_res `{Countable K} {A B}
    (Φ : K → A → PROP) (Ψ : K → B → PROP) (R : PROP)
    (m1 : gmap K A) (m2 : gmap K B) :
    dom m2 = dom m1 →
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    R -∗
    □ (∀ (k : K) (x : A) (y : B),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ →
         Φ k x -∗ R -∗ Ψ k y ∗ R) -∗
    ([∗ map] k↦y ∈ m2, Ψ k y) ∗ R.
  Proof.
    iInduction m2 as [| k x m2 Hm2k] "IH" using map_ind forall (m1).
    { iIntros (Hdom) "Hm HR #Himpl".
      iFrame.
      iApply big_sepM_empty.
      rewrite dom_empty_L in Hdom. symmetry in Hdom.
      apply dom_empty_inv_L in Hdom.
      by rewrite Hdom big_sepM_empty.
    }
    iIntros (Hdom) "Hm1 HR #Himpl".
    rewrite dom_insert_L in Hdom.
    assert (Hm1k : k ∈ dom m1) by set_solver.
    rewrite elem_of_dom in Hm1k. destruct Hm1k as [y Hy].
    apply insert_delete in Hy. rewrite -Hy.
    set m0 := delete _ _.
    iDestruct (big_sepM_insert with "Hm1") as "[HΦ Hm1]".
    { by rewrite lookup_delete. }
    rewrite big_sepM_insert; last done.
    iDestruct ("Himpl" with "[] [] HΦ HR") as "[HΨ HR]".
    { by rewrite lookup_insert. }
    { by rewrite lookup_insert. }
    iDestruct ("IH" with "[] Hm1 HR []") as "[Hm2 HR]"; last by iFrame.
    { iPureIntro. subst m0. apply not_elem_of_dom_2 in Hm2k. set_solver. }
    iIntros "!>" (i p q Hp Hq) "HΦ HR".
    iDestruct ("Himpl" with "[] [] HΦ HR") as "HH".
    { rewrite lookup_insert_ne; [done | set_solver]. }
    { rewrite lookup_insert_ne; [done | set_solver]. }
    iFrame.
  Qed.

  Lemma big_sepM_impl_dom_eq `{Countable K} {A B}
    (Φ : K → A → PROP) (Ψ : K → B → PROP) (m1 : gmap K A) (m2 : gmap K B) :
    dom m2 = dom m1 →
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    □ (∀ (k : K) (x : A) (y : B),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ →
         Φ k x -∗ Ψ k y) -∗
    ([∗ map] k↦y ∈ m2, Ψ k y).
  Proof.
    iIntros (Hdom) "Hm1 #Himpl".
    iDestruct (big_sepM_impl_dom_eq_res _ Ψ emp _ m2 with "Hm1 [] []")
      as "[Hm2 _ ]"; [done | done | | iFrame].
    iIntros "!>" (k x y Hx Hy) "HΦ".
    iDestruct ("Himpl" with "[] [] HΦ") as "HΨ"; [done | done | by auto].
  Qed.

  Lemma big_sepM_sepM2_impl_res `{Countable K} {A B}
    (Φ : K → A → PROP) (Ψ : K → A -> B → PROP) (R : PROP)
    (m1 : gmap K A) (m2 : gmap K B) :
    dom m2 = dom m1 →
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    R -∗
    □ (∀ (k : K) (x : A) (y : B),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ →
         Φ k x -∗ R -∗ Ψ k x y ∗ R) -∗
    ([∗ map] k↦x;y ∈ m1;m2, Ψ k x y) ∗ R.
  Proof.
    iIntros (Hdom) "Hm1 HR #Himpl".
    rewrite big_sepM2_alt.
    iDestruct (big_sepM_impl_dom_eq_res _ (λ k xy, Ψ k xy.1 xy.2) R _ (map_zip m1 m2)
                with "Hm1 HR []") as "[HΨ Hm2]"; last by iFrame.
    { rewrite dom_map_zip_with_L. set_solver. }
    iIntros "!>" (k x p Hm1 Hm1m2) "HΦ HR".
    rewrite map_lookup_zip_Some in Hm1m2.
    destruct Hm1m2 as [Hm1' Hm2].
    rewrite Hm1' in Hm1. inversion_clear Hm1.
    by iDestruct ("Himpl" with "[] [] HΦ HR") as "[HΨ HR]"; last iFrame.
  Qed.

  Lemma big_sepM2_sepM_impl_res `{Countable K} {A B C}
    (Φ : K → A -> B → PROP) (Ψ : K → C → PROP) (R : PROP)
    (m1 : gmap K A) (m2 : gmap K B) (m3 : gmap K C) :
    dom m3 = dom m1 ->
    ([∗ map] k↦x;y ∈ m1;m2, Φ k x y) -∗
    R -∗
    □ (∀ (k : K) (x : A) (y : B) (z : C),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ → ⌜m3 !! k = Some z⌝ →
         Φ k x y -∗ R -∗ Ψ k z ∗ R) -∗
    ([∗ map] k↦z ∈ m3, Ψ k z) ∗ R.
  Proof.
    iIntros (Hdom) "Hm1m2 HR #Himpl".
    rewrite big_sepM2_alt.
    iDestruct "Hm1m2" as "[%Hdom' Hm1m2]".
    iDestruct (big_sepM_impl_dom_eq_res (λ k xy, Φ k xy.1 xy.2) Ψ R (map_zip m1 m2) m3
                with "[Hm1m2] HR []") as "[HΨ Hm3]"; [| iFrame | | iFrame].
    { rewrite dom_map_zip_with_L. set_solver. }
    iIntros "!>" (k p z Hm1m2 Hm3) "HΦ HR".
    rewrite map_lookup_zip_Some in Hm1m2.
    destruct Hm1m2 as [Hm1 Hm2].
    by iDestruct ("Himpl" with "[] [] [] HΦ HR") as "[HΨ HR]"; last iFrame.
  Qed.

  Lemma big_sepM2_sepM_impl `{Countable K} {A B C}
    (Φ : K → A -> B → PROP) (Ψ : K → C → PROP)
    (m1 : gmap K A) (m2 : gmap K B) (m3 : gmap K C) :
    dom m3 = dom m1 ->
    ([∗ map] k↦x;y ∈ m1;m2, Φ k x y) -∗
    □ (∀ (k : K) (x : A) (y : B) (z : C),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ → ⌜m3 !! k = Some z⌝ →
         Φ k x y -∗ Ψ k z) -∗
    ([∗ map] k↦z ∈ m3, Ψ k z).
  Proof.
    iIntros (Hdom) "Hm1m2 #Himpl".
    iDestruct (big_sepM2_sepM_impl_res Φ Ψ emp _ _ m3 with "Hm1m2 [] []")
      as "[HΨ _]"; [done | done | | by iFrame].
    iIntros "!>" (k x y z Hx Hy Hz) "HΦ _".
    by iDestruct ("Himpl" with "[] [] [] HΦ") as "HΨ"; last iFrame.
  Qed.

  Lemma big_sepM_impl_res `{Countable K} {A}
    (Φ : K → A → PROP) (Ψ : K → A → PROP) (R : PROP) (m : gmap K A) :
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    R -∗
    □ (∀ (k : K) (x : A),
         ⌜m !! k = Some x⌝ →
         Φ k x -∗ R -∗ Ψ k x ∗ R) -∗
    ([∗ map] k↦y ∈ m, Ψ k y) ∗ R.
  Proof.
    iIntros "Hm HR #Himpl".
    iDestruct (big_sepM_impl_dom_eq_res _ Ψ _ m m with "Hm HR []")
      as "[HΨ Hm]"; [done | | iFrame].
    iIntros "!>" (k x y Hx Hy) "HΦ HR".
    rewrite Hx in Hy. inversion Hy. subst y.
    by iApply ("Himpl" with "[] HΦ HR").
  Qed.

  Lemma big_sepM_dom_subseteq_split `{Countable K} {A}
    (Φ : K -> A -> PROP) (m : gmap K A) (s : gset K) :
    s ⊆ dom m ->
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    ∃ m', ⌜dom m' = s ∧ m' ⊆ m⌝ ∗
          ([∗ map] k↦x ∈ m', Φ k x) ∗ ([∗ map] k↦x ∈ m ∖ m', Φ k x).
  Proof.
    iInduction s as [| k s] "IH" using set_ind_L forall (m).
    { iIntros (_) "Hm".
      iExists ∅. iSplit.
      { iPureIntro. split; [done | apply map_empty_subseteq]. }
      rewrite big_sepM_empty map_difference_empty.
      by auto.
    }
    iIntros (Hsubseteq) "Hm".
    rewrite union_subseteq -elem_of_subseteq_singleton elem_of_dom in Hsubseteq.
    destruct Hsubseteq as [Hk Hs].
    destruct Hk as [v Hk].
    iDestruct (big_sepM_delete with "Hm") as "[Hk Hm]"; first apply Hk.
    iDestruct ("IH" with "[] Hm") as (m') "(Hdom & Hm' & Hm)".
    { iPureIntro. set_solver. }
    iDestruct "Hdom" as %[Hdom Hsubseteq].
    iExists (insert k v m').
    iSplit.
    { iPureIntro.
      split; first set_solver.
      apply insert_subseteq_l; first done.
      transitivity (delete k m); [done | apply delete_subseteq].
    }
    rewrite big_sepM_insert; last by rewrite -not_elem_of_dom Hdom.
    iFrame.
    iApply (big_sepM_impl_dom_eq with "Hm"); first set_solver.
    iIntros "!>" (i x y Hx Hy) "HΦ".
    replace y with x; first done.
    rewrite lookup_difference in Hx. rewrite lookup_difference in Hy.
    destruct (decide (i = k)) as [-> | Hne]; first by rewrite lookup_insert in Hy.
    rewrite lookup_insert_ne in Hy; last done.
    destruct (m' !! i) as [? |]; first done.
    rewrite lookup_delete_ne in Hx; last done.
    rewrite Hx in Hy.
    by inversion Hy.
  Qed.

  Lemma big_sepM_difference_combine `{Countable K} {A}
    (Φ : K -> A -> PROP) (m1 m2 : gmap K A) :
    m1 ⊆ m2 ->
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    ([∗ map] k↦x ∈ m2 ∖ m1, Φ k x) -∗
    ([∗ map] k↦x ∈ m2, Φ k x).
  Proof.
    iIntros (Hsubseteq) "Hm1 Hm2m1".
    rewrite -{2}(map_difference_union _ _ Hsubseteq) big_sepM_union; last first.
    { by apply map_disjoint_difference_r. }
    iFrame.
  Qed.

  Lemma big_sepM_dom_subseteq_acc `{Countable K} {A}
    (Φ : K -> A -> PROP) (m : gmap K A) (s : gset K) :
    s ⊆ dom m ->
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    ∃ m', ⌜dom m' = s⌝ ∗ ([∗ map] k↦x ∈ m', Φ k x) ∗
          (([∗ map] k↦x ∈ m', Φ k x) -∗ ([∗ map] k↦x ∈ m, Φ k x)).
  Proof.
    iInduction s as [| k s] "IH" using set_ind_L forall (m).
    { iIntros (_) "Hm".
      iExists ∅. iSplit; first done.
      rewrite big_sepM_empty.
      by auto.
    }
    iIntros (Hsubseteq) "Hm".
    rewrite union_subseteq -elem_of_subseteq_singleton elem_of_dom in Hsubseteq.
    destruct Hsubseteq as [Hk Hs].
    destruct Hk as [v Hk].
    iDestruct (big_sepM_delete with "Hm") as "[Hk Hm]"; first apply Hk.
    iDestruct ("IH" with "[] Hm") as (m') "(Hdom & Hm' & Hacc)".
    { iPureIntro. set_solver. }
    (* not sure why % doesn't work on the above ipat *)
    iDestruct "Hdom" as "%Hdom".
    iExists (insert k v m').
    iSplit.
    { iPureIntro. set_solver. }
    rewrite big_sepM_insert; last by rewrite -not_elem_of_dom Hdom.
    iFrame.
    iIntros "[Hk Hm']".
    iDestruct ("Hacc" with "Hm'") as "Hm".
    iApply big_sepM_delete; first apply Hk.
    iFrame.
  Qed.

  Lemma big_sepS_subseteq_acc `{Countable A} (Φ : A -> PROP) (X Y : gset A) :
    Y ⊆ X ->
    ([∗ set] x ∈ X, Φ x) -∗
    ([∗ set] x ∈ Y, Φ x) ∗
    (([∗ set] x ∈ Y, Φ x) -∗ ([∗ set] x ∈ X, Φ x)).
  Proof.
    iIntros (Hsubseteq) "HX".
    rewrite (union_difference_L _ _ Hsubseteq).
    iDestruct (big_sepS_union with "HX") as "[HY Hacc]"; first set_solver.
    iFrame. iIntros "HY".
    rewrite big_sepS_union; [iFrame | set_solver].
  Qed.

End sep.

Section inv.
  Context `{!heapGS Σ, !distx_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : distx_names).

  Definition all_prepared γ ts wrs : iProp Σ :=
    [∗ set] gid ∈ ptgroups (dom wrs),
      txnst_lb γ gid ts (StPrepared (wrs_group gid wrs)).

  Definition some_aborted γ ts : iProp Σ :=
    ∃ gid, txnst_lb γ gid ts StAborted.

  Definition valid_res γ ts res : iProp Σ :=
    match res with
    | ResCommitted wrs => all_prepared γ ts wrs
    | ResAborted => some_aborted γ ts
    end.

  #[global]
  Instance valid_res_persistent γ ts res :
    Persistent (valid_res γ ts res).
  Proof. destruct res; apply _. Qed.

  Definition txn_inv γ : iProp Σ :=
    ∃ (ts : nat) (future past : list action)
      (txns_cmt txns_abt : gmap nat dbmap)
      (resm : gmap nat txnres) (wrsm : gmap nat dbmap)
      (kmodls kmodcs : gmap dbkey dbkmod),
      (* global timestamp *)
      "Hts"    ∷ ts_auth γ ts ∗
      (* prophecy variable *)
      "Hproph" ∷ txn_proph γ future ∗
      (* transaction result map *)
      "Hresm" ∷ txnres_auth γ resm ∗
      (* transaction write set map *)
      "Hwrsm" ∷ txnwrs_auth γ wrsm ∗
      (* key modifications *)
      "Hkmodls" ∷ kmods_lnrz γ kmodls ∗
      "Hkmodcs" ∷ kmods_cmtd γ kmodcs ∗
      (* safe commit/abort invariant *)
      "#Hvr"  ∷ ([∗ map] tid ↦ res ∈ resm, valid_res γ tid res) ∗
      (* TODO: for coordinator recovery, add a monotonically growing set of
      active txns; each active txn either appears in [txns_cmt]/[txns_abt] or in
      the result map [resm]. *)
      "%Hcf"   ∷ ⌜conflict_free future txns_cmt⌝ ∗
      "%Hcp"   ∷ ⌜conflict_past future past txns_abt⌝ ∗
      "%Hcip"  ∷ ⌜cmtd_impl_prep resm wrsm⌝ ∗
      "%Htkcl" ∷ ⌜tmods_kmods_consistent txns_cmt kmodls⌝ ∗
      "%Htkcc" ∷ ⌜tmods_kmods_consistent (resm_to_tmods resm) kmodcs⌝.

  Definition key_inv_prop
    (key : dbkey) (dbv : dbval) (lnrz cmtd repl : dbhist)
    (tslb tsprep : nat) (kmodl kmodc : dbkmod) : iProp Σ :=
    "%Hlast"    ∷ ⌜last lnrz = Some dbv⌝ ∗
    "%Hprefix"  ∷ ⌜prefix cmtd lnrz⌝ ∗
    "%Hext"     ∷ ⌜(length lnrz ≤ S tslb)%nat⌝ ∗
    "%Hdiffl"   ∷ ⌜diff_by_lnrz cmtd lnrz kmodl⌝ ∗
    "%Hdiffc"   ∷ ⌜diff_by_cmtd repl cmtd kmodc tsprep⌝ ∗
    "%Hzrsv"    ∷ ⌜kmodc !! O = None⌝.

  Definition key_inv γ (key : dbkey) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd repl : dbhist)
      (tslb tsprep : nat)
      (kmodl kmodc : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_half γ key lnrz ∗
      "Hrepl"     ∷ hist_repl_half γ key repl ∗
      "Htsprep"   ∷ ts_repl_half γ key tsprep ∗
      "Hkmodl"    ∷ kmod_lnrz γ key kmodl ∗
      "Hkmodc"    ∷ kmod_cmtd γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "Hprop"     ∷ key_inv_prop key dbv lnrz cmtd repl tslb tsprep kmodl kmodc.

  Definition key_inv_no_repl_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd : dbhist)
      (tslb : nat)
      (kmodl kmodc : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_half γ key lnrz ∗
      "Hkmodl"    ∷ kmod_lnrz γ key kmodl ∗
      "Hkmodc"    ∷ kmod_cmtd γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "Hprop"     ∷ key_inv_prop key dbv lnrz cmtd repl tslb tsprep kmodl kmodc.

  Definition key_inv_with_kmodc_no_repl_tsprep
    γ (key : dbkey) (kmodc : dbkmod) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd : dbhist)
      (tslb : nat)
      (kmodl : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_half γ key lnrz ∗
      "Hkmodl"    ∷ kmod_lnrz γ key kmodl ∗
      "Hkmodc"    ∷ kmod_cmtd γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "Hprop"     ∷ key_inv_prop key dbv lnrz cmtd repl tslb tsprep kmodl kmodc.

  Definition key_inv_xcmted_no_repl_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) (ts : nat) : iProp Σ :=
    ∃ kmodc,
      "Hkey" ∷ key_inv_with_kmodc_no_repl_tsprep γ key kmodc repl tsprep ∗
      "%Hnc" ∷ ⌜kmodc !! ts = None⌝.

  Definition key_inv_cmted_no_repl_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) (v : dbval) : iProp Σ :=
    ∃ kmodc,
      "Hkey" ∷ key_inv_with_kmodc_no_repl_tsprep γ key kmodc repl tsprep ∗
      "%Hv"  ∷ ⌜kmodc !! tsprep = Some v⌝.

  (** The predicate [consistent_abort] says that a transaction is aborted
  globally if it is aborted locally on some replica (the other direction is
  encoded in [safe_submit]). This gives contradiction when learning a commit
  command under an aborted state. *)
  Definition consistent_abort γ tid st : iProp Σ :=
    match st with
    | StAborted => txnres_abt γ tid
    | _ => True
    end.

  #[global]
  Instance consistent_abort_persistent γ gid c :
    Persistent (consistent_abort γ gid c).
  Proof. destruct c; apply _. Qed.

  Definition safe_submit_finalize γ gid (c : command) : iProp Σ :=
    match c with
    (* Enforces [CmdCmt] is submitted to only participant groups. *)
    | CmdCmt ts => (∃ wrs, txnres_cmt γ ts wrs ∧ ⌜gid ∈ ptgroups (dom wrs)⌝)
    | CmdAbt ts => txnres_abt γ ts
    (* Enforces [CmdPrep] is submitted to only participant groups, and partial
    writes is part of the global commit, which we would likely need with
    coordinator recovery. *)
    | CmdPrep ts pwrs => (∃ wrs, txnwrs_receipt γ ts wrs ∧ ⌜pwrs ≠ ∅ ∧ pwrs = wrs_group gid wrs⌝)
    | _ => True
    end.

  #[global]
  Instance safe_submit_finalize_persistent γ gid c :
    Persistent (safe_submit_finalize γ gid c).
  Proof. destruct c; apply _. Qed.

  Definition valid_cmd_in_group gid (c : command) :=
    match c with
    | CmdPrep ts wrs => valid_ts ts ∧ valid_wrs wrs ∧ wrs_in_group gid wrs
    | CmdRead ts key => valid_ts ts ∧ key_in_group gid key
    | _ => True
    end.

  Definition group_inv γ (gid : groupid) : iProp Σ :=
    ∃ (log : dblog) (cpool : gset command)
      (stm : gmap nat txnst) (tpls : gmap dbkey dbtpl),
      "Hlog"    ∷ clog_half γ gid log ∗
      "Hcpool"  ∷ cpool_half γ gid cpool ∗
      "Hstm"    ∷ txnst_auth γ gid stm ∗
      "Hrepls"  ∷ ([∗ map] key ↦ tpl ∈ tpls_group gid tpls, tuple_repl_half γ key tpl) ∗
      "#Hca"    ∷ ([∗ map] tid ↦ st ∈ stm, consistent_abort γ tid st) ∗
      "#Hvc"    ∷ ([∗ set] c ∈ cpool, safe_submit_finalize γ gid c) ∗
      "%Hrsm"   ∷ ⌜apply_cmds log = State stm tpls⌝ ∗
      "%Hcg"    ∷ ⌜set_Forall (valid_cmd_in_group gid) cpool⌝.

  Definition group_inv_with_cpool_no_log
    γ (gid : groupid) (log : dblog) (cpool : gset command) : iProp Σ :=
    ∃ (stm : gmap nat txnst) (tpls : gmap dbkey dbtpl),
      "Hcpool"  ∷ cpool_half γ gid cpool ∗
      "Hstm"    ∷ txnst_auth γ gid stm ∗
      "Hrepls"  ∷ ([∗ map] key ↦ tpl ∈ tpls_group gid tpls, tuple_repl_half γ key tpl) ∗
      "#Hca"    ∷ ([∗ map] tid ↦ st ∈ stm, consistent_abort γ tid st) ∗
      "#Hvc"    ∷ ([∗ set] c ∈ cpool, safe_submit_finalize γ gid c) ∗
      "%Hrsm"   ∷ ⌜apply_cmds log = State stm tpls⌝ ∗
      "%Hcg"    ∷ ⌜set_Forall (valid_cmd_in_group gid) cpool⌝.

  Definition distxN := nroot .@ "distx".

  Definition distx_inv γ : iProp Σ :=
    (* txn invariants *)
    "Htxn"    ∷ txn_inv γ ∗
    (* keys invariants *)
    "Hkeys"   ∷ ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    (* groups invariants *)
    "Hgroups" ∷ ([∗ list] gid ∈ gids_all, group_inv γ gid).

  #[global]
  Instance distx_inv_timeless γ :
    Timeless (distx_inv γ).
  Admitted.

  Definition know_distx_inv γ : iProp Σ :=
    inv distxN (distx_inv γ).

End inv.
(* TODO: move to distx_own.v once stable. *)
  
(* TODO: move to distx_group_inv.v once stable. *)
Section group_inv.
  Context `{!distx_ghostG Σ}.

  Definition cpool_subsume_log (cpool : gset command) (log : list command) :=
    Forall (λ c, c ∈ cpool) log.

  Lemma group_inv_expose_cpool_extract_log {γ} gid :
    group_inv γ gid -∗
    ∃ cpool log,
      clog_half γ gid log ∗
      group_inv_with_cpool_no_log γ gid log cpool.
  Proof.
  Admitted.

  (* TODO: might not need these anymore. *)
  Lemma keys_inv_group {γ keys} gid :
    ([∗ set] key ∈ keys, key_inv γ key) -∗
    ([∗ set] key ∈ (keys_group gid keys), key_inv γ key) ∗
    ([∗ set] key ∈ (keys_except_group gid keys), key_inv γ key).
  Proof.
  Admitted.

  Lemma keys_inv_ungroup {γ keys} gid :
    ([∗ set] key ∈ (keys_group gid keys), key_inv γ key) -∗
    ([∗ set] key ∈ (keys_except_group gid keys), key_inv γ key) -∗
    ([∗ set] key ∈ keys, key_inv γ key).
  Proof.
  Admitted.
  (* TODO: might not need these anymore. *)

  Lemma keys_inv_expose_repl_tsprep {γ} keys :
    ([∗ set] key ∈ keys, key_inv γ key) -∗
    ∃ tpls, ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) ∗
            ([∗ map] key ↦ tpl ∈ tpls, tuple_repl_half γ key tpl) ∧
            ⌜dom tpls = keys⌝.
  Proof.
  Admitted.

  Lemma keys_inv_merge_repl_tsprep {γ tpls} keys :
    dom tpls = keys ->
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) -∗
    ([∗ map] key ↦ tpl ∈ tpls, tuple_repl_half γ key tpl) -∗
    ([∗ set] key ∈ keys, key_inv γ key).
  Proof.
  Admitted.

  Lemma key_inv_no_repl_tsprep_unseal_kmodc γ key repl tsprep :
    key_inv_no_repl_tsprep γ key repl tsprep -∗
    ∃ kmodc, key_inv_with_kmodc_no_repl_tsprep γ key kmodc repl tsprep.
  Proof. iIntros "Hkey". iNamed "Hkey". iFrame "% # ∗". Qed.

  Lemma key_inv_not_committed γ gid ts stm key kmodc tpl :
    gid = key_to_group key ->
    stm !! ts = None ->
    txnst_auth γ gid stm -∗
    txn_inv γ -∗
    key_inv_with_kmodc_no_repl_tsprep γ key kmodc tpl.1 tpl.2 -∗
    ⌜kmodc !! ts = None⌝.
  Proof.
    iIntros (Hgid Hnone) "Hstm Htxn Hkey".
    iNamed "Htxn".
    destruct (resm !! ts) as [res |] eqn:Hlookup.
    { (* Case: Committed or aborted. *)
      iDestruct (big_sepM_lookup with "Hvr") as "Hres"; first apply Hlookup.
      destruct res.
      { (* Case: Committed. *)
        simpl.
        destruct (wrs !! key) as [v |] eqn:Hkey.
        { (* Case: [key] in the write set of [ts]; contradiction. *)
          rewrite /all_prepared.
          iDestruct (big_sepS_elem_of _ _ gid with "Hres") as "Hst".
          { rewrite Hgid. by eapply elem_of_ptgroups, elem_of_dom_2. }
          by iDestruct (txnst_absent_false with "Hstm Hst") as "[]".
        }
        (* Case: [key] not in the write set of [ts]. *)
        iNamed "Hkey".
        iDestruct (kmods_cmtd_lookup with "Hkmodcs Hkmodc") as %Hkm.
        iPureIntro.
        by eapply resm_cmted_kmod_absent.
      }
      { (* Case: Aborted. *)
        iNamed "Hkey".
        iDestruct (kmods_cmtd_lookup with "Hkmodcs Hkmodc") as %Hkm.
        iPureIntro.
        by eapply resm_abted_kmod_absent.
      }
    }
    (* Case: Not committed or aborted. *)
    iNamed "Hkey".
    iDestruct (kmods_cmtd_lookup with "Hkmodcs Hkmodc") as %Hkm.
    iPureIntro.
    by eapply resm_absent_kmod_absent.
  Qed.

  Lemma keys_inv_not_committed γ gid ts stm tpls :
    set_Forall (λ k, key_to_group k = gid) (dom tpls) ->
    stm !! ts = None ->
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) -∗
    txnst_auth γ gid stm -∗
    txn_inv γ -∗
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_xcmted_no_repl_tsprep γ key tpl.1 tpl.2 ts) ∗
    txnst_auth γ gid stm ∗
    txn_inv γ.
  Proof.
    iIntros (Hgid Hnone) "Hkeys Hst Htxn".
    iApply (big_sepM_impl_res with "Hkeys [Hst Htxn]").
    { iFrame. } (* why can't $ do the work? *)
    iIntros "!>" (k t Hkt) "Hkey [Hst Htxn]".
    apply elem_of_dom_2 in Hkt.
    specialize (Hgid _ Hkt). simpl in Hgid.
    rewrite /key_inv_xcmted_no_repl_tsprep.
    iDestruct (key_inv_no_repl_tsprep_unseal_kmodc with "Hkey") as (kmodc) "Hkey".
    iDestruct (key_inv_not_committed with "Hst Htxn Hkey") as %Hprep; first done.
    { apply Hnone. }
    iFrame "∗ %".
  Qed.

  Lemma key_inv_learn_prepare {γ gid ts wrs tpls} k x y :
    validate ts wrs tpls = true ->
    tpls_group gid tpls !! k = Some x ->
    tpls_group gid (acquire ts wrs tpls) !! k = Some y ->
    key_inv_xcmted_no_repl_tsprep γ k x.1 x.2 ts -∗
    key_inv_xcmted_no_repl_tsprep γ k y.1 y.2 ts.
  Proof.
    iIntros (Hvd Hx Hy) "Hkeys".
    iNamed "Hkeys". iNamed "Hkey". iNamed "Hprop".
    iFrame "∗ # %".
    iPureIntro.
    apply map_lookup_filter_Some_1_1 in Hx, Hy.
    destruct (wrs !! k) as [t | ] eqn:Hwrsk; last first.
    { (* Case: tuple not modified. *)
      rewrite acquire_unmodified in Hy; last done.
      rewrite Hy in Hx.
      by inversion Hx.
    }
    (* Case: tuple modified. *)
    assert (Hsome : is_Some (wrs !! k)) by done.
    destruct (validate_true Hsome Hvd) as (l & Htpl & Hlen).
    rewrite Hx in Htpl. inversion Htpl. subst x. clear Htpl.
    rewrite (acquire_modified Hsome Hx) /= in Hy.
    inversion Hy. subst y. clear Hy.
    simpl. simpl in Hdiffc.
    by apply diff_by_cmtd_inv_learn_prepare.
  Qed.

  Lemma keys_inv_learn_prepare {γ gid ts wrs tpls} :
    validate ts wrs tpls = true ->
    ([∗ map] key ↦ tpl ∈ tpls_group gid tpls,
       key_inv_xcmted_no_repl_tsprep γ key tpl.1 tpl.2 ts) -∗
    ([∗ map] key ↦ tpl ∈ tpls_group gid (acquire ts wrs tpls),
       key_inv_xcmted_no_repl_tsprep γ key tpl.1 tpl.2 ts).
  Proof.
    iIntros (Hvd) "Hkeys".
    set tpls' := acquire _ _ _.
    assert (Hdom : dom (tpls_group gid tpls') = dom (tpls_group gid tpls)).
    { apply tpls_group_dom. by rewrite acquire_dom. }
    iDestruct (big_sepM_impl_dom_eq _ _ with "Hkeys") as "Himpl".
    { apply Hdom. }
    iApply "Himpl".
    iIntros "!>" (k x y Hx Hy) "Hkey".
    by iApply (key_inv_learn_prepare with "Hkey").
  Qed.

  Lemma txn_inv_abort γ gid ts wrs :
    gid ∈ ptgroups (dom wrs) ->
    txnwrs_receipt γ ts wrs -∗
    txnst_lb γ gid ts StAborted -∗
    txn_inv γ ==∗
    txn_inv γ ∗
    txnres_abt γ ts.
  Proof.
    iIntros (Hgid) "Hwrs Hrpabt Htxn".
    iNamed "Htxn".
    destruct (resm !! ts) as [res |] eqn:Hres; last first.
    { (* Case: [ts] not aborted or committed yet. *)
      iMod (txnres_insert ts ResAborted with "Hresm") as "Hresm"; first done.
      iDestruct (txnres_witness with "Hresm") as "#Habt".
      { apply lookup_insert. }
      admit.
    }
    destruct res as [wrs' |]; last first.
    { (* Case: [ts] aborted; get a witness without any update. *)
      iDestruct (txnres_witness with "Hresm") as "#Habt".
      { apply Hres. }
      auto 10 with iFrame.
    }
    (* Case: [ts] committed; contradiction. *)
    iDestruct (big_sepM_lookup with "Hvr") as "#Hresc"; first apply Hres.
    rewrite /= /all_prepared.
  Admitted.

  Lemma group_inv_learn_prepare γ gid log cpool ts pwrs :
    CmdPrep ts pwrs ∈ cpool ->
    txn_inv γ -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_with_cpool_no_log γ gid log cpool ==∗
    txn_inv γ ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_with_cpool_no_log γ gid (log ++ [CmdPrep ts pwrs]) cpool.
  Proof.
    iIntros (Hc) "Htxn Hkeys Hgroup".
    iNamed "Hgroup".
    rewrite /apply_cmds in Hrsm.
    rewrite /group_inv_with_cpool_no_log.
    (* Frame away unused resources. *)
    iFrame "Hcpool".
    destruct (stm !! ts) eqn:Hdup.
    { (* Case: Txn [ts] has already prepared, aborted, or committed; no-op. *)
      iFrame "∗ #".
      by rewrite /apply_cmds foldl_snoc Hrsm /= Hdup.
    }
    (* Case: Txn [ts] has not prepared, aborted, or committed. *)
    destruct (try_acquire ts pwrs tpls) eqn:Hacq; last first.
    { (* Case: Validation fails; abort the transaction. *)
      iFrame "Hrepls Hkeys".
      iMod (txnst_direct_abort with "Hstm") as "Hstm"; first apply Hdup.
      iDestruct (txnst_witness with "Hstm") as "#Hrpabt".
      { apply lookup_insert. }
      iDestruct (big_sepS_elem_of with "Hvc") as "Hprep".
      { apply Hc. }
      iDestruct "Hprep" as (wrs) "(Hwrs & %Hne & %Hpwrs)".
      iMod (txn_inv_abort with "Hwrs Hrpabt Htxn") as "[Htxn #Habt]".
      { by eapply wrs_group_elem_of_ptgroups. }
      rewrite /apply_cmds foldl_snoc Hrsm /= Hdup Hacq.
      iDestruct (big_sepM_insert_2 _ _ ts StAborted with "[] Hca") as "Hca'"; first done.
      by iFrame "∗ # %".
    }
    (* Case: Validation succeeds; lock the tuples and mark the transaction prepared. *)
    rewrite /apply_cmds foldl_snoc Hrsm /= Hdup Hacq.
    rewrite /try_acquire in Hacq.
    destruct (validate ts pwrs tpls) eqn:Hvd; last done.
    inversion_clear Hacq.
    set tpls' := acquire _ _ _.
    (* Extract keys invariant in this group. *)
    iDestruct (keys_inv_group gid with "Hkeys") as "[Hkeys Hkeyso]".
    (* Expose the replicated history and prepared timestamp from keys invariant. *)
    iDestruct (keys_inv_expose_repl_tsprep with "Hkeys") as (tplsK) "(Hkeys & Htpls & %Hdom)".
    (* Agree on tuples from the group and keys invariants. *)
    iDestruct (tuple_repl_big_agree with "Hrepls Htpls") as %->.
    { pose proof (apply_cmds_dom log _ _ Hrsm) as Hdom'.
      rewrite Hdom.
      by rewrite -keys_group_tpls_group_dom.
    }
    (* Update the tuples (setting the prepared timestamp to [ts]). *)
    iMod (tuple_repl_big_update (tpls_group gid tpls') with "Hrepls Htpls") as "[Hrepls Htpls]".
    { apply tpls_group_dom. by rewrite acquire_dom. }
    (* Prove txn [ts] has not committed on [tpls]. *)
    iDestruct (keys_inv_not_committed with "Hkeys Hstm Htxn") as "(Hkeys & Hstm & Htxn)".
    { intros k Hk. by eapply key_to_group_tpls_group. }
    { apply Hdup. }
    (* Re-establish keys invariant w.r.t. updated tuples. *)
    iDestruct (keys_inv_learn_prepare with "Hkeys") as "Hkeys"; first done.
    (* Put ownership of tuples back to keys invariant. *)
    iDestruct (keys_inv_merge_repl_tsprep (keys_group gid keys_all) with "[Hkeys] Htpls") as "Hkeys".
    { rewrite -keys_group_tpls_group_dom in Hdom.
      by rewrite -keys_group_tpls_group_dom acquire_dom.
    }
    { iApply (big_sepM_mono with "Hkeys").
      iIntros (k t Hkt) "Hkey".
      iNamed "Hkey". iNamed "Hkey". iFrame "∗ #".
    }
    (* Merge the keys invariants of this group and other groups. *)
    iDestruct (keys_inv_ungroup with "Hkeys Hkeyso") as "Hkeys".
    (* Mark [ts] as prepared in the status map. *)
    iMod (txnst_prepare ts pwrs with "Hstm") as "Hstm"; first apply Hdup.
    iDestruct (big_sepM_insert_2 _ _ ts (StPrepared pwrs) with "[] Hca") as "Hca'"; first done.
    by iFrame "∗ # %".
  Qed.

  Lemma keys_inv_committed γ ts wrs wrsc tpls :
    dom tpls = dom wrs ->
    wrs ⊆ wrsc ->
    map_Forall (λ _ t, t.2 = ts) tpls ->
    txnres_cmt γ ts wrsc -∗
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) -∗
    txn_inv γ -∗
    ([∗ map] key ↦ tpl; v ∈ tpls; wrs, key_inv_cmted_no_repl_tsprep γ key tpl.1 ts v) ∗
    txn_inv γ.
  Proof.
    iIntros (Hdom Hwrsc Hts) "#Hcmt Htpls Htxn".
    iApply (big_sepM_sepM2_impl_res with "Htpls Htxn"); first done.
    iIntros "!>" (k [l t] v Htpl Hv) "Hkey Htxn".
    simpl.
    iNamed "Htxn".
    iDestruct (txnres_lookup with "Hresm Hcmt") as %Hresm.
    iNamed "Hkey".
    iDestruct (kmods_cmtd_lookup with "Hkmodcs Hkmodc") as %Hkmodc.
    assert (Hwrscv : wrsc !! k = Some v); first by eapply lookup_weaken.
    assert (Hkmodcv : kmodc !! ts = Some v); first by eapply resm_cmted_kmod_present.
    specialize (Hts _ _ Htpl). simpl in Hts. subst t.
    by iFrame "∗ # %".
  Qed.

  Lemma txn_inv_has_prepared γ gid ts wrs :
    gid ∈ ptgroups (dom wrs) ->
    txnres_cmt γ ts wrs -∗
    txn_inv γ -∗
    txnst_lb γ gid ts (StPrepared (wrs_group gid wrs)).
  Proof.
    iIntros (Hptg) "Hres Htxn".
    iNamed "Htxn".
  Admitted.

  Lemma key_inv_learn_commit {γ ts wrs tpls} k x y v :
    tpls !! k = Some x ->
    wrs !! k = Some v ->
    multiwrite ts wrs tpls !! k = Some y ->
    key_inv_cmted_no_repl_tsprep γ k x.1 ts v -∗
    key_inv_no_repl_tsprep γ k y.1 y.2.
  Proof.
    iIntros (Hx Hv Hy) "Hkeys".
    iNamed "Hkeys". iNamed "Hkey". iNamed "Hprop".
    iFrame "∗ # %".
    iPureIntro.
    rewrite lookup_merge Hv Hx /= in Hy.
    destruct x as [x ts'].
    inversion_clear Hy.
    by apply diff_by_cmtd_inv_learn_commit.
  Qed.

  Lemma keys_inv_learn_commit {γ ts wrs tpls} :
    ([∗ map] key ↦ tpl; v ∈ tpls; wrs,
       key_inv_cmted_no_repl_tsprep γ key tpl.1 ts v) -∗
    ([∗ map] key ↦ tpl ∈ multiwrite ts wrs tpls,
       key_inv_no_repl_tsprep γ key tpl.1 tpl.2).
  Proof.
    iIntros "Hkeys".
    iApply (big_sepM2_sepM_impl with "Hkeys").
    { apply multiwrite_dom. }
    iIntros "!>" (k x y z Hx Hy Hz) "Hkey".
    by iApply (key_inv_learn_commit with "Hkey").
  Qed.

  Lemma tuple_repl_half_multiwrite_disjoint {γ} ts wrs tpls :
    dom tpls ## dom wrs ->
    ([∗ map] k↦tpl ∈ tpls, tuple_repl_half γ k tpl) -∗
    ([∗ map] k↦tpl ∈ multiwrite ts wrs tpls, tuple_repl_half γ k tpl).
  Admitted.

  Lemma group_inv_learn_commit γ gid log cpool ts :
    cpool_subsume_log cpool (log ++ [CmdCmt ts]) ->
    txn_inv γ -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_with_cpool_no_log γ gid log cpool ==∗
    txn_inv γ ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_with_cpool_no_log γ gid (log ++ [CmdCmt ts]) cpool.
  Proof.
    iIntros (Hsubsume) "Htxn Hkeys Hgroup".
    rewrite /cpool_subsume_log Forall_app Forall_singleton in Hsubsume.
    destruct Hsubsume as [Hsubsume Hc].
    iNamed "Hgroup".
    (* Obtain proof that [ts] has committed. *)
    iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hc.
    iDestruct "Hc" as (wrsc) "[Hcmt %Hgid]".
    rewrite /apply_cmds in Hrsm.
    rewrite /group_inv_with_cpool_no_log.
    destruct (stm !! ts) eqn:Hdup; last first.
    { (* Case: Empty state; contradiction---no prepare before commit. *) 
      iDestruct (txn_inv_has_prepared with "Hcmt Htxn") as "#Hst"; first apply Hgid.
      by iDestruct (txnst_absent_false with "Hstm Hst") as "[]".
    }
    (* Case: Transaction prepared, aborted, or committed. *)
    destruct t as [wrs | |] eqn:Ht; last first.
    { (* Case: [StAborted]; contradiction. *)
      iDestruct (big_sepM_lookup with "Hca") as "#Habt".
      { apply Hdup. }
      simpl.
      iNamed "Htxn".
      iDestruct (txnres_lookup with "Hresm Hcmt") as "%Hcmt".
      iDestruct (txnres_lookup with "Hresm Habt") as "%Habt".
      congruence.
    }
    { (* Case: [StCommitted]; no-op. *)
      rewrite /apply_cmds foldl_snoc Hrsm /= Hdup.
      by auto with iFrame.
    }
    (* Case: [StPrepared wrs] *)
    rewrite /apply_cmds foldl_snoc Hrsm /= Hdup.
    set tpls' := multiwrite _ _ _.
    (* Take the required keys invariants. *)
    iDestruct (big_sepS_subseteq_acc _ _ (dom wrs) with "Hkeys") as "[Hkeys HkeysC]".
    { (* Prove [dom wrs ⊆ keys_all] *)
      unshelve epose proof (pwrs_validity gid log _) as Hpwrs.
      { eapply set_Forall_Forall_subsume; last apply Hsubsume.
        eapply set_Forall_impl; first apply Hcg.
        intros c Hvcg. rewrite /valid_cmd_in_group in Hvcg.
        destruct c; [| done | done | done].
        by destruct Hvcg as (_ & Hvw & Hwg).
      }
      specialize (Hpwrs _ _ _ _ Hrsm Hdup).
      by destruct Hpwrs as [Hvw _].
    }
    (* Take the required tuple ownerships from the group invariant. *)
    iDestruct (big_sepM_dom_subseteq_split _ _ (dom wrs) with "Hrepls")
      as (tplsg [Hdom Hsubseteq]) "[Hrepls HreplsO]".
    { (* Prove [dom wrs ⊆ dom (tpls_group gid tpls)] *)
      unshelve epose proof (pwrs_validity gid log _) as Hpwrs.
      { eapply set_Forall_Forall_subsume; last apply Hsubsume.
        eapply set_Forall_impl; first apply Hcg.
        intros c Hvcg. rewrite /valid_cmd_in_group in Hvcg.
        destruct c; [| done | done | done].
        by destruct Hvcg as (_ & Hvw & Hwg).
      }
      specialize (Hpwrs _ _ _ _ Hrsm Hdup).
      destruct Hpwrs as [Hvw Hwg].
      rewrite /wrs_in_group in Hwg.
      intros k Hin.
      specialize (Hwg _ Hin). simpl in Hwg.
      pose proof (apply_cmds_dom log _ _ Hrsm) as Hdom.
      rewrite (@keys_group_tpls_group_dom gid) in Hdom.
      rewrite Hdom elem_of_filter.
      by auto.
    }
    (* Expose the replicated history and prepared timestamp from keys invariant. *)
    iDestruct (keys_inv_expose_repl_tsprep with "Hkeys") as (tplsk) "(Hkeys & Htpls & %Hdom')".
    (* Agree on tuples from the group and keys invariants. *)
    iDestruct (tuple_repl_big_agree with "Hrepls Htpls") as %->; first by rewrite -Hdom in Hdom'.
    clear Hdom'.
    (* Update the tuples (resetting the prepared timestamp and extending the history). *)
    iMod (tuple_repl_big_update (multiwrite ts wrs tplsg) with "Hrepls Htpls") as "[Hrepls Htpls]".
    { by rewrite multiwrite_dom. }
    (* Prove [wrs ⊆ wrsc] (i.e., the prepare writes is a subset of the global writes). *)
    iAssert (⌜wrs ⊆ wrsc⌝)%I as %Hwrsc.
    { iNamed "Htxn".
      iDestruct (txnres_lookup with "Hresm Hcmt") as "%Hresm".
      iDestruct (big_sepM_lookup with "Hvr") as "Hprep"; first apply Hresm.
      rewrite /= /all_prepared.
      iDestruct (big_sepS_elem_of with "Hprep") as "Hp"; first apply Hgid.
      iDestruct (txnst_lookup with "Hstm Hp") as %Hp.
      iPureIntro.
      rewrite Hdup in Hp. inversion Hp.
      apply map_filter_subseteq.
    }
    (* Prove txn [ts] has committed on [tpls]. *)
    iDestruct (keys_inv_committed with "Hcmt Hkeys Htxn") as "[Hkeys Htxn]".
    { apply Hdom. }
    { apply Hwrsc. }
    { (* Prove prepared timestamp of [tplsg] is [ts]. *)
      intros k tpl Hlookup.
      eapply (pts_consistency log).
      { rewrite Forall_forall.
        intros c Hin.
        rewrite Forall_forall in Hsubsume.
        specialize (Hsubsume _ Hin).
        specialize (Hcg _ Hsubsume).
        rewrite /valid_cmd_in_group in Hcg.
        destruct c; [ | done | done | done].
        by destruct Hcg as [Hts _].
      }
      { apply Hrsm. }
      { apply Hdup. }
      { eapply lookup_weaken; first apply Hlookup.
        transitivity (tpls_group gid tpls); first done.
        rewrite /tpls_group.
        apply map_filter_subseteq.
      }
      { rewrite -Hdom. by eapply elem_of_dom_2. }
    }
    (* Re-establish keys invariant w.r.t. updated tuples. *)
    iDestruct (keys_inv_learn_commit with "Hkeys") as "Hkeys".
    (* Put ownership of tuples back to keys invariant. *)
    iDestruct (keys_inv_merge_repl_tsprep (dom wrs) with "Hkeys Htpls") as "Hkeys".
    { by rewrite multiwrite_dom. }
    iDestruct ("HkeysC" with "Hkeys") as "Hkeys".
    (* Merge ownership of tuples back to group invariant. *)
    iDestruct (tuple_repl_half_multiwrite_disjoint ts wrs with "HreplsO") as "HreplsO".
    { set_solver. }
    rewrite multiwrite_difference_distr.
    iDestruct (big_sepM_difference_combine with "Hrepls HreplsO") as "Hrepls".
    { by apply multiwrite_mono. }
    rewrite multiwrite_tpls_group_commute.
    (* Mark [ts] as committed in the status map. *)
    iMod (txnst_commit ts wrs with "Hstm") as "Hstm"; first apply Hdup.
    iDestruct (big_sepM_insert_2 _ _ ts (StCommitted) with "[] Hca") as "Hca'"; first done.
    by auto with iFrame.
  Qed.

  Lemma group_inv_learn γ gid cpool cmds :
    ∀ log,
    cpool_subsume_log cpool (log ++ cmds) ->
    txn_inv γ -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_with_cpool_no_log γ gid log cpool ==∗
    txn_inv γ ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_with_cpool_no_log γ gid (log ++ cmds) cpool.
  Proof.
    iInduction cmds as [| c l] "IH".
    { iIntros (log Hsubsume) "Htxn Hkeys Hgroup". rewrite app_nil_r. by iFrame. }
    (* rewrite Forall_cons in Hcpool. *)
    (* destruct Hcpool as [Hc Hcpool]. *)
    iIntros (log Hsubsume) "Htxn Hkeys Hgroup".
    rewrite cons_middle app_assoc in Hsubsume.
    rewrite cons_middle app_assoc.
    destruct c.
    { (* Case: [CmdPrep tid wrs] *)
      iMod (group_inv_learn_prepare with "Htxn Hkeys Hgroup") as "(Htxn & Hkeys & Hgroup)".
      { rewrite /cpool_subsume_log 2!Forall_app Forall_singleton in Hsubsume.
        by destruct Hsubsume as [[_ Hc] _].
      }
      by iApply ("IH" with "[] Htxn Hkeys Hgroup").
    }
    { (* Case: [CmdCmt tid] *)
      iMod (group_inv_learn_commit with "Htxn Hkeys Hgroup") as "(Htxn & Hkeys & Hgroup)".
      { rewrite /cpool_subsume_log Forall_app in Hsubsume.
        by destruct Hsubsume as [Hsubsume _].
      }
      by iApply ("IH" with "[] Htxn Hkeys Hgroup").
    }
  Admitted.

End group_inv.
(* TODO: move to distx_group_inv.v once stable. *)
