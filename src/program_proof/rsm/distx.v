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

Definition dbval_from_val (v : val) : option dbval :=
  match v with
  | (#(LitBool b), (#(LitString s), #()))%V => if b then Some (Some s) else Some None
  | _ => None
  end.

Definition dbmod_to_val (x : dbmod) : val :=
  (#(LitString x.1), (dbval_to_val x.2, #())).

Definition dbmod_from_val (v : val) : option dbmod :=
  match v with
  | (#(LitString k), (dbv, #()))%V => match dbval_from_val dbv with
                                     | Some x => Some (k, x)
                                     | _ => None
                                     end
  | _ => None
  end.

#[global]
Instance dbmod_into_val : IntoVal dbmod.
Proof.
  refine {|
      to_val := dbmod_to_val;
      from_val := dbmod_from_val;
      IntoVal_def := ("", None);
    |}.
  intros [k v].
  by destruct v.
Defined.

Definition fstring := {k : string | (String.length k < 2 ^ 64)%nat}.

#[local]
Instance fstring_finite :
  finite.Finite fstring.
Admitted.

(* Definition keys_all : gset string := fin_to_set fstring. *)
Definition keys_all : gset string.
Admitted.

Definition groupid := nat.
Definition gids_all : gset groupid := list_to_set (seq 0 2).

Definition key_to_group (key : dbkey) : groupid.
Admitted.

Definition wrs_group gid (wrs : dbmap) :=
  filter (λ t, key_to_group t.1 = gid) wrs.

(* Note the coercion here. [word] seems to work better with this. *)
Definition valid_ts (ts : nat) := 0 < ts < 2 ^ 64.

Definition valid_wrs (wrs : dbmap) := dom wrs ⊆ keys_all.

Definition valid_key (key : dbkey) := key ∈ keys_all.

Definition tpls_group gid (tpls : gmap dbkey dbtpl) :=
  filter (λ t, key_to_group t.1 = gid) tpls.

Definition keys_group gid (keys : gset dbkey) :=
  filter (λ k, key_to_group k = gid) keys.

Lemma tpls_group_keys_group_dom gid tpls :
  dom (tpls_group gid tpls) = keys_group gid (dom tpls).
Proof. by rewrite /tpls_group /keys_group filter_dom_L. Qed.

Lemma wrs_group_keys_group_dom gid wrs :
  dom (wrs_group gid wrs) = keys_group gid (dom wrs).
Proof. by rewrite /wrs_group /keys_group filter_dom_L. Qed.

Lemma key_to_group_tpls_group key gid tpls :
  key ∈ dom (tpls_group gid tpls) ->
  key_to_group key = gid.
Proof. intros Hdom. rewrite tpls_group_keys_group_dom in Hdom. set_solver. Qed.

Lemma tpls_group_dom {gid tpls0 tpls1} :
  dom tpls0 = dom tpls1 ->
  dom (tpls_group gid tpls0) = dom (tpls_group gid tpls1).
Proof. intros Hdom. by rewrite 2!tpls_group_keys_group_dom Hdom. Qed.

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
| CmdRead (tid : nat) (key : dbkey)
| CmdPrep (tid : nat) (wrs : dbmap)
| CmdCmt (tid : nat)
| CmdAbt (tid : nat).

#[local]
Instance command_eq_decision :
  EqDecision command.
Proof. solve_decision. Qed.

#[local]
Instance command_countable :
  Countable command.
Admitted.

Definition valid_ts_of_command (c : command) :=
  match c with
  | CmdCmt ts => valid_ts ts
  | CmdAbt ts => valid_ts ts
  | CmdPrep ts _ => valid_ts ts
  | CmdRead ts _ => valid_ts ts
  end.

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

Definition not_stuck st := st ≠ Stuck.

Inductive acquiring :=
| Acquired (tpls : gmap dbkey dbtpl)
| NotAcquired.

Definition validate_key (tid : nat) (wr : option dbval) (tpl : option dbtpl) :=
  match wr, tpl with
  | Some _, Some (vs, tsprep) => Some (bool_decide (tsprep = O ∧ length vs ≤ tid)%nat)
  | Some _, None => Some false
  | _, _ => None
  end.

Definition validate (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  map_fold (λ _, andb) true (merge (validate_key tid) wrs tpls).

Lemma map_fold_andb_true `{Countable K} (m : gmap K bool) :
  map_fold (λ _, andb) true m = true ->
  map_Forall (λ _ b, b = true) m.
Proof.
  intros Hfold k b Hkb.
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
Qed.

Lemma validate_true {tid wrs tpls} key :
  is_Some (wrs !! key) ->
  validate tid wrs tpls = true ->
  ∃ l, tpls !! key = Some (l, O) ∧ (length l ≤ tid)%nat.
Proof.
  intros Hsome Hvd.
  destruct Hsome as [v Hv].
  destruct (tpls !! key) as [t |] eqn:Htpls.
  { rewrite /validate in Hvd.
    apply map_fold_andb_true in Hvd.
    specialize (Hvd key).
    rewrite lookup_merge Hv Htpls /= in Hvd.
    destruct t as [vs tsprep].
    case_bool_decide as Hcond; last first.
    { specialize (Hvd false).
      by unshelve epose proof (Hvd _); first reflexivity.
    }
    destruct Hcond as [-> Hlen].
    by eauto.
  }
  rewrite /validate in Hvd.
  apply map_fold_andb_true in Hvd.
  specialize (Hvd key false).
  rewrite lookup_merge Hv Htpls /= in Hvd.
  by unshelve epose proof (Hvd _); first reflexivity.
Qed.

Definition acquire_key (tid : nat) (wr : option dbval) (tpl : option dbtpl) :=
  match wr, tpl with
  | None, Some (vs, tsprep) => Some (vs, tsprep)
  | Some _, Some (vs, _) => Some (vs, tid)
  | _, _ => None
  end.

Definition acquire (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  merge (acquire_key tid) wrs tpls.

(* NB: nonexpanding is not the most precise name, since it also says the domain
is nonshrinking. Something like domain preserving but more concise. *)
Definition mergef_nonexpanding {A B C} (f : option A -> option B -> option C) :=
  ∀ x y, is_Some (f x y) ↔ is_Some y.

Lemma mergef_nonexpanding_Some {A B C} {f : option A -> option B -> option C} x u :
  mergef_nonexpanding f ->
  ∃ v, f x (Some u) = Some v.
Proof.
  intros Hne. specialize (Hne x (Some u)).
  by destruct Hne as [_ [v Hne]]; last eauto.
Qed.

Lemma mergef_nonexpanding_None {A B C} {f : option A -> option B -> option C} x :
  mergef_nonexpanding f ->
  f x None = None.
Proof.
  intros Hne.
  destruct (f _ _) eqn:Hf; last done.
  by apply mk_is_Some, Hne, is_Some_None in Hf.
Qed.

Lemma gmap_nonexpanding_merge_empty `{Countable K} {A B C : Type}
  (m : gmap K A) (f : option A -> option B -> option C) :
  mergef_nonexpanding f ->
  merge f m ∅ = ∅.
Proof.
  intros Hne.
  apply map_eq. intros k.
  rewrite lookup_merge 2!lookup_empty.
  by destruct (m !! k); simpl; first rewrite mergef_nonexpanding_None.
Qed.

Lemma gmap_nonexpanding_merge_dom `{Countable K} {A B C : Type}
  (ma : gmap K A) (mb : gmap K B) (f : option A -> option B -> option C) :
  mergef_nonexpanding f ->
  dom (merge f ma mb) = dom mb.
Proof.
  intros Hne.
  apply set_eq. intros k. rewrite 2!elem_of_dom.
  split; intros Hdom.
  - destruct (ma !! k) as [u |] eqn:Hma, (mb !! k) as [v |] eqn:Hmb.
    + done.
    + by rewrite lookup_merge Hma Hmb /= Hne in Hdom.
    + done.
    + rewrite lookup_merge Hma Hmb /= in Hdom. by apply is_Some_None in Hdom.
  - destruct (ma !! k) as [u |] eqn:Hma, (mb !! k) as [v |] eqn:Hmb.
    + by rewrite lookup_merge Hma Hmb /= Hne.
    + by apply is_Some_None in Hdom.
    + by rewrite lookup_merge Hma Hmb /= Hne.
    + by apply is_Some_None in Hdom.
Qed.

Lemma gmap_nonexpanding_merge_difference_distr `{Countable K} {A B C : Type}
  (ma : gmap K A) (mb1 mb2 : gmap K B) (f : option A -> option B -> option C) :
  mergef_nonexpanding f ->
  merge f ma (mb1 ∖ mb2) = merge f ma mb1 ∖ merge f ma mb2.
Proof.
  intros Hne.
  apply map_eq. intros k.
  rewrite lookup_merge 2!lookup_difference 2!lookup_merge.
  destruct (ma !! k); simpl.
  - destruct (mb2 !! k); simpl.
    + rewrite mergef_nonexpanding_None; last done.
      apply (mergef_nonexpanding_Some (Some a) b) in Hne as [c Hc].
      by rewrite Hc.
    + by rewrite mergef_nonexpanding_None; last done.
  - destruct (mb2 !! k); simpl.
    + apply (mergef_nonexpanding_Some None b) in Hne as [c Hc].
      by rewrite Hc.
    + done.
Qed.

Lemma gmap_nonexpanding_merge_mono `{Countable K} {A B C : Type}
  (ma : gmap K A) (mb1 mb2 : gmap K B) (f : option A -> option B -> option C) :
  mergef_nonexpanding f ->
  mb1 ⊆ mb2 ->
  merge f ma mb1 ⊆ merge f ma mb2.
Proof.
  rewrite 2!map_subseteq_spec.
  intros Hne Hsubseteq.
  intros k c. rewrite 2!lookup_merge.
  destruct (ma !! k); simpl; intros Hkc.
  - destruct (mb1 !! k) eqn:Hmb1; simpl.
    + by erewrite Hsubseteq.
    + by rewrite mergef_nonexpanding_None in Hkc.
  - destruct (mb1 !! k) eqn:Hmb1; simpl.
    + by erewrite Hsubseteq.
    + done.
Qed.

Lemma gmap_nonexpanding_merge_filter_commute `{Countable K} {A B C : Type}
  (P : K -> Prop) {Hdec : ∀ x, Decision (P x)}
  (ma : gmap K A) (mb : gmap K B) (f : option A -> option B -> option C) :
  mergef_nonexpanding f ->
  merge f ma (filter (λ kv, P kv.1) mb) = filter (λ kv, P kv.1) (merge f ma mb).
Proof.
  intros Hne.
  induction mb as [| k t m Hlookup IH] using map_ind.
  { rewrite map_filter_empty. by rewrite gmap_nonexpanding_merge_empty. }
  destruct (decide (P k)) as [Hp | Hn].
  - rewrite map_filter_insert_True; last done.
    apply (mergef_nonexpanding_Some (ma !! k) t) in Hne.
    destruct Hne as [c Hc].
    erewrite <- insert_merge_r; last done.
    erewrite <- insert_merge_r; last done.
    rewrite map_filter_insert_True; last done.
    by rewrite IH.
  - rewrite map_filter_insert_False; last done.
    rewrite delete_notin; last done.
    apply (mergef_nonexpanding_Some (ma !! k) t) in Hne as Hc.
    destruct Hc as [c Hc].
    erewrite <- insert_merge_r; last done.
    rewrite map_filter_insert_False; last done.
    rewrite delete_notin; first apply IH.
    rewrite lookup_merge Hlookup.
    by destruct (ma !! k); simpl; [apply mergef_nonexpanding_None |].
Qed.

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

Definition extend {A} (n : nat) (x : A) (l : list A) :=
  l ++ replicate (n - length l) x.

(* Lemmas about [extend]. *)
Lemma extend_id {A} (n : nat) (x : A) (l : list A) :
  (n ≤ length l)%nat ->
  extend n x l = l.
Proof.
  intros Hlen. rewrite /extend. replace (n - _)%nat with O by lia.
  by rewrite /= app_nil_r.
Qed.

Lemma extend_length {A} (n : nat) (x : A) (l : list A) :
  length (extend n x l) = (n - length l + length l)%nat.
Proof. rewrite app_length replicate_length. lia. Qed.

Lemma extend_length_ge_n {A} (n : nat) (x : A) (l : list A) :
  (n ≤ length (extend n x l))%nat.
Proof. rewrite extend_length. lia. Qed.

Definition last_extend {A} (n : nat) (l : list A) :=
  match last l with
  | None => []
  | Some x => extend n x l
  end.

(* Lemmas about [last_extend]. *)
Lemma last_extend_id {A} (n : nat) (l : list A) :
  (n ≤ length l)%nat ->
  last_extend n l = l.
Proof.
  intros Hlen. rewrite /last_extend.
  destruct (last l) eqn:Hl; first by apply extend_id.
  symmetry.
  by apply last_None.
Qed.

Lemma last_extend_length {X : Type} (n : nat) (l : list X) :
  l ≠ [] ->
  length (last_extend n l) = (n - length l + length l)%nat.
Proof.
  intros Hl. rewrite -last_is_Some in Hl. destruct Hl as [x Hl].
  rewrite /last_extend Hl extend_length.
  lia.
Qed.

Lemma last_extend_length_ge_n {A} (n : nat) (l : list A) :
  l ≠ [] ->
  (n ≤ length (last_extend n l))%nat.
Proof. intros Hl. rewrite last_extend_length; [lia | done]. Qed.

Lemma last_extend_length_eq_n_or_same {A} (n : nat) (l : list A) :
  length (last_extend n l) = n ∨ length (last_extend n l) = length l.
Proof.
  destruct (decide (l = [])) as [-> | Hne]; first by right.
  rewrite last_extend_length; last done.
  lia.
Qed.

Lemma last_last_extend {A} (n : nat) (l : list A) :
  last (last_extend n l) = last l.
Proof.
  destruct (last l) as [x |] eqn:Hlast; last by rewrite /last_extend Hlast.
  rewrite /last_extend Hlast /extend last_app.
  destruct (last (replicate _ _)) eqn:Hl; last done.
  apply last_Some_elem_of, elem_of_replicate_inv in Hl.
  by rewrite Hl.
Qed.

Lemma last_extend_twice {A} (n1 n2 : nat) (l : list A) :
  last_extend n1 (last_extend n2 l) = last_extend (n1 `max` n2) l.
Proof.
  destruct (decide (l = [])) as [-> | Hne]; first done.
  destruct (last l) as [x |] eqn:Hlast; last by rewrite last_None in Hlast.
  pose proof (last_last_extend n2 l) as Hn2.
  rewrite {1}/last_extend Hn2 Hlast /last_extend Hlast /extend -app_assoc.
  rewrite -replicate_add app_length replicate_length.
  (* wow how does lia solve this *)
  by replace (n2 - _ + _)%nat with (n1 `max` n2 - length l)%nat by lia.
Qed.

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

Lemma multiwrite_unmodified {tid wrs tpls key} :
  wrs !! key = None ->
  (multiwrite tid wrs tpls) !! key = tpls !! key.
Proof.
  intros Hlookup.
  rewrite lookup_merge Hlookup /=.
  by destruct (tpls !! key) as [t |] eqn:Ht.
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

Definition release_key (tid : nat) (wr : option dbval) (tpl : option dbtpl) :=
  match wr, tpl with
  | None, Some _ => tpl
  | Some _, Some (vs, _) => Some (vs, O)
  | _, _ => None
  end.

Lemma release_key_nonexpanding ts :
  mergef_nonexpanding (release_key ts).
Proof. intros x y. by destruct x, y as [[h t] |]. Qed.

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

Lemma release_dom {tid wrs tpls} :
  dom (release tid wrs tpls) = dom tpls.
Proof. apply gmap_nonexpanding_merge_dom, release_key_nonexpanding. Qed.

Lemma release_difference_distr {tid wrs tpls tplsd} :
  release tid wrs (tpls ∖ tplsd) =
  release tid wrs tpls ∖ release tid wrs tplsd.
Proof. apply gmap_nonexpanding_merge_difference_distr, release_key_nonexpanding. Qed.

Lemma release_mono tid wrs tpls1 tpls2 :
  tpls1 ⊆ tpls2 ->
  release tid wrs tpls1 ⊆ release tid wrs tpls2.
Proof. apply gmap_nonexpanding_merge_mono, release_key_nonexpanding. Qed.

Lemma release_tpls_group_commute tid wrs tpls gid :
  release tid wrs (tpls_group gid tpls) = tpls_group gid (release tid wrs tpls).
Proof.
  set P := (λ x, key_to_group x = gid).
  pose proof (release_key_nonexpanding tid) as Hne.
  by apply (gmap_nonexpanding_merge_filter_commute P wrs tpls) in Hne.
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
  if decide (tsprep = 0 ∨ tid ≤ tsprep)%nat
  then (last_extend tid vs, tsprep)
  else (vs, tsprep).

Definition apply_read st (tid : nat) (key : dbkey) :=
  match st with
  | State stm tpls =>
      match tpls !! key with
      | Some (vs, tsprep) => State stm (<[ key := (read tid vs tsprep) ]> tpls)
      | None => Stuck
      end
  | Stuck => Stuck
  end.

Lemma insert_tpls_group_commute key tpl tpls gid :
  key_to_group key = gid ->
  <[key := tpl]> (tpls_group gid tpls) = tpls_group gid (<[key := tpl]> tpls).
Proof.
  intros Hgid.
  apply map_eq. intros k.
  destruct (decide (key = k)) as [-> | Hne].
  { rewrite lookup_insert /tpls_group.
    by rewrite (map_lookup_filter_Some_2 _ _ k tpl); [| rewrite lookup_insert |].
  }
  rewrite lookup_insert_ne; last done.
  rewrite /tpls_group map_filter_insert.
  by case_decide as H; first rewrite lookup_insert_ne.
Qed.

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
    by destruct (try_acquire _ _ _); inversion Heq;
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
  rewrite elem_of_list_lookup in Hprep.
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
  destruct (try_acquire _ _ _).
  { eapply foldl_apply_cmd_from_stm_present; first apply Hrsm.
    by rewrite lookup_insert.
  }
  { eapply foldl_apply_cmd_from_stm_present; first apply Hrsm.
    by rewrite lookup_insert.
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
    destruct (try_acquire _ _ _) eqn:Hacq; last by inversion Hrsm.
    inversion Hrsm. subst tpls'.
    rewrite /try_acquire in Hacq.
    destruct (validate _ _ _); last done.
    inversion Hacq.
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

(* Note: RSM invariants can either be defined as properties about [apply_cmds],
or explicit invariants materialized in [group_inv]. The first form gives a
minimal set of invariants and allow replicas to deduce those properties, but the
proofs can be a bit repetitive and hard to comprehend. The second form is more
verbose (and weaker since it does not directly allows replica to deduce the
invariants), but might yield more informative lemmas and proofs. *)

(* Some of these lemmas about [apply_cmds] are indeed used in the replica proof,
so it seems like the first approach is preferred. *)

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

(* TODO: Clean up the naming about wrs/pwrs validity. *)
Definition pwrs_valid log :=
  ∀ stm tpls ts pwrs,
  apply_cmds log = State stm tpls ->
  stm !! ts = Some (StPrepared pwrs) ->
  valid_wrs pwrs.

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

Definition valid_pwrs_of_command c :=
  match c with
  | CmdPrep _ pwrs => valid_wrs pwrs
  | _ => True
  end.

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
    rewrite lookup_insert in Htpl.
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
    destruct (try_acquire _ _ _) as [tpls' |] eqn:Hacq;
      inversion Happly; subst stmc tplsc; last first.
    { (* Case: Fail to acquire lock. *) by eapply Hwf. }
    (* Case: Successfully acquire lock. *)
    rewrite /try_acquire in Hacq.
    destruct (validate _ _ _) eqn:Hvd; last done.
    inversion Hacq. subst tpls'.
    destruct (wrs !! keyx) as [v |] eqn:Hwrs; last first.
    { rewrite acquire_unmodified in Htpl; last done.
      by eapply Hwf.
    }
    unshelve epose proof (validate_true keyx _ Hvd) as (h & Hh & Hlen); first done.
    rewrite /acquire lookup_merge Hwrs Hh /= in Htpl.
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

Lemma pwrs_valid_snoc l c :
  valid_pwrs_of_command c ->
  pwrs_valid l ->
  pwrs_valid (l ++ [c]).
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
    destruct (try_acquire _ _ _) as [tpls' |] eqn:Hacq;
      inversion Happly; subst stmc tplsc; last first.
    { (* Case: Fail to acquire lock. *)
      destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hpwrs.
    }
    (* Case: Successfully acquire lock. *)
    rewrite /try_acquire in Hacq.
    destruct (validate _ _ _) eqn:Hvd; last done.
    inversion Hacq. subst tpls'.
    destruct (decide (ts = tid)) as [-> | Hne]; last first.
    { rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hpwrs.
    }
    rewrite lookup_insert in Hstm.
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
      { by rewrite lookup_insert in Hstm. }
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
      { by rewrite lookup_insert in Hstm. }
      rewrite lookup_insert_ne in Hstm; last done.
      by eapply Hpwrs.
    }
    destruct st; inversion Happly; subst stmc tplsc; last by eapply Hpwrs.
    (* Case: Prepared then abort. *)
    destruct (decide (ts = tid)) as [-> | Hne].
    { by rewrite lookup_insert in Hstm. }
    rewrite lookup_insert_ne in Hstm; last done.
    by eapply Hpwrs.
  }
Qed.

Lemma pwrs_valid_nil :
  pwrs_valid [].
Proof.
  intros stm tpls ts pwrs Happly Hpwrs.
  rewrite /apply_cmds /= /init_rpst in Happly.
  set_solver.
Qed.

Lemma pwrs_validity_step l1 l2 :
  Forall (λ c, valid_pwrs_of_command c) l2 ->
  pwrs_valid l1 ->
  pwrs_valid (l1 ++ l2).
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

Lemma pwrs_validity l :
  Forall (λ c, valid_pwrs_of_command c) l ->
  pwrs_valid l.
Proof.
  intros Hpwrs.
  apply (pwrs_validity_step [] l); [done | apply pwrs_valid_nil].
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
    destruct (try_acquire _ _ _) as [tpls' |] eqn:Hacq;
      inversion Happly; subst stmc tplsc; last first.
    { destruct (decide (ts = tid)) as [-> | Hne].
      { by rewrite lookup_insert in Hstm. }
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
    rewrite lookup_insert /read in Htpls.
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
      destruct (validate_true _ Hwrs1 Hvd) as (h & Htpls & _).
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
      destruct (validate_true _ Hwrs2 Hvd) as (h & Htpls & _).
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

Definition valid_pwrs gid wrs pwrs :=
  valid_wrs wrs ∧ pwrs ≠ ∅ ∧ pwrs = wrs_group gid wrs.

Lemma set_Forall_Forall_subsume `{Countable A} (l : list A) (s : gset A) P :
  set_Forall P s ->
  Forall (λ x, x ∈ s) l ->
  Forall P l.
Proof. do 2 rewrite Forall_forall. intros HP Hl x Hin. by auto. Qed.
  
Inductive action :=
| ActCmt (tid : nat) (wrs : dbmap)
| ActRead (tid : nat) (key : dbkey).

Definition diff_by_cmtd
  (repl cmtd : list dbval) (kmod : dbkmod) (ts : nat) :=
  match kmod !! ts with
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
  kmod !! ts = Some v ->
  diff_by_cmtd repl cmtd kmod ts ->
  diff_by_cmtd (last_extend ts repl ++ [v]) cmtd kmod O.
Proof.
  intros Hz Hts Hdiff.
  rewrite /diff_by_cmtd Hts in Hdiff.
  rewrite /diff_by_cmtd Hz.
  split; last done.
  (* by the time repl catches up cmtd, they are equal, hence using 0 here *)
  exists O.
  by rewrite Hdiff {2}/last_extend last_snoc /extend /= app_nil_r.
Qed.

Lemma diff_by_cmtd_inv_learn_abort {repl cmtd kmod} ts :
  kmod !! O = None ->
  kmod !! ts = None ->
  diff_by_cmtd repl cmtd kmod ts ->
  diff_by_cmtd repl cmtd kmod O.
Proof.
  intros Hz Hts Hdiff.
  rewrite /diff_by_cmtd Hts in Hdiff.
  rewrite /diff_by_cmtd Hz.
  by destruct Hdiff as [Hdiff _].
Qed.

Lemma diff_by_cmtd_inv_learn_read_free {repl cmtd kmod} ts :
  kmod !! O = None ->
  diff_by_cmtd repl cmtd kmod O ->
  diff_by_cmtd (last_extend ts repl) cmtd kmod O.
Proof.
  intros Hz. rewrite /diff_by_cmtd Hz.
  intros [[ts' Hrepl] _].
  split; last done.
  rewrite Hrepl.
  exists (ts `max` ts')%nat.
  apply last_extend_twice.
Qed.

Lemma diff_by_cmtd_inv_learn_read_acquired {repl cmtd kmod} ts tslock :
  (ts ≤ tslock)%nat ->
  diff_by_cmtd repl cmtd kmod tslock ->
  diff_by_cmtd (last_extend ts repl) cmtd kmod tslock.
Proof.
  rewrite /diff_by_cmtd. intros Hlt Hdiff.
  destruct (kmod !! tslock) as [v |] eqn:Hv.
  { (* Case: Tuple committed by [tslock]. *)
    rewrite last_extend_twice.
    by replace (_ `max` _)%nat with tslock by lia.
  }
  destruct Hdiff as [[ts' Hrepl] Hlen].
  (* Case: Tuple prepared but not committed by [tslock] yet. *)
  split.
  { rewrite Hrepl last_extend_twice. by eauto. }
  intros Hnz. specialize (Hlen Hnz).
  destruct (decide (repl = [])) as [-> | Hne]; first done.
  rewrite last_extend_length; [lia | done].
Qed.

Lemma cmtd_impl_prep_inv_abort {resm wrsm} ts :
  cmtd_impl_prep resm wrsm ->
  cmtd_impl_prep (<[ts:=ResAborted]> resm) wrsm.
Proof.
  intros Hcip ts'.
  destruct (decide (ts' = ts)) as [-> | Hne]; first by rewrite lookup_insert.
  rewrite lookup_insert_ne; last done.
  by apply Hcip.
Qed.

Lemma tmods_kmods_consistent_inv_abort {resm kmods} ts :
  resm !! ts = None ->
  tmods_kmods_consistent (resm_to_tmods resm) kmods ->
  tmods_kmods_consistent (resm_to_tmods (<[ts:=ResAborted]> resm)) kmods.
Proof.
  intros Hnotin Htkc.
  rewrite /resm_to_tmods omap_insert_None; last done.
  rewrite delete_notin; first done.
  by rewrite lookup_omap Hnotin.
Qed.
(* TODO: move to distx_inv_proof.v once stable. *)

(* TODO: move to misc.v once stable. *)
Lemma prefix_snoc {A : Type} (l1 l2 : list A) x :
  prefix l1 (l2 ++ [x]) ->
  prefix l1 l2 ∨ l1 = l2 ++ [x].
Proof.
  intros Hprefix.
  destruct Hprefix as [l Hprefix].
  destruct l as [| y l].
  { right. by rewrite app_nil_r in Hprefix. }
  left.
  rewrite /prefix.
  apply app_eq_inv in Hprefix.
  destruct Hprefix as [(k & Hprefix & _) | (k & Hprefix & Hx)]; first by eauto.
  destruct k.
  { rewrite app_nil_r in Hprefix. exists nil. by rewrite app_nil_r. }
  inversion Hx as [[Ha Hcontra]].
  by apply app_cons_not_nil in Hcontra.
Qed.
(* TODO: move to misc.v once stable. *)

(* TODO: move to distx_own.v once stable. *)
Class distx_ghostG (Σ : gFunctors).

Record distx_names := {}.

Record replica_names := {}.

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

  (* Transaction write-sets. This resource allows us to specify that [CmdPrep]
  is submitted to only the participant group, as encoded in
  [safe_submit]. Without which we won't be able to prove that learning a commit
  under an aborted state is impossible, as a non-participant group could have
  received [CmdPrep] and aborted. *)
  Definition txnwrs_auth γ (wrsm : gmap nat dbmap) : iProp Σ.
  Admitted.

  Definition txnwrs_receipt γ (ts : nat) (wrs : dbmap) : iProp Σ.
  Admitted.

  #[global]
  Instance txnwrs_receipt_persistent γ ts wrs  :
    Persistent (txnwrs_receipt γ ts wrs).
  Admitted.

  Lemma txnwrs_lookup γ wrsm ts wrs :
    txnwrs_auth γ wrsm -∗
    txnwrs_receipt γ ts wrs -∗
    ⌜wrsm !! ts = Some wrs⌝.
  Admitted.

  (* Custom transaction status. *)
  Definition txnprep_auth γ (gid : groupid) (pm : gmap nat bool) : iProp Σ.
  Admitted.

  Definition txnprep_receipt γ (gid : groupid) (ts : nat) (p : bool) : iProp Σ.
  Admitted.

  #[global]
  Instance txnprep_lb_persistent γ gid ts p :
    Persistent (txnprep_receipt γ gid ts p).
  Admitted.

  Definition txnprep_prep γ gid ts :=
    txnprep_receipt γ gid ts true.

  Definition txnprep_unprep γ gid ts :=
    txnprep_receipt γ gid ts false.

  Lemma txnprep_insert {γ gid pm} ts p :
    pm !! ts = None ->
    txnprep_auth γ gid pm ==∗
    txnprep_auth γ gid (<[ts := p]> pm).
  Admitted.

  Lemma txnprep_witness γ gid pm ts p :
    pm !! ts = Some p ->
    txnprep_auth γ gid pm -∗
    txnprep_receipt γ gid ts p.
  Admitted.

  Lemma txnprep_lookup γ gid pm ts p :
    txnprep_auth γ gid pm -∗
    txnprep_receipt γ gid ts p -∗
    ⌜pm !! ts = Some p⌝.
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

  (* Paxos log and command pool. TODO: rename clog to just log. *)
  Definition clog_half γ (gid : groupid) (log : dblog) : iProp Σ.
  Admitted.

  Definition clog_lb γ (gid : groupid) (log : dblog) : iProp Σ.
  Admitted.

  #[global]
  Instance clog_lb_persistent γ gid log :
    Persistent (clog_lb γ gid log).
  Admitted.

  Definition clog_lbs γ (logs : gmap groupid dblog) : iProp Σ :=
    [∗ map] gid ↦ log ∈ logs, clog_lb γ gid log.

  Definition cpool_half γ (gid : groupid) (cpool : gset command) : iProp Σ.
  Admitted.

  Definition cmd_receipt γ (gid : groupid) (lsn : nat) (term : nat) (c : command) : iProp Σ.
  Admitted.

  #[global]
  Instance cmd_receipt_persistent γ gid lsn term c :
    Persistent (cmd_receipt γ gid lsn term c).
  Admitted.

  Lemma log_witness γ gid log :
    clog_half γ gid log -∗
    clog_lb γ gid log.
  Admitted.

  Lemma log_prefix γ gid log logp :
    clog_half γ gid log -∗
    clog_lb γ gid logp -∗
    ⌜prefix logp log⌝.
  Admitted.

  Lemma log_lb_prefix γ gid logp1 logp2 :
    clog_lb γ gid logp1 -∗
    clog_lb γ gid logp2 -∗
    ⌜prefix logp1 logp2 ∨ prefix logp2 logp1⌝.
  Admitted.

  Lemma log_lb_weaken {γ gid} logp1 logp2 :
    prefix logp1 logp2 ->
    clog_lb γ gid logp2 -∗
    clog_lb γ gid logp1.
  Admitted.

  Definition cpool_subsume_log (cpool : gset command) (log : list command) :=
    Forall (λ c, c ∈ cpool) log.

  Lemma log_cpool_incl γ gid log cpool :
    clog_half γ gid log -∗
    cpool_half γ gid cpool -∗
    ⌜cpool_subsume_log cpool log⌝.
  Admitted.

  (* Global timestamp. *)
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

  Definition all_prepared γ ts keys : iProp Σ :=
    [∗ set] gid ∈ ptgroups keys, txnprep_prep γ gid ts.

  (* TODO: probably need to refer to [wrs] when proving in the case of learning
  a commit under an aborted state. *)
  Definition some_aborted γ ts : iProp Σ :=
    ∃ gid, txnprep_unprep γ gid ts.

  Definition valid_res γ ts res : iProp Σ :=
    match res with
    | ResCommitted wrs => all_prepared γ ts (dom wrs)
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

  (* TODO: better naming. *)
  
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

  Definition key_inv_prepared_no_repl_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    ∃ kmodc,
      "Hkey" ∷ key_inv_with_kmodc_no_repl_tsprep γ key kmodc repl tsprep ∗
      "%Hnc" ∷ ⌜kmodc !! tsprep = None⌝.

  (** The [StAborted] branch says that a transaction is aborted globally if it
  is aborted locally on some replica (the other direction is encoded in
  [safe_submit]). This gives contradiction when learning a commit command under
  an aborted state. *)
  Definition txn_token γ gid ts st : iProp Σ :=
    match st with
    | StPrepared _ => txnprep_prep γ gid ts
    | StCommitted => (∃ wrs, txnres_cmt γ ts wrs)
    | StAborted => txnres_abt γ ts
    end.

  #[global]
  Instance txn_token_persistent γ gid ts st :
    Persistent (txn_token γ gid ts st).
  Proof. destruct st; apply _. Qed.

  Definition txn_tokens γ gid log : iProp Σ :=
    ∀ logp stm tpls,
    ⌜prefix logp log⌝ -∗
    ⌜apply_cmds logp = State stm tpls⌝ -∗
    ([∗ map] ts ↦ st ∈ stm, txn_token γ gid ts st)%I.

  Definition safe_read gid ts key :=
    valid_ts ts ∧ valid_key key ∧ key_to_group key = gid.

  Definition safe_prepare γ gid ts pwrs : iProp Σ :=
    ∃ wrs, txnwrs_receipt γ ts wrs ∧ ⌜valid_ts ts ∧ valid_pwrs gid wrs pwrs⌝.

  Definition safe_commit γ gid ts : iProp Σ :=
    ∃ wrs, txnres_cmt γ ts wrs ∧ ⌜valid_ts ts ∧ gid ∈ ptgroups (dom wrs)⌝.

  Definition safe_abort γ ts : iProp Σ :=
    txnres_abt γ ts ∧ ⌜valid_ts ts⌝.

  Definition safe_submit γ gid (c : command) : iProp Σ :=
    match c with
    | CmdRead ts key => ⌜safe_read gid ts key⌝
    (* Enforces [CmdPrep] is submitted to only participant groups, and partial
    writes is part of the global commit, which we would likely need with
    coordinator recovery. *)
    | CmdPrep ts pwrs => safe_prepare γ gid ts pwrs
    (* Enforces [CmdCmt] is submitted to only participant groups. *)
    | CmdCmt ts => safe_commit γ gid ts
    | CmdAbt ts => safe_abort γ ts
    end.

  #[global]
  Instance safe_submit_persistent γ gid c :
    Persistent (safe_submit γ gid c).
  Proof. destruct c; apply _. Qed.

  Definition valid_prepared γ gid ts st : iProp Σ :=
    match st with
    | StPrepared pwrs => safe_prepare γ gid ts pwrs
    | _ => True
    end.

  #[global]
  Instance valid_prepared_persistent γ gid ts st :
    Persistent (valid_prepared γ gid ts st).
  Proof. destruct st; apply _. Qed.

  Definition group_inv_no_log_no_cpool
    γ (gid : groupid) (log : dblog) (cpool : gset command) : iProp Σ :=
    ∃ (pm : gmap nat bool) (stm : gmap nat txnst) (tpls : gmap dbkey dbtpl),
      "Hpm"     ∷ txnprep_auth γ gid pm ∗
      "Hrepls"  ∷ ([∗ map] key ↦ tpl ∈ tpls_group gid tpls, tuple_repl_half γ key tpl) ∗
      "#Htks"   ∷ txn_tokens γ gid log ∗
      "#Hvp"    ∷ ([∗ map] ts ↦ st ∈ stm, valid_prepared γ gid ts st) ∗
      "#Hvc"    ∷ ([∗ set] c ∈ cpool, safe_submit γ gid c) ∗
      "%Hrsm"   ∷ ⌜apply_cmds log = State stm tpls⌝ ∗
      "%Hdompm" ∷ ⌜dom pm ⊆ dom stm⌝.

  Definition group_inv_no_log_with_cpool
    γ (gid : groupid) (log : dblog) (cpool : gset command) : iProp Σ :=
    "Hcpool" ∷ cpool_half γ gid cpool ∗
    "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

  Definition group_inv_no_log γ (gid : groupid) (log : dblog) : iProp Σ :=
    ∃ (cpool : gset command),
      "Hcpool" ∷ cpool_half γ gid cpool ∗
      "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

  Definition group_inv_no_cpool γ (gid : groupid) (cpool : gset command) : iProp Σ :=
    ∃ (log : dblog),
      "Hlog"   ∷ clog_half γ gid log ∗
      "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

  Definition group_inv γ (gid : groupid) : iProp Σ :=
    ∃ (log : dblog) (cpool : gset command),
      "Hlog"   ∷ clog_half γ gid log ∗
      "Hcpool" ∷ cpool_half γ gid cpool ∗
      "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

  Definition distxN := nroot .@ "distx".

  Definition distx_inv γ : iProp Σ :=
    (* txn invariants *)
    "Htxn"    ∷ txn_inv γ ∗
    (* keys invariants *)
    "Hkeys"   ∷ ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    (* groups invariants *)
    "Hgroups" ∷ ([∗ set] gid ∈ gids_all, group_inv γ gid).

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

  Lemma group_inv_extract_log_expose_cpool {γ} gid :
    group_inv γ gid -∗
    ∃ log cpool,
      clog_half γ gid log ∗
      group_inv_no_log_with_cpool γ gid log cpool.
  Proof. iIntros "Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_merge_log_hide_cpool {γ gid} log cpool :
    clog_half γ gid log -∗
    group_inv_no_log_with_cpool γ gid log cpool -∗
    group_inv γ gid.
  Proof. iIntros "Hlog Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_extract_log {γ} gid :
    group_inv γ gid -∗
    ∃ log,
      clog_half γ gid log ∗
      group_inv_no_log γ gid log.
  Proof. iIntros "Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_merge_log {γ gid} log :
    clog_half γ gid log -∗
    group_inv_no_log γ gid log -∗
    group_inv γ gid.
  Proof. iIntros "Hlog Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_extract_cpool {γ} gid :
    group_inv γ gid -∗
    ∃ cpool,
      cpool_half γ gid cpool ∗
      group_inv_no_cpool γ gid cpool.
  Proof. iIntros "Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_merge_cpool {γ gid} cpool :
    cpool_half γ gid cpool -∗
    group_inv_no_cpool γ gid cpool -∗
    group_inv γ gid.
  Proof. iIntros "Hcpool Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  (* TODO: might not need these anymore once update the learn_prepare proof to
  be more consistent with that of learn_commit. *)
  Definition keys_except_group gid (keys : gset dbkey) :=
    filter (λ x, key_to_group x ≠ gid) keys.

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

  Lemma txn_tokens_inv_learn_prepare_noop {γ gid log stm tpls ts} pwrs :
    apply_cmds log = State stm tpls ->
    is_Some (stm !! ts) ->
    txn_tokens γ gid log -∗
    txn_tokens γ gid (log ++ [CmdPrep ts pwrs]).
  Proof.
    iIntros (Hrsm Hstm) "Htks".
    iIntros (logp stmp tplsp Hprefix Hrsmp).
    destruct (prefix_snoc _ _ _ Hprefix) as [Hlogp | ->].
    { by iApply "Htks". }
    destruct Hstm as [st Hstm].
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hstm in Hrsmp.
    inversion Hrsmp. subst stmp.
    by iApply "Htks".
  Qed.

  Lemma txn_tokens_inv_learn_prepare_prepared γ gid log stm tpls ts pwrs :
    apply_cmds log = State stm tpls ->
    validate ts pwrs tpls = true ->
    txnprep_prep γ gid ts -∗
    txn_tokens γ gid log -∗
    txn_tokens γ gid (log ++ [CmdPrep ts pwrs]).
  Proof.
    iIntros (Hrsm Hvd) "Hprep Htks".
    destruct (stm !! ts) eqn:Hstm.
    { by iDestruct (txn_tokens_inv_learn_prepare_noop pwrs with "Htks") as "Htks". }
    iIntros (logp stmp tplsp Hprefix Hrsmp).
    destruct (prefix_snoc _ _ _ Hprefix) as [Hlogp | ->].
    { by iApply "Htks". }
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hstm /try_acquire Hvd in Hrsmp.
    inversion Hrsmp. subst stmp.
    iApply (big_sepM_insert_2 with "[Hprep] [Htks]"); first done.
    by iApply "Htks".
  Qed.

  Lemma txn_tokens_inv_learn_prepare_aborted γ gid log stm tpls ts pwrs :
    apply_cmds log = State stm tpls ->
    validate ts pwrs tpls = false ->
    txnres_abt γ ts -∗
    txn_tokens γ gid log -∗
    txn_tokens γ gid (log ++ [CmdPrep ts pwrs]).
  Proof.
    iIntros (Hrsm Hvd) "Habt Htks".
    destruct (stm !! ts) eqn:Hstm.
    { by iDestruct (txn_tokens_inv_learn_prepare_noop pwrs with "Htks") as "Htks". }
    iIntros (logp stmp tplsp Hprefix Hrsmp).
    destruct (prefix_snoc _ _ _ Hprefix) as [Hlogp | ->].
    { by iApply "Htks". }
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hstm /try_acquire Hvd in Hrsmp.
    inversion Hrsmp. subst stmp.
    iApply (big_sepM_insert_2 with "[Habt] [Htks]"); first done.
    by iApply "Htks".
  Qed.

  Lemma txn_tokens_inv_learn_commit γ gid log ts :
    (∃ wrs, txnres_cmt γ ts wrs) -∗
    txn_tokens γ gid log -∗
    txn_tokens γ gid (log ++ [CmdCmt ts]).
  Proof.
    iIntros "[%wrs Hcmt] Htks".
    iIntros (logp stmp tplsp Hprefix Hrsmp).
    destruct (prefix_snoc _ _ _ Hprefix) as [Hlogp | ->].
    { by iApply "Htks". }
    rewrite /apply_cmds foldl_snoc /= in Hrsmp.
    destruct (foldl _ _ _) eqn:Hrsm; last done.
    simpl in Hrsmp.
    destruct (txns !! ts) as [st |]; last done.
    destruct st as [pwrs | |] eqn:Hst; last done.
    { inversion Hrsmp. subst stmp.
      iApply (big_sepM_insert_2 with "[Hcmt] [Htks]"); first by iFrame.
      by iApply "Htks".
    }
    inversion Hrsmp. subst stmp.
    by iApply "Htks".
  Qed.

  Lemma txn_tokens_inv_learn_abort γ gid log ts :
    txnres_abt γ ts -∗
    txn_tokens γ gid log -∗
    txn_tokens γ gid (log ++ [CmdAbt ts]).
  Proof.
    iIntros "Habt Htks".
    iIntros (logp stmp tplsp Hprefix Hrsmp).
    destruct (prefix_snoc _ _ _ Hprefix) as [Hlogp | ->].
    { by iApply "Htks". }
    rewrite /apply_cmds foldl_snoc /= in Hrsmp.
    destruct (foldl _ _ _) eqn:Hrsm; last done.
    simpl in Hrsmp.
    destruct (txns !! ts) as [st |]; last first.
    { inversion_clear Hrsmp.
      iApply (big_sepM_insert_2 with "[Habt] [Htks]"); first by iFrame.
      by iApply "Htks".
    }
    destruct st as [pwrs | |] eqn:Hst; inversion Hrsmp; subst stmp.
    { iApply (big_sepM_insert_2 with "[Habt] [Htks]"); first by iFrame.
      by iApply "Htks".
    }
    by iApply "Htks".
  Qed.

  Lemma txn_tokens_inv_learn_read {γ gid log} ts key :
    txn_tokens γ gid log -∗
    txn_tokens γ gid (log ++ [CmdRead ts key]).
  Proof.
    iIntros "Htks".
    iIntros (logp stmp tplsp Hprefix Hrsmp).
    destruct (prefix_snoc _ _ _ Hprefix) as [Hlogp | ->].
    { by iApply "Htks". }
    rewrite /apply_cmds foldl_snoc /= in Hrsmp.
    destruct (foldl _ _ _) eqn:Hrsm; last done.
    simpl in Hrsmp.
    destruct (tpls !! key) as [[h t] |]; last done.
    inversion Hrsmp. subst stmp.
    by iApply "Htks".
  Qed.

  Lemma group_inv_no_log_witness_txn_token {γ gid log} loga stm tpls ts st :
    prefix loga log ->
    apply_cmds loga = State stm tpls ->
    stm !! ts = Some st ->
    group_inv_no_log γ gid log -∗
    txn_token γ gid ts st.
  Proof.
    iIntros (Hprefix Hrsm Hstm) "Hgroup".
    do 2 iNamed "Hgroup".
    iDestruct ("Htks" with "[] []") as "Htksm".
    { iPureIntro. apply Hprefix. }
    { iPureIntro. apply Hrsm. }
    by iDestruct (big_sepM_lookup with "Htksm") as "Htk"; first apply Hstm.
  Qed.

  Lemma key_inv_extract_repl_tsprep {γ} key :
    key_inv γ key -∗
    ∃ tpl, key_inv_no_repl_tsprep γ key tpl.1 tpl.2 ∗ tuple_repl_half γ key tpl.
  Proof.
    iIntros "Hkey".
    iNamed "Hkey". iNamed "Hprop".
    rewrite /tuple_repl_half.
    iExists (repl, tsprep).
    iFrame "∗ # %".
  Qed.

  Lemma keys_inv_extract_repl_tsprep {γ} keys :
    ([∗ set] key ∈ keys, key_inv γ key) -∗
    ∃ tpls, ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) ∗
            ([∗ map] key ↦ tpl ∈ tpls, tuple_repl_half γ key tpl) ∧
            ⌜dom tpls = keys⌝.
  Proof.
    iIntros "Hkeys".
    iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
    { iIntros (k Hk) "Hkey". iApply (key_inv_extract_repl_tsprep with "Hkey"). }
    iDestruct (big_sepS_exists_sepM with "Hkeys") as (tpls Hdom) "Htpls".
    iDestruct (big_sepM_sep with "Htpls") as "[Hkeys Htpls]".
    by iFrame.
  Qed.

  Lemma key_inv_merge_repl_tsprep {γ} key tpl :
    key_inv_no_repl_tsprep γ key tpl.1 tpl.2 -∗
    tuple_repl_half γ key tpl -∗
    key_inv γ key.
  Proof.
    iIntros "Hkey Htpl".
    iNamed "Hkey". iDestruct "Htpl" as "[Hhist Hts]".
    iFrame "∗ #".
  Qed.

  Lemma keys_inv_merge_repl_tsprep {γ tpls} keys :
    dom tpls = keys ->
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) -∗
    ([∗ map] key ↦ tpl ∈ tpls, tuple_repl_half γ key tpl) -∗
    ([∗ set] key ∈ keys, key_inv γ key).
  Proof.
    iIntros (Hdom) "Hkeys Htpls".
    iDestruct (big_sepM_sep_2 with "Hkeys Htpls") as "Htpls".
    rewrite -Hdom -big_sepM_dom.
    iApply (big_sepM_mono with "Htpls").
    iIntros (k t Ht) "[Hkey Htpl]".
    iApply (key_inv_merge_repl_tsprep with "Hkey Htpl").
  Qed.

  Lemma key_inv_no_repl_tsprep_unseal_kmodc γ key repl tsprep :
    key_inv_no_repl_tsprep γ key repl tsprep -∗
    ∃ kmodc, key_inv_with_kmodc_no_repl_tsprep γ key kmodc repl tsprep.
  Proof. iIntros "Hkey". iNamed "Hkey". iFrame "% # ∗". Qed.

  Lemma key_inv_not_committed γ gid ts pm key kmodc tpl :
    gid = key_to_group key ->
    pm !! ts = None ->
    txnprep_auth γ gid pm -∗
    txn_inv γ -∗
    key_inv_with_kmodc_no_repl_tsprep γ key kmodc tpl.1 tpl.2 -∗
    ⌜kmodc !! ts = None⌝.
  Proof.
    iIntros (Hgid Hnone) "Hpm Htxn Hkey".
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
          iDestruct (txnprep_lookup with "Hpm Hst") as %Hprep.
          congruence.
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

  Lemma keys_inv_not_committed γ gid ts pm tpls :
    set_Forall (λ k, key_to_group k = gid) (dom tpls) ->
    pm !! ts = None ->
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) -∗
    txnprep_auth γ gid pm -∗
    txn_inv γ -∗
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_xcmted_no_repl_tsprep γ key tpl.1 tpl.2 ts) ∗
    txnprep_auth γ gid pm ∗
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
    destruct (validate_true _ Hsome Hvd) as (l & Htpl & Hlen).
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

  Lemma txn_inv_abort γ gid pm ts wrs :
    gid ∈ ptgroups (dom wrs) ->
    txnwrs_receipt γ ts wrs -∗
    txnprep_unprep γ gid ts -∗
    txnprep_auth γ gid pm -∗
    txn_inv γ ==∗
    txnprep_auth γ gid pm ∗
    txn_inv γ ∗
    txnres_abt γ ts.
  Proof.
    iIntros (Hgid) "#Hwrs #Hnp Hpm Htxn".
    iNamed "Htxn".
    destruct (resm !! ts) as [res |] eqn:Hres; last first.
    { (* Case: [ts] not aborted or committed yet. *)
      iMod (txnres_insert ts ResAborted with "Hresm") as "Hresm"; first done.
      iDestruct (txnres_witness with "Hresm") as "#Habt".
      { apply lookup_insert. }
      pose proof (cmtd_impl_prep_inv_abort ts Hcip) as Hcip'.
      pose proof (tmods_kmods_consistent_inv_abort ts Hres Htkcc) as Htkcc'.
      iFrame "∗ # %".
      rewrite big_sepM_insert; last done.
      by iFrame "∗ #".
    }
    destruct res as [wrsc |]; last first.
    { (* Case: [ts] aborted; get a witness without any update. *)
      iDestruct (txnres_witness with "Hresm") as "#Habt".
      { apply Hres. }
      by auto 10 with iFrame.
    }
    (* Case: [ts] committed; contradiction. *)
    iDestruct (big_sepM_lookup with "Hvr") as "#Hresc"; first apply Hres.
    (* Prove [wrsc = wrs]. *)
    iDestruct (txnwrs_lookup with "Hwrsm Hwrs") as %Hwrs.
    specialize (Hcip ts).
    rewrite Hres Hwrs in Hcip.
    inversion Hcip. subst wrsc.
    rewrite /= /all_prepared.
    iDestruct (big_sepS_elem_of with "Hresc") as "Hp"; first apply Hgid.
    iDestruct (txnprep_lookup with "Hpm Hp") as %Hp.
    iDestruct (txnprep_lookup with "Hpm Hnp") as %Hnp.
    congruence.
  Qed.

  (* TODO: make proof closer to [learn_commit]; i.e., take only the required
  tuples out rather than all tuples in the group invariants. *)
  Lemma group_inv_learn_prepare γ gid log cpool ts pwrs :
    CmdPrep ts pwrs ∈ cpool ->
    txn_inv γ -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log_with_cpool γ gid log cpool ==∗
    txn_inv γ ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log_with_cpool γ gid (log ++ [CmdPrep ts pwrs]) cpool.
  Proof.
    iIntros (Hc) "Htxn Hkeys Hgroup".
    do 2 iNamed "Hgroup".
    rewrite /group_inv_no_log_with_cpool.
    (* Frame away unused resources. *)
    iFrame "Hcpool".
    destruct (stm !! ts) eqn:Hdup.
    { (* Case: Txn [ts] has already prepared, aborted, or committed; no-op. *)
      iDestruct (txn_tokens_inv_learn_prepare_noop pwrs with "Htks") as "Htks'"; [done | done |].
      iFrame "∗ # %".
      by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup.
    }
    assert (Hpm : pm !! ts = None).
    { rewrite -not_elem_of_dom. rewrite -not_elem_of_dom in Hdup. set_solver. }
    (* Case: Txn [ts] has not prepared, aborted, or committed. *)
    destruct (try_acquire ts pwrs tpls) eqn:Hacq; last first.
    { (* Case: Validation fails; abort the transaction. *)
      rewrite /group_inv_no_log_no_cpool.
      rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup Hacq.
      iFrame "Hrepls Hkeys".
      (* Mark [ts] unprepared in the prepare map. *)
      iMod (txnprep_insert ts false with "Hpm") as "Hpm"; first done.
      iDestruct (txnprep_witness with "Hpm") as "#Hunp".
      { apply lookup_insert. }
      iDestruct (big_sepS_elem_of with "Hvc") as "Hprep".
      { apply Hc. }
      iDestruct "Hprep" as (wrs) "(Hwrs & %Hnz & %Hpwrs)".
      (* Obtain evidence that [ts] has aborted. *)
      iMod (txn_inv_abort with "Hwrs Hunp Hpm Htxn") as "(Hpm & Htxn & #Habt)".
      { destruct Hpwrs as (_ & Hne & Hpwrs). by eapply wrs_group_elem_of_ptgroups. }
      (* Create txn tokens for the new state. *)
      rewrite /try_acquire in Hacq. destruct (validate _ _ _) eqn:Hvd; first done.
      iDestruct (txn_tokens_inv_learn_prepare_aborted with "Habt Htks") as "Htks'"; [done | done |].
      (* Re-establish [valid_prepared]. *)
      iDestruct (big_sepM_insert_2 _ _ ts StAborted with "[] Hvp") as "Hvp'"; first done.
      iFrame "∗ # %".
      by auto with set_solver.
    }
    (* Case: Validation succeeds; lock the tuples and mark the transaction prepared. *)
    rewrite /group_inv_no_log_no_cpool.
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup Hacq.
    rewrite /try_acquire in Hacq.
    destruct (validate ts pwrs tpls) eqn:Hvd; last done.
    inversion_clear Hacq.
    set tpls' := acquire _ _ _.
    (* Extract keys invariant in this group. *)
    iDestruct (keys_inv_group gid with "Hkeys") as "[Hkeys Hkeyso]".
    (* Expose the replicated history and prepared timestamp from keys invariant. *)
    iDestruct (keys_inv_extract_repl_tsprep with "Hkeys") as (tplsK) "(Hkeys & Htpls & %Hdom)".
    (* Agree on tuples from the group and keys invariants. *)
    iDestruct (tuple_repl_big_agree with "Hrepls Htpls") as %->.
    { pose proof (apply_cmds_dom log _ _ Hrsm) as Hdom'.
      by rewrite Hdom tpls_group_keys_group_dom Hdom'.
    }
    (* Update the tuples (setting the prepared timestamp to [ts]). *)
    iMod (tuple_repl_big_update (tpls_group gid tpls') with "Hrepls Htpls") as "[Hrepls Htpls]".
    { apply tpls_group_dom. by rewrite acquire_dom. }
    (* Prove txn [ts] has not committed on [tpls]. *)
    iDestruct (keys_inv_not_committed with "Hkeys Hpm Htxn") as "(Hkeys & Hpm & Htxn)".
    { intros k Hk. by eapply key_to_group_tpls_group. }
    { apply Hpm. }
    (* Re-establish keys invariant w.r.t. updated tuples. *)
    iDestruct (keys_inv_learn_prepare with "Hkeys") as "Hkeys"; first done.
    (* Put ownership of tuples back to keys invariant. *)
    iDestruct (keys_inv_merge_repl_tsprep (keys_group gid keys_all) with "[Hkeys] Htpls") as "Hkeys".
    { rewrite tpls_group_keys_group_dom in Hdom.
      by rewrite tpls_group_keys_group_dom acquire_dom.
    }
    { iApply (big_sepM_mono with "Hkeys").
      iIntros (k t Hkt) "Hkey".
      iNamed "Hkey". iNamed "Hkey". iFrame "∗ #".
    }
    (* Merge the keys invariants of this group and other groups. *)
    iDestruct (keys_inv_ungroup with "Hkeys Hkeyso") as "Hkeys".
    (* Mark [ts] as prepared in the prepare map. *)
    iMod (txnprep_insert ts true with "Hpm") as "Hpm"; first done.
    (* Extract witness that [ts] has prepared. *)
    iDestruct (txnprep_witness with "Hpm") as "#Hprep".
    { apply lookup_insert. }
    (* Create txn tokens for the new state. *)
    iDestruct (txn_tokens_inv_learn_prepare_prepared with "Hprep Htks") as "Htks'"; [done | done |].
    (* Re-establish [valid_prepared]. *)
    iDestruct (big_sepM_insert_2 _ _ ts (StPrepared pwrs) with "[] Hvp") as "Hvp'".
    { by iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hc. }
    iFrame "∗ # %".
    by auto with set_solver.
  Qed.

  Lemma keys_inv_committed γ ts pwrs wrs tpls :
    dom tpls = dom pwrs ->
    pwrs ⊆ wrs ->
    map_Forall (λ _ t, t.2 = ts) tpls ->
    txnres_cmt γ ts wrs -∗
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) -∗
    txn_inv γ -∗
    ([∗ map] key ↦ tpl; v ∈ tpls; pwrs, key_inv_cmted_no_repl_tsprep γ key tpl.1 ts v) ∗
    txn_inv γ.
  Proof.
    iIntros (Hdom Hwrs Hts) "#Hcmt Htpls Htxn".
    iApply (big_sepM_sepM2_impl_res with "Htpls Htxn"); first done.
    iIntros "!>" (k [l t] v Htpl Hv) "Hkey Htxn".
    simpl.
    iNamed "Htxn".
    iDestruct (txnres_lookup with "Hresm Hcmt") as %Hresm.
    iNamed "Hkey".
    iDestruct (kmods_cmtd_lookup with "Hkmodcs Hkmodc") as %Hkmodc.
    assert (Hwrsv : wrs !! k = Some v); first by eapply lookup_weaken.
    assert (Hkmodcv : kmodc !! ts = Some v); first by eapply resm_cmted_kmod_present.
    specialize (Hts _ _ Htpl). simpl in Hts. subst t.
    by iFrame "∗ # %".
  Qed.

  Lemma txn_inv_has_prepared γ gid ts wrs :
    gid ∈ ptgroups (dom wrs) ->
    txnres_cmt γ ts wrs -∗
    txn_inv γ -∗
    txnprep_prep γ gid ts.
  Proof.
    iIntros (Hptg) "Hres Htxn".
    iNamed "Htxn".
    iDestruct (txnres_lookup with "Hresm Hres") as %Hr.
    iDestruct (big_sepM_lookup with "Hvr") as "Hr"; first by apply Hr.
    rewrite /= /all_prepared.
    iDestruct (big_sepS_elem_of with "Hr") as "Hp"; first apply Hptg.
    iFrame "#".
  Qed.

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
  Proof.
    iIntros (Hdom) "Htpls".
    iApply (big_sepM_impl_dom_eq with "Htpls"); first apply multiwrite_dom.
    iIntros "!>" (k t1 t2 Ht1 Ht2) "Htpl".
    destruct (wrs !! k) as [v |] eqn:Hwrs.
    { apply elem_of_dom_2 in Ht1. apply elem_of_dom_2 in Hwrs. set_solver. }
    rewrite /multiwrite lookup_merge Hwrs Ht1 /= in Ht2.
    by inversion_clear Ht2.
  Qed.

  Lemma group_inv_learn_commit γ gid log cpool ts :
    cpool_subsume_log cpool (log ++ [CmdCmt ts]) ->
    txn_inv γ -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log_with_cpool γ gid log cpool ==∗
    txn_inv γ ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log_with_cpool γ gid (log ++ [CmdCmt ts]) cpool.
  Proof.
    iIntros (Hsubsume) "Htxn Hkeys Hgroup".
    rewrite /cpool_subsume_log Forall_app Forall_singleton in Hsubsume.
    destruct Hsubsume as [Hsubsume Hc].
    do 2 iNamed "Hgroup".
    (* Obtain proof that [ts] has committed. *)
    iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hc.
    iDestruct "Hc" as (wrsc) "[Hcmt %Hgid]".
    rewrite /group_inv_no_log_with_cpool.
    destruct (stm !! ts) eqn:Hdup; last first.
    { (* Case: Empty state; contradiction---no prepare before commit. *) 
      iDestruct (txn_inv_has_prepared with "Hcmt Htxn") as "#Hst"; first apply Hgid.
      assert (Hpm : pm !! ts = None).
      { rewrite -not_elem_of_dom. rewrite -not_elem_of_dom in Hdup. set_solver. }
      iDestruct (txnprep_lookup with "Hpm Hst") as %Hlookup.
      congruence.
    }
    (* Case: Transaction prepared, aborted, or committed. *)
    destruct t as [pwrs | |] eqn:Ht; last first.
    { (* Case: [StAborted]; contradiction. *)
      iDestruct ("Htks" $! log stm tpls with "[] []") as "Htk"; [done | done |].
      iDestruct (big_sepM_lookup with "Htk") as "#Habt".
      { apply Hdup. }
      simpl.
      iNamed "Htxn".
      iDestruct (txnres_lookup with "Hresm Hcmt") as "%Hcmt".
      iDestruct (txnres_lookup with "Hresm Habt") as "%Habt".
      congruence.
    }
    { (* Case: [StCommitted]; no-op. *)
      rewrite /group_inv_no_log_no_cpool.
      rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup.
      (* Create txn tokens for the new state. *)
      iDestruct (txn_tokens_inv_learn_commit with "[Hcmt] Htks") as "Htks'".
      { by eauto. }
      by iFrame "∗ #".
    }
    (* Case: [StPrepared wrs] *)
    rewrite /group_inv_no_log_no_cpool.
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup.
    set tpls' := multiwrite _ _ _.
    (* Obtain proof of valid prepared input. *)
    iDestruct (big_sepM_lookup with "Hvp") as "Hc"; first apply Hdup. simpl.
    iDestruct "Hc" as (wrs) "(Hwrs & %Hts & %Hpwrs)".
    rewrite /valid_pwrs in Hpwrs.
    (* Prove the previously prepare [wrs] is equal to the commit [wrsc]. *)
    iAssert (⌜wrsc = wrs⌝)%I as %->.
    { iNamed "Htxn".
      iDestruct (txnres_lookup with "Hresm Hcmt") as %Hresm.
      iDestruct (txnwrs_lookup with "Hwrsm Hwrs") as %Hwrsm.
      specialize (Hcip ts).
      rewrite /cmtd_impl_prep Hresm Hwrsm in Hcip.
      by inversion Hcip.
    }
    (* Take the required keys invariants. *)
    iDestruct (big_sepS_subseteq_acc _ _ (dom pwrs) with "Hkeys") as "[Hkeys HkeysC]".
    { (* Prove [dom pwrs ⊆ keys_all] *)
      destruct Hpwrs as (Hvalid & _ & Hpwrs).
      transitivity (dom wrs); last done.
      rewrite Hpwrs.
      apply dom_filter_subseteq.
    }
    (* Take the required tuple ownerships from the group invariant. *)
    iDestruct (big_sepM_dom_subseteq_split _ _ (dom pwrs) with "Hrepls")
      as (tplsg [Hdom Hsubseteq]) "[Hrepls HreplsO]".
    { (* Prove [dom pwrs ⊆ dom (tpls_group gid tpls)]. *)
      destruct Hpwrs as (Hvalid & _ & Hpwrs).
      pose proof (apply_cmds_dom log _ _ Hrsm) as Hdom.
      rewrite Hpwrs wrs_group_keys_group_dom tpls_group_keys_group_dom Hdom.
      set_solver.
    }
    (* Expose the replicated history and prepared timestamp from keys invariant. *)
    iDestruct (keys_inv_extract_repl_tsprep with "Hkeys") as (tplsk) "(Hkeys & Htpls & %Hdom')".
    (* Agree on tuples from the group and keys invariants. *)
    iDestruct (tuple_repl_big_agree with "Hrepls Htpls") as %->; first by rewrite -Hdom in Hdom'.
    clear Hdom'.
    (* Update the tuples (resetting the prepared timestamp and extending the history). *)
    iMod (tuple_repl_big_update (multiwrite ts pwrs tplsg) with "Hrepls Htpls") as "[Hrepls Htpls]".
    { by rewrite multiwrite_dom. }
    (* Prove txn [ts] has committed on [tpls]. *)
    iAssert (⌜Forall (λ c, valid_pts_of_command c) log⌝)%I as %Hpts.
    { rewrite Forall_forall.
      iIntros (x Hx).
      rewrite Forall_forall in Hsubsume.
      specialize (Hsubsume _ Hx).
      iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hsubsume.
      destruct x; [done | | done | done]. simpl.
      by iDestruct "Hc" as (?) "(_ & %Hvts & _)".
    }
    iDestruct (keys_inv_committed with "Hcmt Hkeys Htxn") as "[Hkeys Htxn]".
    { apply Hdom. }
    { destruct Hpwrs as (_ & _ & Hpwrs). rewrite Hpwrs. apply map_filter_subseteq. }
    { (* Prove prepared timestamp of [tplsg] is [ts]. *)
      intros k tpl Hlookup.
      eapply (pts_consistency log); [apply Hpts | apply Hrsm | apply Hdup | |].
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
    iDestruct (keys_inv_merge_repl_tsprep (dom pwrs) with "Hkeys Htpls") as "Hkeys".
    { by rewrite multiwrite_dom. }
    iDestruct ("HkeysC" with "Hkeys") as "Hkeys".
    (* Merge ownership of tuples back to group invariant. *)
    iDestruct (tuple_repl_half_multiwrite_disjoint ts pwrs with "HreplsO") as "HreplsO".
    { set_solver. }
    rewrite multiwrite_difference_distr.
    iDestruct (big_sepM_difference_combine with "Hrepls HreplsO") as "Hrepls".
    { by apply multiwrite_mono. }
    rewrite multiwrite_tpls_group_commute.
    (* Create txn tokens for the new state. *)
    iDestruct (txn_tokens_inv_learn_commit with "[Hcmt] Htks") as "Htks'".
    { by eauto. }
    (* Re-establish [valid_prepared]. *)
    iDestruct (big_sepM_insert_2 _ _ ts (StCommitted) with "[] Hvp") as "Hvp'".
    { by iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hc. }
    iFrame "∗ # %".
    by auto with set_solver.
  Qed.

  (* Invariance proof for [learn_abort]. *)

  Lemma keys_inv_prepared γ ts tpls :
    map_Forall (λ _ t, t.2 = ts) tpls ->
    txnres_abt γ ts -∗
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) -∗
    txn_inv γ -∗
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_prepared_no_repl_tsprep γ key tpl.1 ts) ∗
    txn_inv γ.
  Proof.
    iIntros (Hts) "#Habt Htpls Htxn".
    iApply (big_sepM_impl_res with "Htpls Htxn").
    iIntros "!>" (k [l t] Htpl) "Hkey Htxn". simpl.
    iNamed "Htxn".
    iDestruct (txnres_lookup with "Hresm Habt") as %Hresm.
    iNamed "Hkey".
    iDestruct (kmods_cmtd_lookup with "Hkmodcs Hkmodc") as %Hkmodc.
    assert (Hnc : kmodc !! ts = None); first by eapply resm_abted_kmod_absent.
    specialize (Hts _ _ Htpl). simpl in Hts. subst t.
    by iFrame "∗ # %".
  Qed.

  Lemma key_inv_learn_abort {γ ts wrs tpls} k x y :
    tpls !! k = Some x ->
    release ts wrs tpls !! k = Some y ->
    is_Some (wrs !! k) ->
    key_inv_prepared_no_repl_tsprep γ k x.1 ts -∗
    key_inv_no_repl_tsprep γ k y.1 y.2.
  Proof.
    iIntros (Hx Hy Hv) "Hkeys".
    iNamed "Hkeys". iNamed "Hkey". iNamed "Hprop".
    iFrame "∗ # %".
    iPureIntro.
    destruct Hv as [v Hv].
    rewrite lookup_merge Hx Hv /= in Hy.
    destruct x as [h t].
    inversion_clear Hy.
    by apply (diff_by_cmtd_inv_learn_abort ts).
  Qed.

  Lemma keys_inv_learn_abort {γ ts wrs tpls} :
    dom tpls = dom wrs ->
    ([∗ map] key ↦ tpl ∈ tpls,
       key_inv_prepared_no_repl_tsprep γ key tpl.1 ts) -∗
    ([∗ map] key ↦ tpl ∈ release ts wrs tpls,
       key_inv_no_repl_tsprep γ key tpl.1 tpl.2).
  Proof.
    iIntros (Hdom) "Hkeys".
    iApply (big_sepM_impl_dom_eq with "Hkeys").
    { apply release_dom. }
    iIntros "!>" (k x y Hx Hy) "Hkey".
    assert (is_Some (wrs !! k)) as Hwrs.
    { apply elem_of_dom_2 in Hx.
      rewrite set_eq in Hdom.
      by rewrite Hdom elem_of_dom in Hx.
    }
    by iApply (key_inv_learn_abort with "Hkey").
  Qed.

  Lemma tuple_repl_half_release_disjoint {γ} ts wrs tpls :
    dom tpls ## dom wrs ->
    ([∗ map] k↦tpl ∈ tpls, tuple_repl_half γ k tpl) -∗
    ([∗ map] k↦tpl ∈ release ts wrs tpls, tuple_repl_half γ k tpl).
  Proof.
    iIntros (Hdom) "Htpls".
    iApply (big_sepM_impl_dom_eq with "Htpls"); first apply release_dom.
    iIntros "!>" (k t1 t2 Ht1 Ht2) "Htpl".
    destruct (wrs !! k) as [v |] eqn:Hwrs.
    { apply elem_of_dom_2 in Ht1. apply elem_of_dom_2 in Hwrs. set_solver. }
    rewrite /release lookup_merge Hwrs Ht1 /= in Ht2.
    by inversion_clear Ht2.
  Qed.

  Lemma group_inv_learn_abort γ gid log cpool ts :
    cpool_subsume_log cpool (log ++ [CmdAbt ts]) ->
    txn_inv γ -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log_with_cpool γ gid log cpool ==∗
    txn_inv γ ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log_with_cpool γ gid (log ++ [CmdAbt ts]) cpool.
  Proof.
    iIntros (Hsubsume) "Htxn Hkeys Hgroup".
    rewrite /cpool_subsume_log Forall_app Forall_singleton in Hsubsume.
    destruct Hsubsume as [Hsubsume Hc].
    do 2 iNamed "Hgroup".
    (* Obtain proof that [ts] has aborted. *)
    iDestruct (big_sepS_elem_of _ _ _ Hc with "Hvc") as "[Habt _]".
    rewrite /group_inv_no_log_with_cpool.
    destruct (stm !! ts) as [st |] eqn:Hdup; last first.
    { (* Case: Directly abort without prepare. *)
      rewrite /group_inv_no_log_no_cpool.
      rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup.
      (* Create txn tokens for the new state. *)
      iDestruct (txn_tokens_inv_learn_abort with "Habt Htks") as "Htks'".
      (* Re-establish [valid_prepared]. *)
      iDestruct (big_sepM_insert_2 _ _ ts StAborted with "[] Hvp") as "Hvp'".
      { done. }
      iFrame "∗ # %".
      by auto with set_solver.
    }
    (* Case: Txn [ts] has prepared, aborted, or committed. *)
    rewrite /group_inv_no_log_no_cpool.
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup.
    destruct st as [pwrs | |] eqn:Ht; first 1 last.
    { (* Case: Committed; contradiction by obtaining a commit token. *)
      iDestruct ("Htks" $! log stm tpls with "[] []") as "Htk"; [done | done |].
      iDestruct (big_sepM_lookup with "Htk") as "Hcmt"; first apply Hdup. simpl.
      iDestruct "Hcmt" as (wrs) "Hcmt".
      iNamed "Htxn".
      iDestruct (txnres_lookup with "Hresm Habt") as %Habt.
      iDestruct (txnres_lookup with "Hresm Hcmt") as %Hcmt.
      congruence.
    }
    { (* Case: Aborted; no-op. *)
      (* Create txn tokens for the new state. *)
      iDestruct (txn_tokens_inv_learn_abort with "Habt Htks") as "Htks'".
      by iFrame "∗ # %".
    }
    (* Case: Prepared; release the locks on tuples. *)
    set tpls' := release _ _ _.
    (* Obtain proof of valid prepared input. *)
    iDestruct (big_sepM_lookup with "Hvp") as "Hc"; first apply Hdup. simpl.
    iDestruct "Hc" as (wrs) "(Hwrs & %Hts & %Hpwrs)".
    rewrite /valid_pwrs in Hpwrs.
    (* Take the required keys invariants. *)
    iDestruct (big_sepS_subseteq_acc _ _ (dom pwrs) with "Hkeys") as "[Hkeys HkeysC]".
    { (* Prove [dom pwrs ⊆ keys_all] *)
      destruct Hpwrs as (Hvalid & _ & Hpwrs).
      transitivity (dom wrs); last done.
      rewrite Hpwrs.
      apply dom_filter_subseteq.
    }
    (* Take the required tuple ownerships from the group invariant. *)
    iDestruct (big_sepM_dom_subseteq_split _ _ (dom pwrs) with "Hrepls")
      as (tplsg [Hdom Hsubseteq]) "[Hrepls HreplsO]".
    { (* Prove [dom pwrs ⊆ dom (tpls_group gid tpls)]. *)
      destruct Hpwrs as (Hvalid & _ & Hpwrs).
      pose proof (apply_cmds_dom log _ _ Hrsm) as Hdom.
      rewrite Hpwrs wrs_group_keys_group_dom tpls_group_keys_group_dom Hdom.
      set_solver.
    }
    (* Expose the replicated history and prepared timestamp from keys invariant. *)
    iDestruct (keys_inv_extract_repl_tsprep with "Hkeys") as (tplsk) "(Hkeys & Htpls & %Hdom')".
    (* Agree on tuples from the group and keys invariants. *)
    iDestruct (tuple_repl_big_agree with "Hrepls Htpls") as %->; first by rewrite -Hdom in Hdom'.
    clear Hdom'.
    (* Update the tuples (resetting the prepared timestamp). *)
    iMod (tuple_repl_big_update (release ts pwrs tplsg) with "Hrepls Htpls") as "[Hrepls Htpls]".
    { by rewrite release_dom. }
    (* Prove txn [ts] has prepared but not committed on [tpls]. *)
    iAssert (⌜Forall (λ c, valid_pts_of_command c) log⌝)%I as %Hpts.
    { rewrite Forall_forall.
      iIntros (x Hx).
      rewrite Forall_forall in Hsubsume.
      specialize (Hsubsume _ Hx).
      iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hsubsume.
      destruct x; [done | | done | done]. simpl.
      by iDestruct "Hc" as (?) "(_ & %Hvts & _)".
    }
    iDestruct (keys_inv_prepared with "Habt Hkeys Htxn") as "[Hkeys Htxn]".
    { (* Prove prepared timestamp of [tplsg] is [ts]. *)
      intros k tpl Hlookup.
      eapply (pts_consistency log); [apply Hpts | apply Hrsm | apply Hdup | |].
      { eapply lookup_weaken; first apply Hlookup.
        transitivity (tpls_group gid tpls); first done.
        rewrite /tpls_group.
        apply map_filter_subseteq.
      }
      { rewrite -Hdom. by eapply elem_of_dom_2. }
    }
    (* Re-establish keys invariant w.r.t. updated tuples. *)
    iDestruct (keys_inv_learn_abort with "Hkeys") as "Hkeys"; first apply Hdom.
    (* Put ownership of tuples back to keys invariant. *)
    iDestruct (keys_inv_merge_repl_tsprep (dom pwrs) with "Hkeys Htpls") as "Hkeys".
    { by rewrite release_dom. }
    iDestruct ("HkeysC" with "Hkeys") as "Hkeys".
    (* Merge ownership of tuples back to group invariant. *)
    iDestruct (tuple_repl_half_release_disjoint ts pwrs with "HreplsO") as "HreplsO".
    { set_solver. }
    rewrite release_difference_distr.
    iDestruct (big_sepM_difference_combine with "Hrepls HreplsO") as "Hrepls".
    { by apply release_mono. }
    rewrite release_tpls_group_commute.
    (* Create txn tokens for the new state. *)
    iDestruct (txn_tokens_inv_learn_abort with "Habt Htks") as "Htks'".
    (* Re-establish [valid_prepared]. *)
    iDestruct (big_sepM_insert_2 _ _ ts StAborted with "[] Hvp") as "Hvp'".
    { by iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hc. }
    iFrame "∗ # %".
    by auto with set_solver.
  Qed.

  (* Invariance proof for [learn_read]. *)

  Lemma key_inv_learn_read {γ} ts k h t :
    let tpl := read ts h t in
    key_inv_no_repl_tsprep γ k h t -∗
    key_inv_no_repl_tsprep γ k tpl.1 tpl.2.
  Proof.
    iIntros (tpl) "Hkey".
    subst tpl. rewrite /read.
    case_decide as Ht; last done.
    iNamed "Hkey". iNamed "Hprop". simpl.
    destruct Ht as [-> | Hlt].
    { (* Case: Tuple not acquired by any txn. *)
      apply (diff_by_cmtd_inv_learn_read_free ts) in Hdiffc; last done.
      iFrame "∗ # %".
    }
    (* Case: Tuple prepared at [t] where [ts < t]. *)
    pose proof (diff_by_cmtd_inv_learn_read_acquired _ _ Hlt Hdiffc) as Hdiffc'.
    iFrame "∗ # %".
  Qed.

  Lemma group_inv_learn_read γ gid log cpool ts key :
    CmdRead ts key ∈ cpool ->
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log_with_cpool γ gid log cpool ==∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log_with_cpool γ gid (log ++ [CmdRead ts key]) cpool.
  Proof.
    iIntros (Hc) "Hkeys Hgroup".
    do 2 iNamed "Hgroup".
    rewrite /group_inv_no_log_with_cpool /group_inv_no_log_no_cpool.
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /=.
    (* Obtain validity of the read input. *)
    iDestruct (big_sepS_elem_of with "Hvc") as "Hread"; first apply Hc.
    iDestruct "Hread" as %(_ & Hkey & Hgid).
    destruct (tpls !! key) as [[h t] |] eqn:Hht; last first.
    { (* Case: Out-of-range key; contradiction. *)
      pose proof (apply_cmds_dom log _ _ Hrsm) as Hdom.
      rewrite /valid_key in Hkey.
      by rewrite -not_elem_of_dom Hdom in Hht.
    }
    (* Case: Valid read. *)
    set tpl' := read _ _ _.
    (* Create txn tokens for the new state. *)
    iDestruct (txn_tokens_inv_learn_read ts key with "Htks") as "Htks'".
    (* Take the required key invariant. *)
    iDestruct (big_sepS_elem_of_acc with "Hkeys") as "[Hkey HkeysC]"; first apply Hkey.
    (* Take the half-ownership of the tuple out from the key invariant. *)
    iDestruct (key_inv_extract_repl_tsprep with "Hkey") as (tpl) "[Hkey Htpl]".
    (* And the other half from the group invariant. *)
    iDestruct (big_sepM_delete with "Hrepls") as "[Hrepl Hrepls]".
    { by apply map_lookup_filter_Some_2. }
    (* Agree on their value. *)
    iDestruct (tuple_repl_agree with "Hrepl Htpl") as %->. simpl.
    (* Update the tuple. *)
    iMod (tuple_repl_update tpl' with "Hrepl Htpl") as "[Hrepl Htpl]".
    (* Re-establish key invariant w.r.t. the updated tuple. *)
    iDestruct (key_inv_learn_read ts with "Hkey") as "Hkey".
    (* Put back tuple ownership back to key invariant. *)
    iDestruct (key_inv_merge_repl_tsprep with "Hkey Htpl") as "Hkey".
    (* Put the key invariant back. *)
    iDestruct ("HkeysC" with "Hkey") as "Hkeys".
    (* Put back tuple ownership back to group invariant. *)
    iDestruct (big_sepM_insert_2 with "Hrepl Hrepls") as "Hrepls".
    rewrite insert_delete_insert insert_tpls_group_commute; last done.
    by iFrame "∗ # %".
  Qed.

  Lemma group_inv_learn γ gid cpool cmds :
    ∀ log,
    cpool_subsume_log cpool (log ++ cmds) ->
    txn_inv γ -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log_with_cpool γ gid log cpool ==∗
    txn_inv γ ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log_with_cpool γ gid (log ++ cmds) cpool.
  Proof.
    iInduction cmds as [| c l] "IH".
    { iIntros (log Hsubsume) "Htxn Hkeys Hgroup". rewrite app_nil_r. by iFrame. }
    (* rewrite Forall_cons in Hcpool. *)
    (* destruct Hcpool as [Hc Hcpool]. *)
    iIntros (log Hsubsume) "Htxn Hkeys Hgroup".
    rewrite cons_middle app_assoc in Hsubsume.
    rewrite cons_middle app_assoc.
    destruct c.
    { (* Case: [CmdRead tid key] *)
      iMod (group_inv_learn_read with "Hkeys Hgroup") as "[Hkeys Hgroup]".
      { rewrite /cpool_subsume_log 2!Forall_app Forall_singleton in Hsubsume.
        by destruct Hsubsume as [[_ Hc] _].
      }
      by iApply ("IH" with "[] Htxn Hkeys Hgroup").
    }
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
    { (* Case: [CmdAbt tid] *)
      iMod (group_inv_learn_abort with "Htxn Hkeys Hgroup") as "(Htxn & Hkeys & Hgroup)".
      { rewrite /cpool_subsume_log Forall_app in Hsubsume.
        by destruct Hsubsume as [Hsubsume _].
      }
      by iApply ("IH" with "[] Htxn Hkeys Hgroup").
    }
  Qed.

End group_inv.
(* TODO: move to distx_group_inv.v once stable. *)

(* TODO: move to inv_commit.v once stable. *)
Section inv_commit.
  Context `{!distx_ghostG Σ}.

  (**
   * The commit action modifies the following logical states in [txn_inv]:
   * 1. Result map [resm].
   * 2. Will-commit transaction map [txns_cmt].
   * 3. Key modification map by committed txns [kmodcs].
   * 4. Key modification map by linearized txns [kmodls].
   * Invariants to re-establish:
   * 1. Committed implies prepared [Hcip].
   * 2. Consistency between result map and committed kmod map [Htkcc].
   * 3. Consistency between result map and linearized kmod map [Htkcl].
   * 4. Conflict free [Hcf].
   *
   * And the following logical states in [key_inv]:
   * 1. Committed history [cmtd].
   * 2. Key modification by committed txns [kmodc].
   * 3. Key modification by linearized txns [kmodl].
   * Invariants to re-establish:
   * 1. Committed history is a prefix of linearized history [Hprefix].
   * 2. Difference between linearized and committed histories [Hdiffl].
   * 3. Difference between committed and replicated histories [Hdiffc].
   * 4. Not written at timestamp 0 [Hzrsv].
   *
   * It seems like we're missing an invariant that proves the committing
   * transaction must have linearized. We might want to add something like
   * prepared-implies-linearized-or-finalized.
   *)

  Lemma txn_inv_commit γ ts wrs :
    txnwrs_receipt γ ts wrs -∗
    all_prepared γ ts (dom wrs) -∗
    txn_inv γ -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ==∗
    txn_inv γ ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    txnres_cmt γ ts wrs.
  Proof.
  Admitted.

End inv_commit.
(* TODO: move to inv_commit.v once stable. *)

(* TODO: move to group_inv_submit.v once stable. *)
Section inv_submit.
  Context `{!distx_ghostG Σ}.

  Lemma group_inv_submit γ gid cpool c :
    safe_submit γ gid c -∗
    group_inv_no_cpool γ gid cpool -∗
    group_inv_no_cpool γ gid ({[c]} ∪ cpool).
  Proof.
    iIntros "Hsafe Hgroup".
    do 2 iNamed "Hgroup".
    iDestruct (big_sepS_insert_2 with "Hsafe Hvc") as "Hvc'".
    iFrame "∗ # %".
  Qed.

End inv_submit.
(* TODO: move to group_inv_submit.v once stable. *)
