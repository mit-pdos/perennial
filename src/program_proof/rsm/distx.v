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
  dom tpls = keys ->
  dom (tpls_group gid tpls) = keys_group gid keys.
Proof.
Admitted.

(* Participant groups. *)
Definition ptgroups (keys : gset dbkey) :=
  set_fold (λ k s, {[key_to_group k]} ∪ s) (∅ : gset groupid) keys.

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

Lemma acquire_tuple_unmodified {tid wrs tpls key} :
  wrs !! key = None ->
  (acquire tid wrs tpls) !! key = tpls !! key.
Admitted.

Lemma acquire_tuple_modified {tid wrs tpls key tpl} :
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

Definition multiwrite_key (tid : nat) (wr : option dbval) (tpl : option dbtpl) :=
  match wr, tpl with
  | None, Some (vs, tsprep) => Some (vs, tsprep)
  | Some v, Some (vs, _) => Some (last_extend tid vs ++ [v], O)
  | _, _ => None
  end.

Definition multiwrite (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  merge (multiwrite_key tid) wrs tpls.

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
  | None, Some (vs, tsprep) => Some (vs, tsprep)
  | Some _, Some (vs, _) => Some (vs, O)
  | _, _ => None
  end.

Definition release (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  merge (release_key tid) wrs tpls.

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

(* TODO: should initial tuple state be ∅? *)
Definition apply_cmds (cmds : list command) :=
  foldl apply_cmd init_rpst cmds.

Definition apply_cmds_stm (cmds : list command) :=
  match apply_cmds cmds with
  | State stm _ => Some stm
  | _ => None
  end.

Lemma apply_cmds_dom cmds :
  match apply_cmds cmds with
  | State _ tpls => dom tpls = keys_all
  | _ => False
  end.
Admitted.

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

Definition tmods_kmods_consistent (m1 : gmap nat dbmap) (m2 : gmap dbkey dbkmod) :=
  ∀ t k, lookup_twice m1 t k = lookup_twice m2 k t.

Definition res_to_tmod (res : txnres) :=
  match res with
  | ResCommitted wrs => Some wrs
  | ResAborted => None
  end.

Definition resm_to_tmods (resm : gmap nat txnres) :=
  omap res_to_tmod resm.

(* TODO: move to distx_inv_proof.v once stable. *)
Lemma diff_by_cmtd_inv_learn_prepare repl cmtd tmods ts' :
  tmods !! O = None ->
  (length repl ≤ ts')%nat ->
  tmods !! ts' = None ->
  diff_by_cmtd repl cmtd tmods O ->
  diff_by_cmtd repl cmtd tmods ts'.
Proof.
  intros Hz Hlen Hts' Hdiff.
  rewrite /diff_by_cmtd Hz in Hdiff.
  destruct Hdiff as [[tsrd Hextend] _].
  rewrite /diff_by_cmtd Hts'.
  by split; first eauto.
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

  (* Custom transaction status RA. *)
  Definition txnst_auth γ (gid : groupid) (stm : gmap nat txnst) : iProp Σ.
  Admitted.

  Definition txnst_lb γ (gid : groupid) (ts : nat) (st : txnst) : iProp Σ.
  Admitted.

  #[global]
  Instance txnst_lb_persistent γ gid ts st :
    Persistent (txnst_lb γ gid ts st).
  Admitted.

  Lemma txnst_prepare γ gid stm ts wrs :
    stm !! ts = None ->
    txnst_auth γ gid stm ==∗
    txnst_auth γ gid (<[ts := StPrepared wrs]> stm).
  Admitted.

  Lemma txnst_commit γ gid stm ts wrs :
    stm !! ts = Some (StPrepared wrs) ->
    txnst_auth γ gid stm ==∗
    txnst_auth γ gid (<[ts := StCommitted]> stm).
  Admitted.

  Lemma txnst_abort γ gid stm ts wrs :
    stm !! ts = Some (StPrepared wrs) ->
    txnst_auth γ gid stm ==∗
    txnst_auth γ gid (<[ts := StAborted]> stm).
  Admitted.

  Lemma txnst_direct_abort γ gid stm ts :
    stm !! ts = None ->
    txnst_auth γ gid stm ==∗
    txnst_auth γ gid (<[ts := StAborted]> stm).
  Admitted.

  Lemma txnst_witness γ gid stm ts st :
    stm !! ts = Some st ->
    txnst_auth γ gid stm -∗
    txnst_lb γ gid ts st.
  Admitted.

  Definition kmods_lnrz γ (kmods : gmap dbkey dbkmod) : iProp Σ.
  Admitted.

  Definition kmod_lnrz γ (k : dbkey) (kmod : dbkmod) : iProp Σ.
  Admitted.

  Definition kmods_cmtd γ (kmods : gmap dbkey dbkmod) : iProp Σ.
  Admitted.

  Definition kmod_cmtd γ (k : dbkey) (kmod : dbkmod) : iProp Σ.
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

Lemma big_sepM_impl_dom_eq {PROP : bi} `{Countable K} {A B}
    (Φ : K → A → PROP) (Ψ : K → B → PROP) (m1 : gmap K A) (m2 : gmap K B) :
  dom m2 = dom m1 →
  ([∗ map] k↦x ∈ m1, Φ k x) -∗
  □ (∀ (k : K) (x : A) (y : B),
      ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ →
      Φ k x -∗ Ψ k y) -∗
  ([∗ map] k↦y ∈ m2, Ψ k y).
Proof.
  iIntros (Hdom) "Hm1".
  assert (Hsubseteq : dom m2 ⊆ dom m1) by set_solver.
  iDestruct (big_sepM_impl_dom_subseteq with "Hm1") as "Hm2"; first done.
  iIntros "Himpl".
  iDestruct ("Hm2" with "Himpl") as "[H2 H1]".
  replace (filter _ _) with (∅ : gmap K A); first done.
  apply map_eq. intros k.
  rewrite lookup_empty. symmetry.
  rewrite map_lookup_filter_None. right.
  intros x Hm1 Hm2.
  apply elem_of_dom_2 in Hm1.
  apply not_elem_of_dom_2 in Hm2.
  set_solver.
Qed.

Lemma big_sepM_impl_res {PROP : bi} `{Countable K} {A}
  (Φ : K → A → PROP) (Ψ : K → A → PROP) (R : PROP) (m : gmap K A) :
  ([∗ map] k↦x ∈ m, Φ k x) -∗
  R -∗
  □ (∀ (k : K) (x : A),
       ⌜m !! k = Some x⌝ →
       Φ k x -∗ R -∗ Ψ k x ∗ R) -∗
  ([∗ map] k↦y ∈ m, Ψ k y) ∗ R.
Proof.
  iIntros "Hm HR #Himpl".
  iInduction m as [| k x m] "IH" using map_ind.
  { iFrame. by iApply big_sepM_empty. }
  iDestruct (big_sepM_insert with "Hm") as "[HΦ Hm]"; first done.
  rewrite big_sepM_insert; last done.
  iDestruct ("Himpl" with "[] HΦ HR") as "[HΨ HR]"; first by rewrite lookup_insert.
  iDestruct ("IH" with "[] Hm HR") as "[Hm HR]"; last by iFrame.
  iIntros "!>" (q y Hmqy) "HΦ HR".
  iApply ("Himpl" with "[] HΦ HR").
  iPureIntro.
  rewrite lookup_insert_ne; [done | set_solver].
Qed.

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
      (resm : gmap nat txnres)
      (kmodsl kmodsc : gmap dbkey dbkmod),
      (* global timestamp *)
      "Hts"    ∷ ts_auth γ ts ∗
      (* prophecy variable *)
      "Hproph" ∷ txn_proph γ future ∗
      (* transaction result map *)
      "Hresm" ∷ txnres_auth γ resm ∗
      (* key modifications *)
      "Hkmodl" ∷ kmods_lnrz γ kmodsl ∗
      "Hkmodc" ∷ kmods_cmtd γ kmodsc ∗
      (* safe commit/abort invariant *)
      "#Hvr"  ∷ ([∗ map] tid ↦ res ∈ resm, valid_res γ tid res) ∗
      (* TODO: for coordinator recovery, add a monotonically growing set of
      active txns; each active txn either appears in [txns_cmt]/[txns_abt] or in
      the result map [resm]. *)
      "%Hcf"   ∷ ⌜conflict_free future txns_cmt⌝ ∗
      "%Hcp"   ∷ ⌜conflict_past future past txns_abt⌝ ∗
      "%Htkcl" ∷ ⌜tmods_kmods_consistent txns_cmt kmodsl⌝ ∗
      "%Htkcc" ∷ ⌜tmods_kmods_consistent (resm_to_tmods resm) kmodsc⌝.

  Definition key_inv γ (key : dbkey) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd repl : dbhist)
      (tslb tsprep : nat)
      (kmodl kmodc : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_half γ key lnrz ∗
      "Hrepl"     ∷ hist_repl_half γ key repl ∗
      "Htsprep"   ∷ ts_repl_half γ key tsprep ∗
      "Htmlnrz"   ∷ kmod_lnrz γ key kmodl ∗
      "Htmcmtd"   ∷ kmod_cmtd γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "%Hlast"    ∷ ⌜last lnrz = Some dbv⌝ ∗
      "%Hprefix"  ∷ ⌜prefix cmtd lnrz⌝ ∗
      "%Hext"     ∷ ⌜(length lnrz ≤ S tslb)%nat⌝ ∗
      "%Hdiffl"   ∷ ⌜diff_by_lnrz cmtd lnrz kmodl⌝ ∗
      "%Hdiffc"   ∷ ⌜diff_by_cmtd repl cmtd kmodc tsprep⌝.

  Definition key_inv_no_repl_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd : dbhist)
      (tslb : nat)
      (kmodl kmodc : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_half γ key lnrz ∗
      "Htmlnrz"   ∷ kmod_lnrz γ key kmodl ∗
      "Htmcmtd"   ∷ kmod_cmtd γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "%Hlast"    ∷ ⌜last lnrz = Some dbv⌝ ∗
      "%Hprefix"  ∷ ⌜prefix cmtd lnrz⌝ ∗
      "%Hext"     ∷ ⌜(length lnrz ≤ S tslb)%nat⌝ ∗
      "%Hdiffl"   ∷ ⌜diff_by_lnrz cmtd lnrz kmodl⌝ ∗
      "%Hdiffc"   ∷ ⌜diff_by_cmtd repl cmtd kmodc tsprep⌝.

  Definition key_inv_with_kmodc_no_repl_tsprep
    γ (key : dbkey) (kmodc : dbkmod) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd : dbhist)
      (tslb : nat)
      (kmodl : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_half γ key lnrz ∗
      "Htmlnrz"   ∷ kmod_lnrz γ key kmodl ∗
      "Htmcmtd"   ∷ kmod_cmtd γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "%Hlast"    ∷ ⌜last lnrz = Some dbv⌝ ∗
      "%Hprefix"  ∷ ⌜prefix cmtd lnrz⌝ ∗
      "%Hext"     ∷ ⌜(length lnrz ≤ S tslb)%nat⌝ ∗
      "%Hdiffl"   ∷ ⌜diff_by_lnrz cmtd lnrz kmodl⌝ ∗
      "%Hdiffc"   ∷ ⌜diff_by_cmtd repl cmtd kmodc tsprep⌝.

  Lemma key_inv_no_repl_tsprep_unseal_kmodc γ key repl tsprep :
    key_inv_no_repl_tsprep γ key repl tsprep -∗
    ∃ kmodc, key_inv_with_kmodc_no_repl_tsprep γ key kmodc repl tsprep.
  Proof. iIntros "Hkey".  iNamed "Hkey". iFrame "% # ∗". Qed.

  Definition key_inv_ncmted_no_repl_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) (ts : nat) : iProp Σ :=
    ∃ kmodc,
      "Hkey" ∷ key_inv_with_kmodc_no_repl_tsprep γ key kmodc repl tsprep ∧
      "Hnc"  ∷ ⌜kmodc !! ts = None⌝.

  Definition valid_cmd γ (c : command) : iProp Σ :=
    match c with
    | CmdCmt ts => (∃ wrs, txnres_cmt γ ts wrs)
    | CmdAbt ts => txnres_abt γ ts
    | _ => True
    end.

  #[global]
  Instance valid_cmd_persistent γ c :
    Persistent (valid_cmd γ c).
  Proof. destruct c; apply _. Qed.

  Definition group_inv γ (gid : groupid) : iProp Σ :=
    ∃ (log : dblog) (cpool : gset command)
      (stm : gmap nat txnst) (tpls : gmap dbkey dbtpl),
      "Hlog"    ∷ clog_half γ gid log ∗
      "Hcpool"  ∷ cpool_half γ gid cpool ∗
      "Hstm"    ∷ txnst_auth γ gid stm ∗
      "Hrepls"  ∷ ([∗ map] key ↦ tpl ∈ tpls_group gid tpls, tuple_repl_half γ key tpl) ∗
      "#Hvc"    ∷ ([∗ set] c ∈ cpool, valid_cmd γ c) ∗
      "%Hrsm"   ∷ ⌜apply_cmds log = State stm tpls⌝.

  Definition group_inv_no_log γ (gid : groupid) (log : dblog) : iProp Σ :=
    ∃ (cpool : gset command) (stm : gmap nat txnst) (tpls : gmap dbkey dbtpl),
      "Hcpool"  ∷ cpool_half γ gid cpool ∗
      "Hstm"    ∷ txnst_auth γ gid stm ∗
      "Hrepls"  ∷ ([∗ map] key ↦ tpl ∈ tpls_group gid tpls, tuple_repl_half γ key tpl) ∗
      "#Hvc"    ∷ ([∗ set] c ∈ cpool, valid_cmd γ c) ∗
      "%Hrsm"   ∷ ⌜apply_cmds log = State stm tpls⌝.

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

  Lemma group_inv_extract_log {γ} gid :
    group_inv γ gid -∗
    ∃ log, clog_half γ gid log ∗ group_inv_no_log γ gid log.
  Proof.
  Admitted.

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

  Lemma keys_inv_extract_repl_tsprep {γ} keys :
    ([∗ set] key ∈ keys, key_inv γ key) -∗
    ∃ tpls, ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) ∗
            ([∗ map] key ↦ tpl ∈ tpls, tuple_repl_half γ key tpl) ∧
            ⌜dom tpls = keys⌝.
  Proof.
  Admitted.

  Lemma key_inv_not_committed γ gid ts stm key kmodc tpl :
    stm !! ts = None ->
    txnst_auth γ gid stm -∗
    txn_inv γ -∗
    key_inv_with_kmodc_no_repl_tsprep γ key kmodc tpl.1 tpl.2 -∗
    ⌜kmodc !! ts = None⌝.
  Proof.
    iIntros (Hnone) "Hstm Htxn Hkey".
    iNamed "Htxn".
    destruct (resm !! ts) as [res |] eqn:Hlookup.
    { (* Case: Committed or aborted. *)
      iDestruct (big_sepM_lookup with "Hvr") as "Hres"; first apply Hlookup.
      destruct res.
      { (* Case: Committed. *)
        simpl.
        destruct (wrs !! key) as [v |] eqn:Hv.
        { (* Case: [key] in the write set of [ts]; contradiction. *)
          admit.
        }
        (* Case: [key] not in the write set of [ts]. *)
        admit.
      }
      { (* Case: Aborted. *)
        (* Prove [kmodc !! ts = None] using [Htkcc] and [Hlookup]. *)
        admit.
      }
    }
    (* Case: Not committed or aborted. *)
    iPureIntro.
    (* TODO: prove this with [Htkcc] and [Hres]. *)
  Admitted.

  Lemma keys_inv_not_committed γ gid ts stm tpls :
    stm !! ts = None ->
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) -∗
    txnst_auth γ gid stm -∗
    txn_inv γ -∗
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_ncmted_no_repl_tsprep γ key tpl.1 tpl.2 ts) ∗
    txnst_auth γ gid stm ∗
    txn_inv γ.
  Proof.
    iIntros (Hnone) "Hkeys Hst Htxn".
    iApply (big_sepM_impl_res with "Hkeys [Hst Htxn]").
    { iFrame. } (* why can't $ do the work? *)
    iIntros "!>" (k t Hkt) "Hkey [Hst Htxn]".
    rewrite /key_inv_ncmted_no_repl_tsprep.
    iDestruct (key_inv_no_repl_tsprep_unseal_kmodc with "Hkey") as (kmodc) "Hkey".
    iDestruct (key_inv_not_committed with "Hst Htxn Hkey") as %Hprep.
    { apply Hnone. }
    iFrame "∗ %".
  Qed.

  Lemma key_inv_learn_prepare {γ gid ts wrs tpls} k x y :
    validate ts wrs tpls = true ->
    tpls_group gid tpls !! k = Some x ->
    tpls_group gid (acquire ts wrs tpls) !! k = Some y ->
    key_inv_no_repl_tsprep γ k x.1 x.2 -∗
    key_inv_no_repl_tsprep γ k y.1 y.2.
  Proof.
    iIntros (Hvd Hx Hy) "Hkeys".
    iNamed "Hkeys".
    iFrame "% # ∗".
    iPureIntro.
    apply map_lookup_filter_Some_1_1 in Hx, Hy.
    destruct (wrs !! k) as [t | ] eqn:Hwrsk; last first.
    { (* Case: tuple not modified. *)
      rewrite acquire_tuple_unmodified in Hy; last done.
      rewrite Hy in Hx.
      by inversion Hx.
    }
    (* Case: tuple modified. *)
    assert (Hsome : is_Some (wrs !! k)) by done.
    destruct (validate_true Hsome Hvd) as (l & Htpl & Hlen).
    rewrite Hx in Htpl. inversion Htpl. subst x. clear Htpl.
    rewrite (acquire_tuple_modified Hsome Hx) /= in Hy.
    inversion Hy. subst y. clear Hy.
    simpl. simpl in Hdiffc.
    apply diff_by_cmtd_inv_learn_prepare; [| done |  | done].
  Admitted.

  Lemma keys_inv_learn_preapre {γ gid ts wrs tpls} :
    validate ts wrs tpls = true ->
    ([∗ map] key ↦ tpl ∈ tpls_group gid tpls,
       key_inv_no_repl_tsprep γ key tpl.1 tpl.2) -∗
    ([∗ map] key ↦ tpl ∈ tpls_group gid (acquire ts wrs tpls),
       key_inv_no_repl_tsprep γ key tpl.1 tpl.2).
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
  
  Lemma group_inv_learn_prepare γ gid log ts wrs :
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log γ gid log ==∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log γ gid (log ++ [CmdPrep ts wrs]).
  Proof.
    iIntros "Hkeys Hgroup".
    iNamed "Hgroup".
    rewrite /apply_cmds in Hrsm.
    rewrite /group_inv_no_log.
    (* Frame away unused resources. *)
    iFrame "Hcpool Hvc".
    destruct (stm !! ts) eqn:Hdup.
    { (* Case: Txn [ts] has already prepared, aborted, or committed; no-op. *)
      iFrame "Hrepls Hkeys Hstm".
      by rewrite /apply_cmds foldl_snoc Hrsm /= Hdup.
    }
    (* Case: Txn [ts] has not prepared, aborted, or committed. *)
    destruct (try_acquire ts wrs tpls) eqn:Hacq; last first.
    { (* Case: Validation fails; abort the transaction. *)
      iFrame "Hrepls Hkeys".
      iMod (txnst_direct_abort with "Hstm") as "Hstm"; first apply Hdup.
      rewrite /apply_cmds foldl_snoc Hrsm /= Hdup Hacq.
      by iFrame.
    }
    (* Case: Validation succeeds; lock the tuples and mark the transaction prepared. *)
    rewrite /apply_cmds foldl_snoc Hrsm /= Hdup Hacq.
    rewrite /try_acquire in Hacq.
    destruct (validate ts wrs tpls) eqn:Hvd; last done.
    inversion_clear Hacq.
    set tpls' := acquire _ _ _.
    (* Extract keys invariant in this group. *)
    iDestruct (keys_inv_group gid with "Hkeys") as "[Hkeys Hkeyso]".
    (* Extract the replicated history and prepared timestamp from keys invariant. *)
    iDestruct (keys_inv_extract_repl_tsprep with "Hkeys") as (tplsK) "(Hkeys & Htpls & %Hdom)".
    (* Agree on tuples from the group and keys invariants. *)
    iDestruct (tuple_repl_big_agree with "Hrepls Htpls") as %->.
    { pose proof (apply_cmds_dom log) as Hdom'.
      rewrite /apply_cmds Hrsm in Hdom'.
      rewrite Hdom.
      by apply keys_group_tpls_group_dom.
    }
    (* Update the replicated history and prepared timestamp. *)
    iMod (tuple_repl_big_update (tpls_group gid tpls') with "Hrepls Htpls") as "[Hrepls Htpls]".
    { apply tpls_group_dom. by rewrite acquire_dom. }
    (* Re-establish keys invariant. *)
  Admitted.

  Lemma group_inv_learn γ gid cmds :
    ∀ log,
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log γ gid log ==∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log γ gid (log ++ cmds).
  Proof.
    iInduction cmds as [| c l] "IH".
    { iIntros (log) "Hkeys Hgroup". rewrite app_nil_r. by iFrame. }
    iIntros (log) "Hkeys Hgroup".
    rewrite cons_middle. rewrite app_assoc.
    destruct c.
    { (* Case: [CmdPrep tid wrs] *)
      iMod (group_inv_learn_prepare with "Hkeys Hgroup") as "[Hkeys Hgroup]".
      by iApply ("IH" with "Hkeys").
    }
  Admitted.

End group_inv.
(* TODO: move to distx_group_inv.v once stable. *)
