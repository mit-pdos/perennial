From Perennial.program_proof Require Import grove_prelude.
From Perennial.Helpers Require finite.

Definition dbkey := string.
Definition dbval := option string.
Definition dbhist := list dbval.
Definition dbtpl := (dbhist * nat)%type.
Definition dbmod := (dbkey * dbval)%type.
Definition dbmap := gmap dbkey dbval.
Definition dbkmod := gmap nat dbval.
Definition dbpver := (u64 * dbval)%type.
Definition coordid := (u64 * u64)%type.
Definition ppsl := (u64 * bool)%type.

(** Transaction result. *)
Inductive txnres :=
| ResCommitted (wrs : dbmap)
| ResAborted.

Definition fstring := {k : string | String.length k < 2 ^ 64}.

#[local]
Instance fstring_finite :
  finite.Finite fstring.
Proof. apply Helpers.finite.string_finite_Zlt_length. Qed.

Definition keys_all : gset string :=
  list_to_set (map proj1_sig (finite.enum fstring)).

(** Transaction status on group/replica. *)
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

Definition gids_all : gset u64 := list_to_set (fmap W64 (seqZ 0 2)).

Lemma size_gids_all :
  size gids_all < 2 ^ 64 - 1.
Proof.
  rewrite /gids_all size_list_to_set; last first.
  { apply seq_U64_NoDup; lia. }
  rewrite length_fmap length_seqZ.
  lia.
Qed.

(* TODO: Parametrize the number of replicas in each group. *)
Definition rids_all : gset u64 := list_to_set (fmap W64 (seqZ 0 3)).

Lemma size_rids_all :
  size rids_all = 3%nat.
Proof.
  rewrite size_list_to_set.
  { rewrite length_fmap length_seqZ. lia. }
  { apply seq_U64_NoDup; lia. }
Qed.

(** Transaction R/C/A action. *)
Inductive action :=
| ActCommit (tid : nat) (wrs : dbmap)
| ActAbort (tid : nat)
| ActRead (tid : nat) (key : dbkey).

(** State-machine commands. *)
Inductive ccommand :=
| CmdCommit (tid : nat) (pwrs : dbmap)
| CmdAbort (tid : nat).

Inductive icommand :=
| CmdAcquire (tid : nat) (pwrs : dbmap) (ptgs : gset u64)
| CmdRead (tid : nat) (key : dbkey)
| CmdAdvance (tid : nat) (rank : nat)
| CmdAccept (tid : nat) (rank : nat) (pdec : bool).

Inductive command :=
| CCmd (cmd : ccommand)
| ICmd (cmd : icommand).

#[global]
Instance ccommand_eq_decision :
  EqDecision ccommand.
Proof. solve_decision. Qed.

#[global]
Instance ccommand_countable :
  Countable ccommand.
Admitted.

#[global]
Instance icommand_eq_decision :
  EqDecision icommand.
Proof. solve_decision. Qed.

#[global]
Instance icommand_countable :
  Countable icommand.
Admitted.

#[global]
Instance command_eq_decision :
  EqDecision command.
Proof. solve_decision. Qed.

#[global]
Instance command_countable :
  Countable command.
Admitted.

(** State-machine log. *)
Definition dblog := list ccommand.

(** Converting keys to group IDs. *)
Definition key_to_group (key : dbkey) : u64.
Admitted.

(** Participant groups. *)
Definition ptgroups (keys : gset dbkey) : gset u64 :=
  set_map key_to_group keys.

Definition wrs_group gid (wrs : dbmap) :=
  filter (λ t, key_to_group t.1 = gid) wrs.

Definition tpls_group gid (tpls : gmap dbkey dbtpl) :=
  filter (λ t, key_to_group t.1 = gid) tpls.

(* TODO: [filter_group] subsumes [wrs_group] and [tpls_group]. *)
Definition filter_group `{Countable A} gid (m : gmap dbkey A) :=
  filter (λ t, key_to_group t.1 = gid) m.

Definition keys_group gid (keys : gset dbkey) :=
  filter (λ k, key_to_group k = gid) keys.

Definition valid_pwrs (gid : u64) (pwrs : dbmap) :=
  dom pwrs ⊆ keys_group gid keys_all.

Lemma elem_of_key_to_group key :
  key_to_group key ∈ gids_all.
Admitted.

Lemma elem_of_key_to_group_ptgroups key keys :
  key ∈ keys ->
  key_to_group key ∈ ptgroups keys.
Proof. apply elem_of_map_2. Qed.

Lemma subseteq_ptgroups keys :
  ptgroups keys ⊆ gids_all.
Proof.
  unfold ptgroups.
  intros gid Hgid.
  apply elem_of_map_1 in Hgid as [key [-> _]].
  apply elem_of_key_to_group.
Qed.

Lemma elem_of_ptgroups keys gid :
  gid ∈ ptgroups keys ↔ keys_group gid keys ≠ ∅.
Proof.
  rewrite /ptgroups /keys_group.
  split; first set_solver.
  intros Hne.
  rewrite elem_of_map.
  apply set_choose_L in Hne as [k Hk].
  set_solver.
Qed.

Lemma lookup_wrs_group_Some gid wrs k v :
  (wrs_group gid wrs) !! k = Some v ↔ wrs !! k = Some v ∧ key_to_group k = gid.
Proof. by rewrite /wrs_group map_lookup_filter_Some /=. Qed.

Lemma lookup_wrs_group_None gid wrs k :
  (wrs_group gid wrs) !! k = None ↔
  wrs !! k = None ∨ key_to_group k ≠ gid.
Proof.
  rewrite /wrs_group map_lookup_filter_None /=.
  split; intros [Hnone | Hne].
  - by left.
  - destruct (wrs !! k) as [v |] eqn:Hv; last by left.
    apply Hne in Hv. by right.
  - by left.
  - by right.
Qed.

Lemma wrs_group_insert gid wrs k v :
  key_to_group k = gid ->
  wrs_group gid (<[k := v]> wrs) = <[k := v]> (wrs_group gid wrs).
Proof. intros Hgid. by rewrite /wrs_group map_filter_insert_True. Qed.

Lemma wrs_group_insert_ne gid wrs k v :
  key_to_group k ≠ gid ->
  wrs_group gid (<[k := v]> wrs) = wrs_group gid wrs.
Proof. intros Hgid. by rewrite /wrs_group map_filter_insert_not. Qed.

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

Lemma elem_of_ptgroups_non_empty gid wrs :
  gid ∈ ptgroups (dom wrs) ->
  wrs_group gid wrs ≠ ∅.
Proof.
  intros Hptg Hempty.
  rewrite /ptgroups elem_of_map in Hptg.
  destruct Hptg as (k & Hktg & Hin).
  apply elem_of_dom in Hin as [v Hv].
  rewrite map_filter_empty_iff in Hempty.
  specialize (Hempty _ _ Hv). simpl in Hempty. done.
Qed.

(** Safe state-machine conditions. *)
Definition readable (tid : nat) (hist : dbhist) (tsprep : nat) :=
  tsprep = O ∨ (tid ≤ tsprep)%nat.

Definition lockable (tid : nat) (hist : dbhist) (tsprep : nat) :=
  tsprep = O ∧ (length hist ≤ tid)%nat.

Definition tuples_lockable (tid : nat) (tpls : gmap dbkey dbtpl) :=
  map_Forall (λ _ tpl, lockable tid tpl.1 tpl.2) tpls.

(* Note the coercion here. [word] seems to work better with this. *)
Definition valid_ts (ts : nat) := 0 < ts < 2 ^ 64.

Definition valid_wrs (wrs : dbmap) := dom wrs ⊆ keys_all.

Definition valid_key (key : dbkey) := key ∈ keys_all.

Definition valid_ccommand gid (c : ccommand) :=
  match c with
  | CmdCommit ts pwrs => valid_ts ts ∧ valid_pwrs gid pwrs
  | CmdAbort ts => valid_ts ts
  end.

Class tulip_ghostG (Σ : gFunctors).

Record tulip_names := {}.
Record replica_names := {}.

Section msg.

  Inductive txnreq :=
  | ReadReq        (ts : u64) (key : string)
  | FastPrepareReq (ts : u64) (pwrs : dbmap)
  | ValidateReq    (ts : u64) (rank : u64) (pwrs : dbmap)
  | PrepareReq     (ts : u64) (rank : u64)
  | UnprepareReq   (ts : u64) (rank : u64)
  | QueryReq       (ts : u64) (rank : u64)
  | RefreshReq     (ts : u64) (rank : u64)
  | CommitReq      (ts : u64) (pwrs : dbmap)
  | AbortReq       (ts : u64).

  #[global]
  Instance txnreq_eq_decision :
    EqDecision txnreq.
  Proof. solve_decision. Qed.

  #[global]
  Instance txnreq_countable :
    Countable txnreq.
  Admitted.

  Definition encode_txnreq (req : txnreq) : list u8.
  Admitted.

  Inductive rpres :=
  | ReplicaOK
  | ReplicaCommittedTxn
  | ReplicaAbortedTxn
  | ReplicaStaleCoordinator
  | ReplicaFailedValidation
  | ReplicaInvalidRank
  | ReplicaWrongLeader.

  #[global]
  Instance rpres_eq_decision :
    EqDecision rpres.
  Proof. solve_decision. Qed.

  Inductive txnresp :=
  | ReadResp        (ts : u64) (rid : u64) (key : string) (ver : dbpver) (slow : bool)
  | FastPrepareResp (ts : u64) (rid : u64) (res : rpres)
  | ValidateResp    (ts : u64) (rid : u64) (res : rpres)
  | PrepareResp     (ts : u64) (rank : u64) (rid : u64) (res : rpres)
  | UnprepareResp   (ts : u64) (rank : u64) (rid : u64) (res : rpres)
  | QueryResp       (ts : u64) (res : rpres)
  | CommitResp      (ts : u64) (res : rpres)
  | AbortResp       (ts : u64) (res : rpres).

  #[global]
  Instance txnresp_eq_decision :
    EqDecision txnresp.
  Proof. solve_decision. Qed.

  #[global]
  Instance txnresp_countable :
    Countable txnresp.
  Admitted.

  Definition encode_txnresp (resp : txnresp) : list u8.
  Admitted.

End msg.
