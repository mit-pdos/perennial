From iris.algebra Require Import mono_nat mono_list gmap_view gset.
From iris.algebra.lib Require Import dfrac_agree.
From Perennial.base_logic Require Import ghost_map mono_nat saved_prop.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.Helpers Require finite.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Definition dbkey := byte_string.
Definition dbval := option byte_string.
Definition dbhist := list dbval.
Definition dbtpl := (dbhist * nat)%type.
Definition dbmod := (dbkey * dbval)%type.
Definition dbmap := gmap dbkey dbval.
Definition dbkmod := gmap nat dbval.
Definition dbpver := (u64 * dbval)%type.
Definition coordid := (u64 * u64)%type.
Definition ppsl := (u64 * bool)%type.
Definition txnptgs := gset u64.

(** Transaction result. *)
Inductive txnres :=
| ResCommitted (wrs : dbmap)
| ResAborted.

Definition fstring := {k : byte_string | length k < 2 ^ 64 }.

#[local]
Instance fstring_finite :
  finite.Finite fstring.
Proof.
  unfold fstring.
  set(x:=2 ^ 64).
  generalize x. clear x. intros y.
  unshelve refine (finite.surjective_finite (λ x : {k : byte_string | (length k < Z.to_nat y)%nat },
                                               (proj1_sig x) ↾ _ )).
  { abstract (destruct x; simpl; lia). }
  { apply Helpers.finite.list_finite_lt_length. }
  intros [].
  unshelve eexists (exist _ _ _); last rewrite sig_eq_pi /= //.
  simpl. lia.
Qed.

Definition keys_all : gset byte_string :=
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
  0 < size gids_all < 2 ^ 64 - 1.
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
| CmdRead (tid : nat) (key : dbkey)
| CmdAcquire (tid : nat) (pwrs : dbmap) (ptgs : gset u64)
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
Proof.
  refine (inj_countable'
            (λ x, match x with
                  | CmdCommit tid pwrs => inl (tid, pwrs)
                  | CmdAbort tid => inr tid
                  end)
            (λ x, match x with
                  | inl (tid, pwrs) => CmdCommit tid pwrs
                  | inr tid => CmdAbort tid
                  end)
            _).
  intros [|] => //=.
Qed.

#[global]
Instance icommand_eq_decision :
  EqDecision icommand.
Proof. solve_decision. Qed.

#[global]
Instance icommand_countable :
  Countable icommand.
Proof.
  refine (inj_countable'
            (λ x, match x with
                  | CmdAcquire tid pwrs ptgs => inl (tid, pwrs, ptgs)
                  | CmdRead tid key => inr (inl (tid, key))
                  | CmdAdvance tid rank => inr (inr (inl (tid, rank)))
                  | CmdAccept tid rank pdec => inr (inr (inr (tid, rank, pdec)))
                  end)
            (λ x, match x with
                  | inl (tid, pwrs, ptgs) => CmdAcquire tid pwrs ptgs
                  | inr (inl (tid, key)) => CmdRead tid key
                  | inr (inr (inl (tid, rank))) => CmdAdvance tid rank
                  | inr (inr (inr (tid, rank, pdec))) => CmdAccept tid rank pdec
                  end)
            _).
  intros [| | |] => //=.
Qed.

#[global]
Instance command_eq_decision :
  EqDecision command.
Proof. solve_decision. Qed.

#[global]
Instance command_countable :
  Countable command.
Proof.
  refine (inj_countable'
            (λ x, match x with
                  | CCmd cmd => inl cmd
                  | ICmd cmd => inr cmd
                  end)
            (λ x, match x with
                  | inl cmd => CCmd cmd
                  | inr cmd => ICmd cmd
                  end)
            _).
  intros [|] => //=.
Qed.

(** State-machine log. *)
Definition dblog := list ccommand.

(** Converting keys to group IDs. *)
Definition key_to_group (key : dbkey) : u64 :=
  length key `mod` size gids_all.

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
Proof.
  rewrite /key_to_group /gids_all.
  rewrite size_list_to_set; last first.
  { apply seq_U64_NoDup; lia. }
  rewrite length_fmap length_seqZ.
  apply elem_of_list_to_set, list_elem_of_fmap_2, elem_of_seqZ.
  lia.
Qed.

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
  rewrite map_empty_filter in Hempty.
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

Definition valid_backup_rank (rank : nat) := 1 < rank < 2 ^ 64.

Lemma valid_key_length key :
  valid_key key ->
  length key < 2 ^ 64.
Proof.
  intros Hvk.
  rewrite /valid_key /keys_all in Hvk.
  apply elem_of_list_to_set, list_elem_of_fmap_1 in Hvk.
  by destruct Hvk as ([k Hk] & -> & _).
Qed.

Definition valid_ccommand gid (c : ccommand) :=
  match c with
  | CmdCommit ts pwrs => valid_ts ts ∧ valid_pwrs gid pwrs
  | CmdAbort ts => valid_ts ts
  end.

Inductive vote :=
| Accept (d : bool)
| Reject.

#[global]
Instance vote_eq_decision :
  EqDecision vote.
Proof. solve_decision. Qed.

Definition ballot := list vote.

Canonical Structure dbvalO := leibnizO dbval.
Definition dbmapR := gmapR dbkey (dfrac_agreeR dbvalO).
Definition histR := mono_listR dbvalO.
Definition histmR := gmapR dbkey histR.
Definition tsmR := gmapR dbkey (dfrac_agreeR natO).
Canonical Structure dbkmodO := leibnizO dbkmod.
Definition dbkmodR := gmapR dbkey (dfrac_agreeR dbkmodO).
Canonical Structure ccommandO := leibnizO ccommand.
Definition ccommandlR := mono_listR ccommandO.
Definition group_ccommandlR := gmapR u64 ccommandlR.
Definition ccommandsR := gsetR ccommand.
Definition group_ccommandsR := gmapR u64 (dfrac_agreeR ccommandsR).
Canonical Structure boolO := leibnizO bool.
Canonical Structure natboolmvR := gmap_viewR nat (agreeR boolO).
Definition group_natboolmvR := gmapR u64 natboolmvR.
Canonical Structure ppslmR := gmap_viewR (nat * nat) (agreeR boolO).
Definition group_ppslmR := gmapR u64 ppslmR.
Definition replica_tssR := gmapR (u64 * u64) (gmap_viewR nat unitR).
Definition vdlR := mono_listR boolO.
Definition replica_kvdlR := gmapR (u64 * u64 * dbkey) vdlR.
Canonical Structure clogO := leibnizO (list ccommand).
Definition replica_clogR := gmapR (u64 * u64) (dfrac_agreeR clogO).
Canonical Structure ilogO := leibnizO (list (nat * icommand)).
Definition replica_ilogR := gmapR (u64 * u64) (dfrac_agreeR ilogO).
Canonical Structure voteO := leibnizO vote.
Definition ballotR := mono_listR voteO.
Definition ballotmR := gmap_viewR nat (agreeR gnameO).
Definition replica_ballotmR := gmapR (u64 * u64) ballotmR.
Canonical Structure coordidO := leibnizO coordid.
Definition votemR := gmap_viewR (nat * nat) (agreeR coordidO).
Definition replica_votemR := gmapR (u64 * u64) votemR.
Definition tokenmR := gmap_viewR (nat * nat * u64) unitR.
Definition replica_tokenmR := gmapR (u64 * u64) tokenmR.
Definition byte_stringO := listO w8.
Definition replica_stringR := gmapR (u64 * u64) (agreeR byte_stringO).
Definition trmlmR := gmap_viewR chan unitR.
Definition group_trmlmR := gmapR u64 trmlmR.
Canonical Structure dbhistO := leibnizO dbhist.
Definition phistmR := gmapR dbkey (dfrac_agreeR dbhistO).
Definition sid_ownR := gmapR u64 (exclR unitO).

Class tulip_ghostG (Σ : gFunctors) :=
  { (* common resources defined in res.v *)
    #[global] db_ptstoG :: inG Σ dbmapR;
    #[global] repl_histG :: inG Σ histmR;
    #[global] repl_tsG :: inG Σ tsmR;
    #[global] lnrz_kmodG :: inG Σ dbkmodR;
    #[global] cmtd_kmodG :: inG Σ dbkmodR;
    #[global] txn_logG :: inG Σ group_ccommandlR;
    #[global] txn_cpoolG :: inG Σ group_ccommandsR;
    (* txnsys resources defined in res_txnsys.v *)
    #[global] cmtd_histG :: inG Σ histmR;
    #[global] lnrz_histG :: inG Σ histmR;
    #[global] txn_resG :: ghost_mapG Σ nat txnres;
    #[global] txn_oneshot_wrsG :: ghost_mapG Σ nat (option dbmap);
    #[global] lnrz_tidG :: ghost_mapG Σ nat unit;
    #[global] wabt_tidG :: ghost_mapG Σ nat unit;
    #[global] cmt_tmodG :: ghost_mapG Σ nat dbmap;
    #[global] excl_tidG :: ghost_mapG Σ nat unit;
    #[global] txn_client_tokenG :: ghost_mapG Σ (nat * u64) unit;
    #[global] txn_postcondG :: ghost_mapG Σ nat (dbmap -> Prop);
    #[global] largest_tsG :: mono_natG Σ;
    (* group resources defined in res_group.v *)
    #[global] group_prepG :: inG Σ group_natboolmvR;
    #[global] group_ppslG :: inG Σ group_ppslmR;
    #[global] group_commitG :: inG Σ group_natboolmvR;
    (* replica resources defined in res_replica.v *)
    #[global] replica_validated_tsG :: inG Σ replica_tssR;
    #[global] replica_key_validationG :: inG Σ replica_kvdlR;
    #[global] replica_clogG :: inG Σ replica_clogR;
    #[global] replica_ilogG :: inG Σ replica_ilogR;
    #[global] replica_ballotG :: inG Σ replica_ballotmR;
    #[global] ballotG :: inG Σ ballotR;
    #[global] replica_voteG :: inG Σ replica_votemR;
    #[global] replica_tokenG :: inG Σ replica_tokenmR;
    #[global] replica_ilog_fnameG :: inG Σ replica_stringR;
    (* network resources defined din res_network.v *)
    #[global] group_trmlmG :: inG Σ group_trmlmR;
    (* txn local resources defined in program/txn/res.v *)
    #[global] txnmapG :: ghost_mapG Σ dbkey dbval;
    #[global] local_gid_tokenG :: ghost_mapG Σ u64 unit;
    (* replica local resources defined in program/replica/res.v *)
    #[global] phys_histG :: inG Σ phistmR;
    (* tid *)
    #[global] gentid_predG :: savedPredG Σ val;
    #[global] gentid_reservedG :: ghost_mapG Σ u64 gname;
    #[global] gentid_sidG :: inG Σ sid_ownR;
    #[global] tulip_stagedG :: stagedG Σ;
  }.

Definition tulip_ghostΣ :=
  #[ (* res.v *)
     GFunctor dbmapR;
     GFunctor histmR;
     GFunctor tsmR;
     GFunctor dbkmodR;
     GFunctor dbkmodR;
     GFunctor group_ccommandlR;
     GFunctor group_ccommandsR;
     (* res_txnsys.v *)
     GFunctor histmR;
     GFunctor histmR;
     ghost_mapΣ nat txnres;
     ghost_mapΣ nat (option dbmap);
     ghost_mapΣ nat unit;
     ghost_mapΣ nat unit;
     ghost_mapΣ nat dbmap;
     ghost_mapΣ nat unit;
     ghost_mapΣ (nat * u64) unit;
     ghost_mapΣ nat (dbmap -> Prop);
     mono_natΣ;
     (* res_group.v *)
     GFunctor group_natboolmvR;
     GFunctor group_ppslmR;
     GFunctor group_natboolmvR;
     (* res_replica.v *)
     GFunctor replica_tssR;
     GFunctor replica_kvdlR;
     GFunctor replica_clogR;
     GFunctor replica_ilogR;
     GFunctor replica_ballotmR;
     GFunctor ballotR;
     GFunctor replica_votemR;
     GFunctor replica_tokenmR;
     GFunctor replica_stringR;
     (* res_network.v *)
     GFunctor group_trmlmR;
     (* program/txn/res.v *)
     ghost_mapΣ dbkey dbval;
     ghost_mapΣ u64 unit;
     (* program/replica/res.v *)
     GFunctor phistmR;
     ghost_mapΣ u64 gname;
     savedPredΣ val;
     GFunctor sid_ownR;
     stagedΣ
   ].

#[global]
Instance subG_tulip_ghostG {Σ} :
  subG tulip_ghostΣ Σ → tulip_ghostG Σ.
Proof. solve_inG. Qed.

Record tulip_names :=
  { (* res.v *)
    db_ptsto : gname;
    repl_hist : gname;
    repl_ts : gname;
    lnrz_kmod : gname;
    cmtd_kmod : gname;
    txn_log : gname;
    txn_cpool : gname;
    (* res_txnsys.v *)
    cmtd_hist : gname;
    lnrz_hist : gname;
    txn_res : gname;
    txn_oneshot_wrs : gname;
    lnrz_tid : gname;
    wabt_tid : gname;
    cmt_tmod : gname;
    excl_tid : gname;
    txn_client_token : gname;
    txn_postcond : gname;
    largest_ts : gname;
    (* res_group.v *)
    group_prep : gname;
    group_prepare_proposal : gname;
    group_commit : gname;
    (* res_replica.v *)
    replica_validated_ts : gname;
    replica_key_validation : gname;
    replica_clog : gname;
    replica_ilog : gname;
    replica_ballot : gname;
    replica_vote : gname;
    replica_token : gname;
    replica_ilog_fname : gname;
    (* res_network.v *)
    group_trmlm : gname;
    (* tid *)
    sids : gname;
    gentid_reserved : gname;
  }.

Definition sysNS := nroot .@ "sys".
Definition tulipNS := sysNS .@ "tulip".
Definition tsNS := sysNS .@ "ts".
Definition txnlogNS := sysNS .@ "txnlog".
