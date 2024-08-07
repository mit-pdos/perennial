From Perennial.program_proof Require Import grove_prelude.

Definition dbkey := string.
Definition dbval := option string.
Definition dbhist := list dbval.
Definition dbtpl := (dbhist * nat)%type.
Definition dbmod := (dbkey * dbval)%type.
Definition dbmap := gmap dbkey dbval.
Definition dbkmod := gmap nat dbval.

(** Transaction result. *)
Inductive txnres :=
| ResCommitted (wrs : dbmap)
| ResAborted.

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

Definition groupid := nat.
Definition gids_all : gset groupid := list_to_set (seq 0 2).

(** Transaction R/W action. *)
Inductive action :=
| ActCmt (tid : nat) (wrs : dbmap)
| ActRead (tid : nat) (key : dbkey).

(** State-machine commands. *)
Inductive command :=
| CmdRead (tid : nat) (key : dbkey)
| CmdPrep (tid : nat) (wrs : dbmap)
| CmdCmt (tid : nat)
| CmdAbt (tid : nat).

#[global]
Instance command_eq_decision :
  EqDecision command.
Proof. solve_decision. Qed.

#[global]
Instance command_countable :
  Countable command.
Admitted.

(** State-machine log. *)
Definition dblog := list command.

(** Converting keys to group IDs. *)
Definition key_to_group (key : dbkey) : groupid.
Admitted.

(** Participant groups. *)
Definition ptgroups (keys : gset dbkey) : gset groupid :=
  set_map key_to_group keys.

Definition wrs_group gid (wrs : dbmap) :=
  filter (λ t, key_to_group t.1 = gid) wrs.

Definition tpls_group gid (tpls : gmap dbkey dbtpl) :=
  filter (λ t, key_to_group t.1 = gid) tpls.

Definition keys_group gid (keys : gset dbkey) :=
  filter (λ k, key_to_group k = gid) keys.

Definition valid_pwrs (gid : groupid) (pwrs : dbmap) :=
  dom pwrs ⊆ keys_group gid keys_all.

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

(** Safe state-machine conditions. *)
Definition readable (tid : nat) (hist : dbhist) (tsprep : nat) :=
  tsprep = O ∨ (tid ≤ tsprep)%nat.

Definition lockable (tid : nat) (hist : dbhist) (tsprep : nat) :=
  tsprep = O ∧ (length hist ≤ tid)%nat.

(* Note the coercion here. [word] seems to work better with this. *)
Definition valid_ts (ts : nat) := 0 < ts < 2 ^ 64.

Definition valid_wrs (wrs : dbmap) := dom wrs ⊆ keys_all.

Definition valid_key (key : dbkey) := key ∈ keys_all.

Class distx_ghostG (Σ : gFunctors).

Record distx_names := {}.
Record replica_names := {}.
