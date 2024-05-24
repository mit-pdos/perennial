From Perennial.program_proof Require Export grove_prelude.
From Perennial.program_logic Require Export atomic. (* prefer the ncfupd atomics *)

Definition dbkey := string.
Definition dbval := option string.
Definition dbhist := list dbval.
Definition dbtpl := (dbhist * nat)%type.
Definition dbmod := (dbkey * dbval)%type.
Canonical Structure dbvalO := leibnizO dbval.
Definition dbmap := gmap dbkey dbval.

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
  (* TODO: check if [<] is the right thing to do. *)
  | Some _, Some (vs, tsprep) => Some (bool_decide (tsprep = O ∧ length vs < tid)%nat)
  | _, _ => None
  end.

Definition validate (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  map_fold (λ _, andb) true (merge (validate_key tid) wrs tpls).

Definition acquire_key (tid : nat) (wr : option dbval) (tpl : option dbtpl) :=
  match wr, tpl with
  | None, Some (vs, tsprep) => Some (vs, tsprep)
  | Some _, Some (vs, _) => Some (vs, tid)
  | _, _ => None
  end.

Definition acquire (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  merge (acquire_key tid) wrs tpls.

Definition try_acquire (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  if validate tid wrs tpls then Acquired (acquire tid wrs tpls) else NotAcquired.

Definition apply_prepare st (tid : nat) (wrs : dbmap) :=
  match st with
  | State txns tpls =>
      match txns !! tid with
      | Some _ => st
      | None =>  match try_acquire tid wrs tpls with
                | Acquired tpls' => State (<[ tid := StPrepared wrs ]> txns) tpls'
                | NotAcquired => State (<[ tid := StAborted ]> txns) tpls
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
  | State txns tpls =>
      match txns !! tid with
      | Some StCommitted => st
      | Some (StPrepared wrs) => State (<[ tid := StCommitted ]> txns) (multiwrite tid wrs tpls)
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
  | State txns tpls =>
      match txns !! tid with
      | Some StAborted => st
      | Some (StPrepared wrs) => State (<[ tid := StAborted ]> txns) (release tid wrs tpls)
      | None => State (<[ tid := StAborted ]> txns) tpls
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
  | State txns tpls =>
      match tpls !! key with
      | Some (vs, tsprep) => State txns (<[ key := (read tid vs tsprep) ]> tpls)
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

(* TODO: should initial tuple state be ∅? *)
Definition apply_cmds (cmds : list command) :=
  foldl apply_cmd (State ∅ ∅) cmds.

Inductive action :=
| ActCmt (tid : nat) (wrs : dbmap)
| ActRead (tid : nat) (key : dbkey).

Definition diff_by_ongoing (repl cmtd : list dbval) (kcmt : option (nat * dbval)) :=
  match kcmt with
  | Some (ts, v) => cmtd = last_extend ts repl ++ [v]
  | None => ∃ ts', repl = last_extend ts' cmtd
end.

Definition exclusive (ongoing : option (nat * dbval)) (tsprep : nat) (wr : option dbval) :=
  match ongoing with
  | Some (ts, v) => tsprep = ts ∧ wr = Some v
  | None => True
  end.

Definition diff_by_linearized (cmtd lnrz : list dbval) (txns : gmap nat dbval) : Prop.
Admitted.

Definition conflict_free (acts : list action) (txns : gmap nat dbmap) : Prop.
Admitted.

Definition conflict_past (acts_future acts_past : list action) (txns : gmap nat dbmap) : Prop.
Admitted.

Definition repl_impl_cmtd (acts : list action) (cmds : list command) :=
  ∀ ts, CmdCmt ts ∈ cmds → ∃ wrs, ActCmt ts wrs ∈ acts.

Definition has_prepared ts wrs log :=
  match apply_cmds log with
  | State stm _ => stm !! ts = Some (StPrepared wrs)
  | _ => False
  end.

Definition has_aborted ts log :=
  match apply_cmds log with
  | State stm _ => stm !! ts = Some StAborted
  | _ => False
  end.

Definition wrs_group gid (wrs : dbmap) :=
  filter (λ x, key_to_group x.1 = gid) wrs.

Definition keys_group gid (keys : gset string) :=
  filter (λ x, key_to_group x = gid) keys.

(* Participant groups. *)
Definition ptgroups (keys : gset dbkey) :=
  set_fold (λ k s, {[key_to_group k]} ∪ s) (∅ : gset groupid) keys.

Definition all_prepared ts wrs (logs : gmap groupid dblog) :=
  map_Forall (λ gid log, has_prepared ts (wrs_group gid wrs) log) logs ∧
  dom logs = ptgroups (dom wrs).

Definition some_aborted ts (logs : gmap groupid dblog) :=
  map_Exists (λ gid log, has_aborted ts log) logs.

Definition safe_finalize ts res logs :=
  match res with
  | ResCommitted wrs => all_prepared ts wrs logs
  | ResAborted => some_aborted ts logs
  end.

Definition past_commit (acts : list action) (resm : gmap nat txnres) :=
  ∀ ts wrs, ActCmt ts wrs ∈ acts → resm !! ts = Some (ResCommitted wrs).

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

  Definition ts_repl_half γ (k : dbkey) (ts : nat) : iProp Σ.
  Admitted.

  Definition tuple_repl_half γ (k : dbkey) (t : dbtpl) : iProp Σ :=
    hist_repl_half γ k t.1 ∗ ts_repl_half γ k t.2.

  Definition txnres_auth γ (resm : gmap nat txnres) : iProp Σ.
  Admitted.

  Definition txnres_receipt γ (ts : nat) (res : txnres) : iProp Σ.
  Admitted.

  #[global]
  Instance txnres_receipt_persistent γ ts res :
    Persistent (txnres_receipt γ ts res).
  Admitted.

  Definition txnres_cmt  γ ts wrs :=
    txnres_receipt γ ts (ResCommitted wrs).

  Definition txnres_abt  γ ts :=
    txnres_receipt γ ts ResAborted.

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

  Definition txn_proph γ (acts : list action) : iProp Σ.
  Admitted.
End ghost.

Section spec.
  Context `{!distx_ghostG Σ}.

  Definition group_txnst γ gid ts st : iProp Σ :=
    ∃ log, clog_lb γ gid log ∧ ⌜log_txnst ts st log⌝.

End spec.
  
Section inv.
  Context `{!heapGS Σ, !distx_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : distx_names).

  Definition valid_res γ (ts : nat) (res : txnres) : iProp Σ :=
    ∃ (logs : gmap groupid dblog),
      clog_lbs γ logs ∧ ⌜safe_finalize ts res logs⌝.

  Definition txn_inv γ : iProp Σ :=
    ∃ (ts : nat) (future past : list action)
      (txns_cmt txns_abt : gmap nat dbmap)
      (resm : gmap nat txnres),
      (* global timestamp *)
      "Hts"    ∷ ts_auth γ ts ∗
      (* prophecy variable *)
      "Hproph" ∷ txn_proph γ future ∗
      (* transaction result map *)
      "Hresm" ∷ txnres_auth γ resm ∗
      "#Hvr"  ∷ ([∗ map] tid ↦ res ∈ resm, valid_res γ tid res) ∗
      (* TODO: asserting ownership of txns_cmt and txns_abt. *)
      "%Hcf"   ∷ ⌜conflict_free future txns_cmt⌝ ∗
      "%Hcp"   ∷ ⌜conflict_past future past txns_abt⌝.

  Definition key_inv γ (key : dbkey) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd repl : dbhist)
      (tslb : nat) (tsprep : nat)
      (wrs : dbmap) (ongoing : option (nat * dbval))
      (tmods : gmap nat dbval),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hreplh"    ∷ hist_repl_half γ key repl ∗
      "Hreplt"    ∷ ts_repl_half γ key tsprep ∗
      (* TODO: missing some ownership. *)
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "#Hresme"   ∷ if ongoing then txnres_cmt γ tsprep wrs else True ∗
      "%Hlast"    ∷ ⌜last lnrz = Some dbv⌝ ∗
      "%Hprefix"  ∷ ⌜prefix cmtd lnrz⌝ ∗
      "%Hext"     ∷ ⌜(length lnrz ≤ S tslb)%nat⌝ ∗
      "%Hlnrz"    ∷ ⌜diff_by_linearized cmtd lnrz tmods⌝ ∗
      "%Hongoing" ∷ ⌜diff_by_ongoing repl cmtd ongoing⌝ ∗
      "%Hexcl"    ∷ ⌜exclusive ongoing tsprep (wrs !! key)⌝.

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
      (txnm : gmap nat txnst) (tpls : gmap dbkey dbtpl),
      "Hlog"    ∷ clog_half γ gid log ∗
      "Hcpool"  ∷ cpool_half γ gid cpool ∗
      "Hrepls"  ∷ ([∗ map] key ↦ tpl ∈ tpls, tuple_repl_half γ key tpl) ∗
      "#Hvc"    ∷ ([∗ set] c ∈ cpool, valid_cmd γ c) ∗
      "%Hshard" ∷ ⌜dom tpls = keys_group gid keys_all⌝ ∗
      "%Hrsm"   ∷ ⌜apply_cmds log = State txnm tpls⌝.

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
