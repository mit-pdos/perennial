From Perennial.program_proof Require Export grove_prelude.

Definition dbkey := string.
Definition dbval := option string.
Definition dbhist := list dbval.
Definition dbtpl := (dbhist * nat)%type.
Canonical Structure dbvalO := leibnizO dbval.
Definition dbmap := gmap dbkey dbval.

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

Definition dblog := list command.

(* Transaction status on replica *)
Inductive txnst :=
| StPrepared (wrs : dbmap)
| StCommitted
| StAborted.

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
  | State txnst _ => txnst !! ts = Some (StPrepared wrs)
  | _ => False
  end.

Definition has_aborted ts log :=
  match apply_cmds log with
  | State txnst _ => txnst !! ts = Some StAborted
  | _ => False
  end.

Definition wrs_group (wrs : dbmap) gid :=
  filter (λ x, key_to_group x.1 = gid) wrs.

(* Participant groups. *)
Definition ptgroups (keys : gset dbkey) :=
  set_fold (λ k s, {[key_to_group k]} ∪ s) (∅ : gset groupid) keys.

Definition all_prepared ts wrs (logs : gmap groupid dblog) :=
  map_Forall (λ gid log, has_prepared ts (wrs_group wrs gid) log) logs ∧
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

  Definition repl_half γ (k : dbkey) (t : dbtpl) : iProp Σ.
  Admitted.

  Definition resm_auth γ (resm : gmap nat txnres) : iProp Σ.
  Admitted.

  Definition resm_evidence γ (ts : nat) (res : txnres) : iProp Σ.
  Admitted.

  Definition log_auth γ (gid : groupid) (log : dblog) : iProp Σ.
  Admitted.

  Definition log_lb γ (gid : groupid) (log : dblog) : iProp Σ.
  Admitted.
  
  Definition ts_auth γ (ts : nat) : iProp Σ.
  Admitted.

  Definition ts_lb γ (ts : nat) : iProp Σ.
  Admitted.

  Definition txn_proph (p : proph_id) (acts : list action) : iProp Σ.
  Admitted.
End ghost.

Section inv.
  Context `{!distx_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : distx_names).

  Definition mvcc_inv γ p : iProp Σ :=
    ∃ (ts : nat) (future past : list action)
      (txns_cmt txns_abt : gmap nat dbmap),
      (* global timestamp *)
      "Hts"    ∷ ts_auth γ ts ∗
      (* prophecy variable *)
      "Hproph" ∷ txn_proph p future ∗
      (* TODO: asserting ownership of txns_cmt and txns_abt. *)
      "%Hcf"   ∷ ⌜conflict_free future txns_cmt⌝ ∗
      "%Hcp"   ∷ ⌜conflict_past future past txns_abt⌝.

  Definition per_key_inv γ (key : dbkey) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd repl : dbhist)
      (tslb : nat) (tsprep : nat)
      (wrs : dbmap) (ongoing : option (nat * dbval))
      (tmods : gmap nat dbval),
      "Hdbv" ∷ db_ptsto γ key dbv ∗
      "Hrepl" ∷ repl_half γ key (repl, tsprep) ∗
      (* TODO: missing some ownership. *)
      "#Htslb" ∷ ts_lb γ tslb ∗
      "#Hresme" ∷ if ongoing then resm_evidence γ tsprep (ResCommitted wrs) else True ∗
      "%Hlast" ∷ ⌜last lnrz = Some dbv⌝ ∗
      "%Hprefix" ∷ ⌜prefix cmtd lnrz⌝ ∗
      "%Hext" ∷ ⌜(length lnrz ≤ S tslb)%nat⌝ ∗
      "%Hlnrz" ∷ ⌜diff_by_linearized cmtd lnrz tmods⌝ ∗
      "%Hongoing" ∷ ⌜diff_by_ongoing repl cmtd ongoing⌝ ∗
      "%Hexcl" ∷ ⌜exclusive ongoing tsprep (wrs !! key)⌝.

  Definition per_group_inv γ (gid : groupid) : iProp Σ :=
    ∃ (log : dblog) (txnm : gmap nat txnst) (tpls : gmap dbkey dbtpl),
      "Hrepls" ∷ ([∗ map] key ↦ tpl ∈ tpls, repl_half γ key tpl) ∗
      (* TODO: asserting the domain of tpls. *)
      "%Hrsm" ∷ ⌜apply_cmds log = State txnm tpls⌝.

  Definition per_res_inv γ (ts : nat) (res : txnres) : iProp Σ :=
    ∃ (logs : gmap groupid dblog),
      "#Hlogs" ∷ ([∗ map] gid ↦ log ∈ logs, log_lb γ gid log) ∗
      "%Hsafeca" ∷ ⌜safe_finalize ts res logs⌝.

  Definition commit_abort_inv γ : iProp Σ :=
    ∃ (resm : gmap nat txnres),
      "Hresm" ∷ resm_auth γ resm ∗
      "#Hress" ∷ ([∗ map] tid ↦ res ∈ resm, per_res_inv γ tid res).

  Definition distx_inv_def γ p : iProp Σ :=
    (* MVCC invariants *)
    "Hproph" ∷ mvcc_inv γ p ∗
    (* keys invariants *)
    "Hkeys"  ∷ ([∗ set] key ∈ keys_all, per_key_inv γ key) ∗
    (* groups invariants *)
    "Hgroups" ∷ ([∗ list] gid ∈ gids_all, per_group_inv γ gid) ∗
    (* commit/abort invariants *)
    "Hres" ∷ commit_abort_inv γ.
End inv.
(* TODO: move to distx_own.v once stable. *)
