From Perennial.program_proof Require Export grove_prelude.

Definition dbkey := string.
Definition dbval := option string.
Definition dbtpl := (list dbval * nat)%type.
Canonical Structure dbvalO := leibnizO dbval.
Notation Nil := (None : dbval).
Notation Value x := (Some x : dbval).
Definition dbmap := gmap dbkey dbval.

Inductive command :=
| CmdPrep (tid : nat) (wrs : dbmap)
| CmdCmt (tid : nat)
| CmdAbt (tid : nat)
| CmdRead (tid : nat) (key : dbkey).

(* Transaction status *)
Inductive txnst :=
| Prepared (wrs : dbmap)
| Committed
| Aborted.

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
                | Acquired tpls' => State (<[ tid := Prepared wrs ]> txns) tpls'
                | NotAcquired => State (<[ tid := Aborted ]> txns) tpls
                end
      end
  | Stuck => Stuck
  end.

(* TODO: reorder [x] and [n]. *)
Definition extend {X} (x : X) (n : nat) (l : list X) :=
    l ++ replicate (n - length l) x.

Definition multiwrite_key (tid : nat) (wr : option dbval) (tpl : option dbtpl) :=
  match wr, tpl with
  | None, Some (vs, tsprep) => Some (vs, tsprep)
  | Some v, Some (vs, _) => Some (extend v tid vs, O)
  | _, _ => None
  end.

Definition multiwrite (tid : nat) (wrs : dbmap) (tpls : gmap dbkey dbtpl) :=
  merge (multiwrite_key tid) wrs tpls.

Definition apply_commit st (tid : nat) :=
  match st with
  | State txns tpls =>
      match txns !! tid with
      | Some Committed => st
      | Some (Prepared wrs) => State (<[ tid := Committed ]> txns) (multiwrite tid wrs tpls)
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
      | Some Aborted => st
      | Some (Prepared wrs) => State (<[ tid := Aborted ]> txns) (release tid wrs tpls)
      | None => State (<[ tid := Aborted ]> txns) tpls
      | _ => Stuck
      end
  | Stuck => Stuck
  end.

(* TODO *)
Definition last_extend {A} (n : nat) (l : list A) := l.

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

Definition diff_by_linearized (cmtd lnrz : list dbval) (txns : gmap nat dbmap) : Prop.
Admitted.

Definition conflict_free (acts : list action) (txns : gmap nat dbmap) : Prop.
Admitted.

Definition conflict_past (acts_future acts_past : list action) (txns : gmap nat dbmap) : Prop.
Admitted.

Definition exec_eq (key : dbkey) (tpls : gmap dbkey dbtpl) (repl : list dbval) :=
  ∃ ts, tpls !! key = Some (repl, ts).

Definition per_key_inv (key : dbkey) (db : dbmap) (kcmts : gmap dbkey (nat * dbval)) txns tpls :=
  ∃ repl cmtd lnrz,
    db !! key = last lnrz ∧
    exec_eq key tpls repl ∧
    prefix cmtd lnrz ∧
    diff_by_ongoing repl cmtd (kcmts !! key) ∧
    diff_by_linearized cmtd lnrz txns.

Definition exclusive
  (acts : list action) (cmds : list command)
  (kcmts : gmap dbkey (nat * dbval)) :=
  ∀ key, match kcmts !! key with
         | Some (ts, _) => (∃ wrs, ActCmt ts wrs ∈ acts) ∧ CmdCmt ts ∉ cmds
         | _ => True
         end.

Definition repl_impl_cmtd (acts : list action) (cmds : list command) :=
  ∀ ts, CmdCmt ts ∈ cmds → ∃ wrs, ActCmt ts wrs ∈ acts.

Definition has_prepared ts wrs cmds :=
  ∃ cmdsp, prefix cmdsp cmds ∧
           match apply_cmds cmdsp with
           | State txnst _ => txnst !! ts = Some (Prepared wrs)
           | _ => False
           end.

Definition safe_commit (acts : list action) (cmds : list command) :=
  ∀ ts wrs, ActCmt ts wrs ∈ acts → has_prepared ts wrs cmds.

Definition has_extended ts key cmds :=
  ∃ cmdsp, prefix cmdsp cmds ∧
           match apply_cmds cmdsp with
           | State _ tpls => match tpls !! key with
                            | Some (vs, _) => (ts < length vs)%nat
                            | _ => False
                            end
           | _ => False
           end.

Definition safe_read (acts : list action) (cmds : list command) :=
  ∀ ts key, ActRead ts key ∈ acts → has_extended ts key cmds.

Definition distx_inv :=
  ∃ (db : dbmap) (txnm : gmap nat txnst) (tpls : gmap dbkey dbtpl)
    (acts_future acts_past : list action)
    (cmds_paxos : list command) (kcmts_ongoing : gmap dbkey (nat * dbval))
    (txns_cmt txns_abt : gmap nat dbmap),
    (∀ key, per_key_inv key db kcmts_ongoing txns_cmt tpls) ∧
    exclusive acts_past cmds_paxos kcmts_ongoing ∧
    repl_impl_cmtd acts_past cmds_paxos ∧
    conflict_free acts_future txns_cmt ∧
    conflict_past acts_future acts_past txns_abt ∧
    safe_commit acts_past cmds_paxos ∧
    safe_read acts_past cmds_paxos ∧
    apply_cmds cmds_paxos = State txnm tpls.

(* TODO: move to distx_action.v once stable. *)
Definition commit__kcmts_ongoing_key
  (tid: nat) (wr : option dbval) (kcmt : option (nat * dbval)) :=
  match wr with
  | Some v => Some (tid, v)
  | None => kcmt
  end.

Definition commit__kcmts_ongoing
  (tid : nat) (wrs : dbmap) (kcmts : gmap dbkey (nat * dbval)) :=
  merge (commit__kcmts_ongoing_key tid) wrs kcmts.

Definition commit__actions_past
  (tid : nat) (wrs : dbmap) (acts_past : list action) :=
  acts_past ++ [ActCmt tid wrs].
(* TODO: move to distx_action.v once stable. *)

(* TODO: move to distx_inv_proof.v once stable. *)
Theorem exclusive_inv_commit tid wrs acts_past cmds_paxos kcmts_ongoing :
  let acts_past' := commit__actions_past tid wrs acts_past in
  let kcmts_ongoing' := commit__kcmts_ongoing tid wrs kcmts_ongoing in
  repl_impl_cmtd acts_past cmds_paxos ->
  exclusive acts_past cmds_paxos kcmts_ongoing ->
  exclusive acts_past' cmds_paxos kcmts_ongoing'.
Proof.
  intros ? ? Hrlc Hexcl key.
  subst acts_past'. unfold commit__actions_past.
  subst kcmts_ongoing'. unfold commit__kcmts_ongoing.
  unfold exclusive.
  destruct (decide (key ∈ dom wrs)) as [Hin | Hnotin]; rewrite lookup_merge.
  { apply elem_of_dom in Hin as [v Hv].
    rewrite Hv /=.
    specialize (Hexcl key). unfold exclusive in Hexcl.
    split.
    { exists wrs. set_solver. }
    intros Hin.
    specialize (Hrlc _ Hin).
    admit.
  }
  { rewrite not_elem_of_dom in Hnotin.
    rewrite Hnotin /=.
    unfold exclusive in Hexcl.
    admit.
  }
Admitted.
(* TODO: move to distx_inv_proof.v once stable. *)
