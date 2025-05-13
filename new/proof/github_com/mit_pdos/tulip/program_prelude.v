From New.proof Require Export grove_prelude.
From Perennial.program_logic Require Export atomic. (* prefer the ncfupd atomics *)
From Perennial.program_logic Require Export own_crash_inv. (* import [own_crash_ex] *)
From Perennial.goose_lang.lib Require Import persistent_readonly.
From Perennial.goose_lang Require Import ipersist.
From Perennial.program_proof.rsm Require Export big_sep.
From Perennial.program_proof.rsm.pure Require Export
  dual_lookup extend fin_maps fin_maps_list fin_sets largest_before list misc nat
  nonexpanding_merge sets vslice word quorum.
(* FIXME: it's a bad idea to export below for names can collide *)
From New.generatedproof.github_com.mit_pdos.tulip Require Export
  index params tulip tuple util.
(* note being translated yet *)
(*
From New.generatedproof.github_com.mit_pdos.tulip Require Export
  backup gcoord quorum replica txn txnlog message.
*)
From New.proof.github_com.mit_pdos.tulip.pure Require Export
  action cmd encode res msg inv inv_txnlog stability base.

#[global]
Instance dbval_to_val : IntoVal dbval :=
  { to_val_def v := #(dbval_to_t v); }.

#[global]
Program Instance dbval_into_val_typed : IntoValTyped dbval tulip.Value :=
  { default_val := None; }.
Next Obligation. solve_to_val_type. Qed.
Next Obligation.
  solve_zero_val.
  rewrite /dbval_to_t /=.
  rewrite [in lhs in lhs = _]to_val_unseal /=.
  rewrite struct.val_aux_unseal !zero_val_eq //.
Qed.
Final Obligation. solve_to_val_inj. Qed.

(*
Definition dbval_from_val (v : val) : option dbval :=
  match v with
  | (#(LitBool b), (#(LitString s), #()))%V => if b then Some (Some s) else Some None
  | _ => None
  end.
*)

#[global]
Instance dbmod_to_val : IntoVal dbmod :=
  { to_val_def x := #(dbmod_to_t x); }.

(*
Definition dbmod_from_val (v : val) : option dbmod :=
  match v with
  | (#(LitString k), (dbv, #()))%V => match dbval_from_val dbv with
                                     | Some x => Some (k, x)
                                     | _ => None
                                     end
  | _ => None
  end.
*)

#[global]
Instance ppsl_to_val : IntoVal ppsl :=
  { to_val_def x := #(ppsl_to_t x); }.

(*
Definition ppsl_to_val (v : ppsl) : val := (#v.1, (#v.2, #())).

Definition ppsl_from_val (v : val) : option ppsl :=
  match v with
  | (#(LitInt n), (#(LitBool b), #()))%V => Some (n, b)
  | _ => None
  end.

#[global]
Instance ppsl_into_val : IntoVal ppsl.
Proof.
  refine {|
      to_val := ppsl_to_val;
      from_val := ppsl_from_val;
      IntoVal_def := (W64 0, false);
    |}.
  intros v.
  by destruct v.
Defined.

#[global]
Instance ppsl_into_val_for_type :
  IntoValForType ppsl (uint64T * (boolT * unitT)%ht).
Proof. by constructor; [| | intros [r d]; auto 10]. Defined.
*)

Definition ppsl_to_nat_bool (psl : ppsl) := (uint.nat psl.1, psl.2).
Definition ppsl_to_nat_bool' (psl : tulip.PrepareProposal.t) := (uint.nat (tulip.PrepareProposal.Rank' psl), (tulip.PrepareProposal.Prepared' psl)).

(*
Definition dbpver_to_val (x : u64 * dbval) : val := (#x.1, (dbval_to_val x.2, #())).

Definition dbpver_from_val (v : val) : option dbpver :=
  match v with
  | (#(LitInt n), (dbv, #()))%V => match dbval_from_val dbv with
                                  | Some x => Some (n, x)
                                  | _ => None
                                  end
  | _ => None
  end.

#[global]
Instance dbpver_into_val : IntoVal dbpver.
Proof.
  refine {|
      to_val := dbpver_to_val;
      from_val := dbpver_from_val;
      IntoVal_def := (W64 0, None);
    |}.
  intros [n v].
  by destruct v.
Defined.

#[global]
Instance dbpver_into_val_for_type :
  IntoValForType dbpver (uint64T * (boolT * (stringT * unitT) * unitT)%ht).
Proof.
  constructor; [done | done |].
  intros [t [v |]]; by auto 10.
Defined.
*)

(*
Definition coordid_to_val (v : coordid) : val := (#v.1, (#v.2, #())).

Definition coordid_from_val (v : val) : option coordid :=
  match v with
  | (#(LitInt g), (#(LitInt r), #()))%V => Some (g, r)
  | _ => None
  end.

#[global]
Instance coordid_into_val : IntoVal coordid.
Proof.
  refine {|
      to_val := coordid_to_val;
      from_val := coordid_from_val;
      IntoVal_def := (W64 0, W64 0);
    |}.
  intros v.
  by destruct v.
Defined.

#[global]
Instance coordid_into_val_for_type :
  IntoValForType coordid (uint64T * (uint64T * unitT)%ht).
Proof. by constructor; [| | intros [r d]; auto 10]. Defined.

Definition ccommand_to_val (pwrsS : Slice.t) (c : ccommand) : val :=
  match c with
  | CmdAbort ts => (#(U64 0), (#(U64 ts), (Slice.nil, #())))
  | CmdCommit ts _ => (#(U64 1), (#(U64 ts), (to_val pwrsS,  #())))
  end.
*)

Inductive txnphase :=
| TxnPrepared
| TxnCommitted
| TxnAborted.

#[global]
Instance txnphase_eq_decision :
  EqDecision txnphase.
Proof. solve_decision. Qed.

Definition txnphase_to_u64 (p : txnphase) :=
  match p with
  | TxnPrepared => (U64 0)
  | TxnCommitted => (U64 1)
  | TxnAborted => (U64 2)
  end.

#[global]
Instance txnphase_to_u64_inj :
  Inj eq eq txnphase_to_u64.
Proof. intros x y H. by destruct x, y. Defined.

Section def.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition own_dbmap_in_slice s (m : dbmap) : iProp Σ :=
    ∃ l : list dbmod,
      own_slice s (DfracOwn 1) (dbmod_to_t <$> l) ∗ ⌜map_to_list m ≡ₚ l⌝.

  Definition own_dbmap_in_slice_frac s (m : dbmap) : iProp Σ :=
    ∃ (l : list dbmod) (q : dfrac),
      own_slice s q (dbmod_to_t <$> l) ∗
      ⌜map_to_list m ≡ₚ l⌝.

  Definition is_dbmap_in_slice s (m : dbmap) : iProp Σ :=
    ∃ l : list dbmod,
      (* NOTE: changed from a readonly *)
      own_slice s DfracDiscarded (dbmod_to_t <$> l) ∗
      ⌜map_to_list m ≡ₚ l⌝.

  #[global]
  Instance is_dbmap_in_slice_persistent s m :
    Persistent (is_dbmap_in_slice s m).
  Proof. apply _. Defined.

  (* TODO: no longer needs a fupd *)
  Lemma is_dbmap_in_slice_unpersist s m E :
    is_dbmap_in_slice s m ={E}=∗
    own_dbmap_in_slice_frac s m.
  Proof.
    iIntros "Hm".
    iModIntro.
    iDestruct "Hm" as (l) "[Hl %Hl]".
    iFrame.
    done.
  Qed.

  #[global] Instance own_dbmap_in_slice_persist_inst s m :
    UpdateIntoPersistently (own_dbmap_in_slice s m) (is_dbmap_in_slice s m).
  Proof.
    red.
    iIntros "Hm".
    iDestruct "Hm" as (l) "[Hl %Hl]".
    iPersist "Hl".
    iFrame "Hl".
    done.
  Qed.

  Lemma own_dbmap_in_slice_persist s m E :
    own_dbmap_in_slice s m ={E}=∗
    is_dbmap_in_slice s m.
  Proof.
    iIntros "Hm".
    iPersist "Hm".
    done.
  Qed.

  Definition is_txnptgs_in_slice s (g : txnptgs) : iProp Σ :=
    ∃ l : list u64,
      own_slice s DfracDiscarded l ∗
      ⌜list_to_set l = g⌝ ∗
      ⌜NoDup l⌝.

  #[global]
  Instance is_txnptgs_in_slice_persistent s g :
    Persistent (is_txnptgs_in_slice s g).
  Proof. apply _. Defined.

  Definition own_pwrs_slice (pwrsS : slice.t) (c : ccommand) : iProp Σ :=
    match c with
    | CmdCommit _ pwrs => own_dbmap_in_slice pwrsS pwrs
    | _ => True
    end.

  Definition safe_group_txnphase γ ts gid (phase : txnphase) : iProp Σ :=
    match phase with
    | TxnPrepared => quorum_prepared γ gid ts ∗ quorum_validated γ gid ts
    | TxnCommitted => ∃ wrs, is_txn_committed γ ts wrs
    | TxnAborted => is_txn_aborted γ ts ∨ quorum_unprepared γ gid ts
    end.

  #[global]
  Instance safe_group_txnphase_persistent γ ts gid phase :
    Persistent (safe_group_txnphase γ ts gid phase).
  Proof. destruct phase; apply _. Defined.

  Definition safe_txnphase γ ts (phase : txnphase) : iProp Σ :=
    match phase with
    | TxnPrepared => (∃ wrs, all_prepared γ ts wrs)
    | TxnCommitted => (∃ wrs, is_txn_committed γ ts wrs)
    | TxnAborted => is_txn_aborted γ ts
    end.

  #[global]
  Instance safe_txnphase_persistent γ ts phase :
    Persistent (safe_txnphase γ ts phase).
  Proof. destruct phase; apply _. Defined.

End def.
