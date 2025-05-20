From Perennial.program_proof.tulip Require Export prelude.
(* FIXME: it's a bad idea to export below for names can collide *)
From Goose.github_com.mit_pdos.tulip Require Export
  backup gcoord index params quorum replica tulip tuple txn txnlog util message.

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

#[global]
Instance dbval_into_val : IntoVal dbval.
Proof.
  refine {|
      to_val := dbval_to_val;
      from_val := dbval_from_val;
      IntoVal_def := None;
    |}.
  intros v.
  by destruct v.
Defined.

#[global]
Instance dbval_into_val_for_type : IntoValForType dbval (boolT * (stringT * unitT)%ht).
Proof. by constructor; [| | intros [v |]; auto]. Defined.

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
      IntoVal_def := (""%go, None);
    |}.
  intros [k v].
  by destruct v.
Defined.

#[global]
Instance dbmod_into_val_for_type :
  IntoValForType dbmod (stringT * (boolT * (stringT * unitT) * unitT)%ht).
Proof. by constructor; [| | intros [k [s |]]; auto 10]. Defined.

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

Definition ppsl_to_nat_bool (psl : ppsl) := (uint.nat psl.1, psl.2).

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
      own_slice s (struct.t WriteEntry) (DfracOwn 1) l ∗ ⌜map_to_list m ≡ₚ l⌝.

  Definition own_dbmap_in_slice_frac s (m : dbmap) : iProp Σ :=
    ∃ (l : list dbmod) (q : dfrac),
      own_slice_small s (struct.t WriteEntry) q l ∗
      ⌜map_to_list m ≡ₚ l⌝.

  Definition is_dbmap_in_slice s (m : dbmap) : iProp Σ :=
    ∃ l : list dbmod,
      readonly (own_slice_small s (struct.t WriteEntry) (DfracOwn 1) l) ∗
      ⌜map_to_list m ≡ₚ l⌝.

  #[global]
  Instance is_dbmap_in_slice_persistent s m :
    Persistent (is_dbmap_in_slice s m).
  Proof. apply _. Defined.

  Lemma is_dbmap_in_slice_unpersist s m E :
    is_dbmap_in_slice s m ={E}=∗
    own_dbmap_in_slice_frac s m.
  Proof.
    iIntros "Hm".
    iDestruct "Hm" as (l) "[Hl %Hl]".
    iMod (readonly_load with "Hl") as (q) "Hl".
    by iFrame "∗ %".
  Qed.

  Lemma own_dbmap_in_slice_persist s m E :
    own_dbmap_in_slice s m ={E}=∗
    is_dbmap_in_slice s m.
  Proof.
    iIntros "Hm".
    iDestruct "Hm" as (l) "[Hl %Hl]".
    iDestruct (own_slice_to_small with "Hl") as "Hl".
    iMod (readonly_alloc_1 with "Hl") as "Hl".
    by iFrame "∗ %".
  Qed.

  Definition is_txnptgs_in_slice s (g : txnptgs) : iProp Σ :=
    ∃ l : list u64,
      own_slice_small s uint64T DfracDiscarded l ∗
      ⌜list_to_set l = g⌝ ∗
      ⌜NoDup l⌝.

  #[global]
  Instance is_txnptgs_in_slice_persistent s g :
    Persistent (is_txnptgs_in_slice s g).
  Proof. apply _. Defined.

  Definition own_pwrs_slice (pwrsS : Slice.t) (c : ccommand) : iProp Σ :=
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
