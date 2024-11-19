From Perennial.program_proof.tulip Require Export prelude.
From Goose.github_com.mit_pdos.tulip Require Export
  backup gcoord index params quorum replica tulip tuple txn txnlog util.

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
Proof. constructor; [done | done | intros [v |]; by auto]. Defined.

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

Definition u64_dbval_to_val (x : u64 * dbval) : val := (#x.1, (dbval_to_val x.2, #())).

Definition u64_dbval_from_val (v : val) : option (u64 * dbval) :=
  match v with
  | (#(LitInt n), (dbv, #()))%V => match dbval_from_val dbv with
                                  | Some x => Some (n, x)
                                  | _ => None
                                  end
  | _ => None
  end.

#[global]
Instance u64_dbval_into_val : IntoVal (u64 * dbval).
Proof.
  refine {|
      to_val := u64_dbval_to_val;
      from_val := u64_dbval_from_val;
      IntoVal_def := (W64 0, None);
    |}.
  intros [n v].
  by destruct v.
Defined.

#[global]
Instance u64_dbval_into_val_for_type :
  IntoValForType (u64 * dbval) (uint64T * (boolT * (stringT * unitT) * unitT)%ht).
Proof.
  constructor; [done | done |].
  intros [t [v |]]; by auto 10.
Defined.

Definition ccommand_to_val (pwrsS : Slice.t) (c : ccommand) : val :=
  match c with
  | CmdCommit ts _ => (#(U64 1), (#(U64 ts), (to_val pwrsS, (zero_val stringT, #()))))
  | CmdAbort ts => (#(U64 2), (#(U64 ts), (Slice.nil, (zero_val stringT, #()))))
  end.

Section def.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition own_dbmap_in_slice s (l : list dbmod) (m : dbmap) : iProp Σ :=
    own_slice s (struct.t WriteEntry) (DfracOwn 1) l ∗ ⌜map_to_list m = l⌝.

End def.
