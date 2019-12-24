From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Import CountableTactics.
From Perennial.go_lang Require Import lang lifting slice typing.
From Perennial.go_lang Require ffi.disk.

(* TODO: move this out, it's completely general *)
Inductive RecoverableState {state: Type} :=
| UnInit
| Closed (s:state)
| Opened (s:state)
.
Arguments RecoverableState state : clear implicits.

Instance Recoverable_inhabited state : Inhabited (RecoverableState state) := populate UnInit.

Definition ty_ := forall (val_ty:val_types), @ty val_ty.
(* TODO: slice should not require an entire ext_ty *)
Definition sliceT_ (t: ty_) : ty_ := λ val_ty, prodT (arrayT (t _)) uint64T.
Definition blockT_: ty_ := sliceT_ (λ val_ty, byteT).


Inductive LogOp :=
  | AppendOp (* log, slice of blocks *)
  | GetOp (* log, index *)
  | ResetOp (* log *)
  | InitOp (* disk size *)
  | OpenOp (* (no arguments) *)
.

Instance eq_LogOp : EqDecision LogOp.
Proof.
  solve_decision.
Defined.

Instance LogOp_fin : Countable LogOp.
Proof.
  solve_countable LogOp_rec 5%nat.
Qed.

Inductive Log_val := Log (vs:list u8).
Instance eq_Log_val : EqDecision Log_val.
Proof.
  solve_decision.
Defined.

Instance eq_Log_fin : Countable Log_val.
Proof.
  refine (inj_countable' (λ v, match v with
                               | Log vs => vs
                               end) Log _); by intros [].
Qed.

Definition log_op : ext_op.
Proof.
  refine (mkExtOp LogOp _ _ Log_val _ _).
Defined.

Inductive Log_ty := LogT.

Instance log_val_ty: val_types :=
  {| ext_tys := Log_ty; |}.

Section log.
  Existing Instances log_op log_val_ty.
  Instance log_ty: ext_types log_op :=
    {| val_tys := log_val_ty;
       val_ty_def t := match t with
                       | LogT => ExtV (Log [] : @ext_val log_op)
                       end;
       get_ext_tys (op: @external log_op) :=
         match op with
         | AppendOp => (extT LogT, sliceT_ blockT_ _)
         | GetOp => (prodT (extT LogT) uint64T, prodT (blockT_ _) boolT)
         | ResetOp => (extT LogT, unitT)
         | InitOp => (uint64T, extT LogT)
         | OpenOp => (unitT, extT LogT)
         end; |}.

  Definition log_state := RecoverableState (list disk.Block).

  Instance log_model : ffi_model.
  Proof.
    refine (mkFfiModel log_state _).
  Defined.

  (* TODO: this is really hard to write down without combinators for the heap (eg,
semantics for append needs to get a list of pointers, then load all of them as
blocks before it can append them to the log state) *)
  Inductive log_step : LogOp -> val -> state -> val -> state -> Prop :=
  | GetOpS : forall (a: u64) (b: disk.Block) (σ: state) (log: list disk.Block) l',
      σ.(world) = Opened log ->
      log !! int.nat a = Some b ->
      (forall (i:Z), 0 <= i -> i < 4096 -> σ.(heap) !! (l' +ₗ i) = None)%Z ->
      log_step GetOp (LitV (LitInt a)) σ (LitV (LitLoc l'))
               (state_insert_list l' (disk.Block_to_vals b) σ)
  .

  Instance log_semantics : ext_semantics log_op log_model :=
    {| ext_step := log_step;
       ext_crash := eq; |}.
End log.
