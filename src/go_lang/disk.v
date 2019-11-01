From stdpp Require Import gmap.
From stdpp Require Import vector.
From Perennial.go_lang Require Import lang.

Inductive DiskOp := Read | Write.
Instance eq_DiskOp : EqDecision DiskOp.
Proof.
  intros x y; hnf; decide equality.
Defined.

Definition disk_op : ext_op.
Proof.
  refine (mkExtOp DiskOp _ _).
  apply (countable.inj_countable
           (fun op => match op with
                   | Read => 0
                   | Write => 1
                   end)
           (fun n => match n with
                  | 0 => Some Read
                  | 1 => Some Write
                  | _ => None
                  end)).
  destruct x; auto.
Defined.

Definition block_bytes: nat := N.to_nat 4096.
Definition Block := vec byte block_bytes.

Definition disk_state := gmap u64 Block.

Definition disk_model : ffi_model.
Proof.
  refine (mkFfiModel disk_state _).
Defined.

Definition Block_to_vals {ext: ext_op} (bl:Block) : list val :=
  map (λ b, LitV (LitByte b)) (vec_to_list bl).

Section semantics.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the disk model *)
  Existing Instances disk_op disk_model.

  Definition state_insert_block (l: loc) (b: Block) (σ: state): state :=
    state_upd_heap (λ h, heap_array l (Block_to_vals b) ∪ h) σ.

  Inductive ext_step : DiskOp -> val -> state -> val -> state -> Prop :=
  | ReadS : forall (a: u64) (b: Block) (σ: state) l',
      σ.(world) !! a = Some b ->
      (forall (i:Z), 0 <= i -> i < 4096 -> σ.(heap) !! (l' +ₗ i) = None)%Z ->
      ext_step Read (LitV (LitInt a)) σ (LitV (LitLoc l'))
               (state_insert_block l' b σ)
  | WriteS : forall (a: u64) (l: loc) (b0 b: Block) (σ: state),
      σ.(world) !! a = Some b0 ->
      (forall (i:Z), 0 <= i -> i < 4096 ->
                σ.(heap) !! (l +ₗ i) =
                Block_to_vals b !! Z.to_nat i)%Z ->
      ext_step Write (PairV (LitV (LitInt a)) (LitV (LitLoc l))) σ
               (LitV LitUnit) (state_upd_world <[ a := b ]> σ)

  .

End semantics.
