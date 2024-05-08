From stdpp Require Import gmap.
From stdpp Require Import vector fin_maps.
From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import numbers.
From Perennial.algebra Require Import gen_heap_names.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Import ectx_lifting.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import lang lifting slice typing.
From Perennial.goose_lang Require Import crash_modality.

Set Default Proof Using "Type".
(* this is purely cosmetic but it makes printing line up with how the code is
usually written *)
Set Printing Projections.

Inductive DiskOp : Set := ReadOp | WriteOp | SizeOp | BarrierOp.
#[global]
Instance eq_DiskOp : EqDecision DiskOp.
Proof.
  solve_decision.
Defined.

#[global]
Instance DiskOp_fin : Countable DiskOp.
Proof.
  solve_countable DiskOp_rec 4%nat.
Qed.

Definition disk_op : ffi_syntax.
Proof.
  refine (mkExtOp DiskOp _ _ () _ _).
Defined.

Inductive Disk_ty := | DiskInterfaceTy.

#[global]
Instance disk_val_ty: val_types :=
  {| ext_tys := Disk_ty; |}.

Section disk.
  Existing Instances disk_op disk_val_ty.

  Inductive disk_ext_tys : @val disk_op -> (ty * ty) -> Prop :=
  | DiskOpType op :
      disk_ext_tys (λ: "v", ExternalOp op (Var "v"))%V
                   (match op with
                   | ReadOp => (uint64T, arrayT byteT)
                   | WriteOp => (prodT uint64T (arrayT byteT), unitT)
                   | SizeOp => (unitT, uint64T)
                   | BarrierOp => (unitT, unitT)
                   end).

  Definition disk_ty: ext_types disk_op :=
    {| val_tys := disk_val_ty;
       get_ext_tys := disk_ext_tys |}.
  Definition Disk: ty := extT DiskInterfaceTy.
End disk.

Definition block_bytes: nat := Z.to_nat 4096.
Definition BlockSize {ext: ffi_syntax}: val := #4096.
Definition Block := vec byte block_bytes.
Definition blockT `{ext_tys:ext_types}: @ty val_tys := slice.T byteT.
(* TODO: could use vreplicate; not sure how much easier it is to work with *)
Definition block0 : Block := list_to_vec (replicate (Z.to_nat 4096) (I8 0)).


Lemma block_bytes_eq : block_bytes = Z.to_nat 4096.
Proof. reflexivity. Qed.

Global Instance Block0: Inhabited Block := _.
Global Instance Block_countable : Countable Block := _.

Definition Block_to_vals {ext: ffi_syntax} (bl:Block) : list val :=
  fmap b2val (vec_to_list bl).
