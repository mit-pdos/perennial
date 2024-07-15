From stdpp Require Import gmap.
From stdpp Require Import vector fin_maps.
From RecordUpdate Require Import RecordUpdate.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import lang typing notation.
From Perennial.goose_lang.lib Require Import slice.

Set Default Proof Using "Type".
Set Printing Projections.

Inductive DiskOp : Set := ReadOp | WriteOp | SizeOp.
#[global]
Instance eq_DiskOp : EqDecision DiskOp.
Proof.
  solve_decision.
Defined.

#[global]
Instance DiskOp_fin : Countable DiskOp.
Proof.
  solve_countable DiskOp_rec 3%nat.
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
Definition block0 : Block := list_to_vec (replicate (Z.to_nat 4096) (W8 0)).


Lemma block_bytes_eq : block_bytes = Z.to_nat 4096.
Proof. reflexivity. Qed.

Global Instance Block0: Inhabited Block := _.
Global Instance Block_countable : Countable Block := _.

Definition disk_state := gmap Z Block.

Definition disk_model : ffi_model.
Proof.
  refine (mkFfiModel disk_state () _ _).
Defined.

Fixpoint init_disk (d: disk_state) (sz: nat) : disk_state :=
  match sz with
  | O => d
  | S n => <[(Z.of_nat n) := block0]> (init_disk d n)
  end.

Definition Block_to_vals {ext: ffi_syntax} (bl:Block) : list val :=
  b2val <$> vec_to_list bl.

Lemma length_Block_to_vals {ext: ffi_syntax} b :
    length (Block_to_vals b) = block_bytes.
Proof.
  rewrite /Block_to_vals fmap_length vec_to_list_length //.
Qed.

Lemma replicate_zero_to_block0 `{ext_ty: ext_types} :
  replicate (uint.nat 4096) (zero_val byteT) =
  Block_to_vals block0.
Proof. reflexivity. Qed.

Section disk.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the disk model *)
  Existing Instances disk_op disk_model disk_ty.

  Definition disk_val (d : ()) : val := ExtV d.

  Definition Get: val :=
    λ: <>, disk_val ().

  Definition Read: val :=
    λ: "a",
    let: "p" := ExternalOp ReadOp (Var "a") in
    raw_slice byteT (Var "p") #4096.

  Definition ReadTo: val :=
    λ: "a" "buf",
    let: "p" := ExternalOp ReadOp (Var "a") in
    MemCpy_rec byteT (slice.ptr (Var "buf")) (Var "p") #4096.

  Definition Write: val :=
    λ: "a" "b",
    ExternalOp WriteOp (Var "a", slice.ptr (Var "b")).

  Definition Barrier: val :=
    λ: <>, #().

  Definition Size: val :=
    λ: "v",
       ExternalOp SizeOp (Var "v").

  Existing Instances r_mbind r_fmap.

  Definition highest_addr (addrs: gset Z): Z :=
    set_fold (λ k r, k `max` r)%Z 0%Z addrs.

  Definition disk_size (d: gmap Z Block): Z :=
    1 + highest_addr (dom d).

  Definition ffi_step (op: DiskOp) (v: val): transition (state*global_state) expr :=
    match op, v with
    | ReadOp, LitV (LitInt a) =>
      b ← reads (λ '(σ,g), σ.(world) !! uint.Z a) ≫= unwrap;
      l ← allocateN;
      modify (λ '(σ,g), (state_insert_list l (Block_to_vals b) σ, g));;
      ret $ Val $ #(LitLoc l)
    | WriteOp, PairV (LitV (LitInt a)) (LitV (LitLoc l)) =>
      _ ← reads (λ '(σ,g), σ.(world) !! uint.Z a) ≫= unwrap;
        (* TODO: use Sydney's executable version from disk_interpreter.v as
        the generator here *)
      b ← suchThat (gen:=fun _ _ => None) (λ '(σ,g) b, (forall (i:Z), 0 <= i -> i < 4096 ->
                match σ.(heap) !! (l +ₗ i) with
                | Some (Reading _, v) => Block_to_vals b !! Z.to_nat i = Some v
                | _ => False
                end));
      modify (λ '(σ,g), (set world <[ uint.Z a := b ]> σ, g));;
      ret $ Val $ #()
    | SizeOp, LitV LitUnit =>
      sz ← reads (λ '(σ,g), disk_size σ.(world));
      ret $ Val $ LitV $ LitInt (word.of_Z sz)
    | _, _ => undefined
    end.

  Instance disk_semantics : ffi_semantics disk_op disk_model :=
    { ffi_step := ffi_step;
      ffi_crash_step := eq; }.

End disk.
