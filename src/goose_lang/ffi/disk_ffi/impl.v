From stdpp Require Import gmap.
From stdpp Require Import vector fin_maps.
From RecordUpdate Require Import RecordUpdate.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import lang notation.

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

Definition block_bytes: Z := 4096.
Definition BlockSize {ext: ffi_syntax}: val := #4096.
Definition Block := vec byte (Z.to_nat block_bytes).
(* TODO: could use vreplicate; not sure how much easier it is to work with *)
Definition block0 : Block := list_to_vec (replicate (Z.to_nat block_bytes) (W8 0)).

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
    Z.of_nat $ length (Block_to_vals b) = block_bytes.
Proof.
  rewrite /Block_to_vals length_fmap length_vec_to_list //.
Qed.

Section disk.

  Existing Instances disk_op disk_model.
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
