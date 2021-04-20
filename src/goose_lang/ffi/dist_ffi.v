(** FFI module for distributed Perennial (Grove): network *)
From stdpp Require Import gmap vector fin_maps.
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

(** * The Grove extension to GooseLang: primitive operations [Trusted definitions!] *)

Inductive GroveOp := MkSendOp | MkRecvOp | SendOp | RecvOp.
Instance eq_GroveOp : EqDecision GroveOp.
Proof. solve_decision. Defined.
Instance GroveOp_fin : Countable GroveOp.
Proof. solve_countable GroveOp_rec 10%nat. Qed.

Inductive GroveEndpoint := SendEndp | RecvEndp.
Instance eq_GroveEndpoint : EqDecision GroveEndpoint.
Proof. solve_decision. Defined.
Instance GroveEndpoint_fin : Countable GroveEndpoint.
Proof. solve_countable GroveEndpoint_rec 10%nat. Qed.
Definition GroveVal : Set := GroveEndpoint * string.

Definition grove_op : ext_op.
Proof.
  refine (mkExtOp GroveOp _ _ GroveVal _ _).
Defined.

Inductive GroveTys := GroveSendTy | GroveRecvTy.

(* TODO: Why is this an instance but the ones above are not? *)
Instance grove_val_ty: val_types :=
  {| ext_tys := GroveTys; |}.

(** The global network state: a map from endpoint names to the set of messages sent to
those endpoints. *)
Definition endpoint := string.
Definition message := list u8.
Definition grove_global_state := gmap endpoint (gset message).

Definition grove_model : ffi_model.
Proof.
  refine (mkFfiModel () grove_global_state _ _).
Defined.

(** Initial state where the endpoints exist but have not received any messages yet. *)
Definition init_grove (endpoints : list endpoint) : grove_global_state :=
  gset_to_gmap ∅ (list_to_set endpoints).

Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the disk model *)
  Existing Instances grove_op grove_model.

  Existing Instances r_mbind r_fmap.

  Definition ext_step (op: GroveOp) (v: val): transition (state*global_state) val :=
    match op, v with
    | MkSendOp, LitV (LitString s) =>
      ret (ExtV (SendEndp, s))
    | MkRecvOp, LitV (LitString s) =>
      ret (ExtV (RecvEndp, s))
    | SendOp, PairV (ExtV (SendEndp, e)) (PairV (LitV (LitLoc l)) (LitV (LitInt len))) =>
      m ← suchThat (gen:=fun _ _ => None) (λ '(σ,g) (m : vec u8 (int.nat len)),
            forall (i:Z), 0 <= i -> i < (int.Z len) ->
                match σ.(heap) !! (l +ₗ i) with
                | Some (Reading _, LitV (LitByte v)) => (vec_to_list m) !! Z.to_nat i = Some v
                | _ => False
                end);
      ms ← reads (λ '(σ,g), g !! e) ≫= unwrap;
      modify (λ '(σ,g), (σ, <[ e := ms ∪ {[vec_to_list m]} ]> g));;
      ret #()
    | RecvOp, ExtV (RecvEndp, e) =>
      ms ← reads (λ '(σ,g), g !! e) ≫= unwrap;
      m ← suchThat (gen:=fun _ _ => None) (λ _ (m : option message),
            m = None ∨ ∃ m', m = Some m' ∧ m' ∈ ms);
      match m with
      | None => ret (#false, (#locations.null, #0))%V
      | Some m =>
        l ← allocateN (length m);
        modify (λ '(σ,g), (state_insert_list l ((λ b, #(LitByte b)) <$> m) σ, g));;
        ret  (#true, (#(l : loc), #(length m)))%V
      end
    | _, _ => undefined
    end.

  (* these instances are also local (to the outer section) *)
  Instance grove_semantics : ext_semantics grove_op grove_model :=
    { ext_step := ext_step;
      ext_crash := eq; }.
End grove.

(** * Grove semantic interpretation and invariant *)

(** * Grove user-facing operations and their specs *)
Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the disk model *)
  Existing Instances grove_op grove_model.

  (** We only use these types behind a ptr indirection so their size should not matter. *)
  Definition Sender : ty := extT GroveSendTy.
  Definition Receiver : ty := extT GroveRecvTy.

  (** Type: func(string) *Sender *)
  Definition MakeSender : val :=
    λ: "e", ExternalOp MkSendOp (Var "e").

  (** Type: func(string) *Receiver *)
  Definition MakeReceiver : val :=
    λ: "e", ExternalOp MkSendOp (Var "e").

  (** Type: func( *Sender, []byte) *)
  Definition Send : val :=
    (* FIXME: extract ptr and len from "m" (which is intended to have type []byte) *)
    λ: "e" "m", ExternalOp SendOp (Var "e", Var "m").

  (** Type: func( *Receiver) []byte *)
  Definition Receive : val :=
    λ: "e",
      let: "m" := ExternalOp RecvOp (Var "e") in
      let: "slice" := Snd (Var "m") in
      let: "ptr" := Fst (Var "ptr") in
      let: "len" := Snd (Var "ptr") in
      (* FIXME: package "ptr" and "len" to returned slice of type []byte *)
      (Fst (Var "m"), Var "slice").
End grove.
