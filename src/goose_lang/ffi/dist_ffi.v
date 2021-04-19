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
    | SendOp, PairV (ExtV (SendEndp, s)) (PairV (LitV (LitLoc l)) (LitV (LitInt len))) =>
      m ← suchThat (gen:=fun _ _ => None) (λ '(σ,g) (m : vec u8 (int.nat len)),
            forall (i:Z), 0 <= i -> i < (int.Z len) ->
                match σ.(heap) !! (l +ₗ i) with
                | Some (Reading _, LitV (LitByte v)) => (vec_to_list m) !! Z.to_nat i = Some v
                | _ => False
                end);
      ms ← reads (λ '(σ,g), g !! s) ≫= unwrap;
      modify (λ '(σ,g), (σ, <[ s := ms ∪ {[vec_to_list m]} ]> g));;
      ret #()
    | RecvOp, ExtV (RecvEndp, s) =>
      ms ← reads (λ '(σ,g), g !! s) ≫= unwrap;
      m ← suchThat (gen:=fun _ _ => None) (λ _ (m : option message),
            m = None ∨ ∃ m', m = Some m' ∧ m' ∈ ms);
      match m with
      | None => ret (#false, #locations.null)%V
      | Some m =>
        l ← allocateN (length m);
        modify (λ '(σ,g), (state_insert_list l ((λ b, #(LitByte b)) <$> m) σ, g));;
        ret  (#true, #(l : loc))%V
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
