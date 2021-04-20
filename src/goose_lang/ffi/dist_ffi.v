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
  suddenly cause all FFI parameters to be inferred as the grove model *)
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

  Local Instance grove_semantics : ext_semantics grove_op grove_model :=
    { ext_step := ext_step;
      ext_crash := eq; }.
End grove.

(** * Grove semantic interpretation and lifting lemmas *)
Class groveG Σ :=
  { groveG_gen_heapG :> gen_heap.gen_heapG endpoint (gset message) Σ; }.

Class grove_preG Σ :=
  { grove_preG_gen_heapG :> gen_heap.gen_heapPreG endpoint (gset message) Σ; }.

Definition groveΣ : gFunctors :=
  #[gen_heapΣ endpoint (gset message)].

Instance subG_groveG Σ : subG groveΣ Σ → grove_preG Σ.
Proof. solve_inG. Qed.

Definition grove_update_pre {Σ} (dG: grove_preG Σ) (n: gen_heap_names) :=
  {| groveG_gen_heapG := gen_heapG_update_pre (@grove_preG_gen_heapG _ dG) n |}.

Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
  Existing Instances grove_op grove_model.

  Local Program Instance grove_interp: ffi_interp grove_model :=
    {| ffiG := groveG;
       ffi_local_names := unit;
       ffi_global_names := gen_heap_names;
       ffi_get_local_names _ hD := tt;
       ffi_get_global_names _ hD := gen_heapG_get_names (groveG_gen_heapG);
       ffi_update_local  _ hD names := hD;
       ffi_ctx _ _ _ := True%I;
       ffi_global_ctx _ _ _ := True%I;
       ffi_local_start := fun _ _ _ (g: grove_global_state) =>
                      ([∗ map] e↦ms ∈ g, (gen_heap.mapsto (L:=endpoint) (V:=gset message) e (DfracOwn 1) ms))%I;
       ffi_restart _ _ _ := True%I;
       ffi_crash_rel Σ hF1 σ1 hF2 σ2 := True%I;
    |}.
  Next Obligation. intros ? [[]] [] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
End grove.

Notation "e c↦ ms" := (mapsto (L:=endpoint) (V:=gset message) e (DfracOwn 1) ms)
                       (at level 20, format "e  c↦  ms") : bi_scope.


Section lifting.
  Existing Instances grove_op grove_model grove_semantics grove_interp.
  Context `{!heapG Σ}.
  (*Instance groveG0 : groveG Σ := heapG_ffiG.*)

  Definition send_endpoint (e : string) : val :=
    ExtV (SendEndp, e).
  Definition recv_endpoint (e : string) : val :=
    ExtV (RecvEndp, e).

  (* Lifting automation *)
  Local Hint Extern 0 (head_reducible _ _ _) => eexists _, _, _, _, _; simpl : core.
  Local Hint Extern 0 (head_reducible_no_obs _ _ _) => eexists _, _, _, _; simpl : core.
  (** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
  Ltac inv_head_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : head_step_atomic _ _ _ _ _ _ _ _ |- _ =>
          apply head_step_atomic_inv in H; [ | by inversion 1 ]
        | H : head_step ?e _ _ _ _ _ _ _ |- _ =>
          try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
          inversion H; subst; clear H
        | H : ext_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        end.

  Lemma wp_MkSendOp e s E :
    {{{ True }}}
      ExternalOp MkSendOp (Val $ LitV $ LitString e) @ s; E
    {{{ RET send_endpoint e; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /head_step/=.
      monad_simpl. }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    inv_head_step.
    monad_inv.
    simpl.
    iFrame.
    iIntros "!>".
    iSplit; first done.
    by iApply "HΦ".
  Qed.

  Lemma wp_MkRecvOp e s E :
    {{{ True }}}
      ExternalOp MkRecvOp (Val $ LitV $ LitString e) @ s; E
    {{{ RET recv_endpoint e; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /head_step/=.
      monad_simpl. }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    inv_head_step.
    monad_inv.
    simpl.
    iFrame.
    iIntros "!>".
    iSplit; first done.
    by iApply "HΦ".
  Qed.

End lifting.

(** * Grove user-facing operations and their specs *)
Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
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
