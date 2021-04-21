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
Definition chan := string.
Definition message := list u8.
Definition grove_global_state := gmap chan (gset message).

Definition grove_model : ffi_model.
Proof.
  refine (mkFfiModel () grove_global_state _ _).
Defined.

(** Initial state where the endpoints exist but have not received any messages yet. *)
Definition init_grove (channels : list chan) : grove_global_state :=
  gset_to_gmap ∅ (list_to_set channels).

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
    | SendOp, PairV (ExtV (SendEndp, c)) (PairV (LitV (LitLoc l)) (LitV (LitInt len))) =>
      m ← suchThat (gen:=fun _ _ => None) (λ '(σ,g) (m : message),
            length m = int.nat len ∧ forall (i:Z), 0 <= i -> i < length m ->
                match σ.(heap) !! (l +ₗ i) with
                | Some (Reading _, LitV (LitByte v)) => m !! Z.to_nat i = Some v
                | _ => False
                end);
      ms ← reads (λ '(σ,g), g !! c) ≫= unwrap;
      modify (λ '(σ,g), (σ, <[ c := ms ∪ {[m]} ]> g));;
      ret #()
    | RecvOp, ExtV (RecvEndp, c) =>
      ms ← reads (λ '(σ,g), g !! c) ≫= unwrap;
      m ← suchThat (gen:=fun _ _ => None) (λ _ (m : option message),
            m = None ∨ ∃ m', m = Some m' ∧ m' ∈ ms);
      match m with
      | None => ret (#true, (#locations.null, #0))%V
      | Some m =>
        l ← allocateN;
        modify (λ '(σ,g), (state_insert_list l ((λ b, #(LitByte b)) <$> m) σ, g));;
        ret  (#false, (#(l : loc), #(length m)))%V
      end
    | _, _ => undefined
    end.

  Local Instance grove_semantics : ext_semantics grove_op grove_model :=
    { ext_step := ext_step;
      ext_crash := eq; }.
End grove.

(** * Grove semantic interpretation and lifting lemmas *)
Class groveG Σ :=
  { groveG_gen_heapG :> gen_heap.gen_heapG chan (gset message) Σ; }.

Class grove_preG Σ :=
  { grove_preG_gen_heapG :> gen_heap.gen_heapPreG chan (gset message) Σ; }.

Definition groveΣ : gFunctors :=
  #[gen_heapΣ chan (gset message)].

Instance subG_groveG Σ : subG groveΣ Σ → grove_preG Σ.
Proof. solve_inG. Qed.

Definition grove_update_pre {Σ} (dG: grove_preG Σ) (n: gen_heap_names) :=
  {| groveG_gen_heapG := gen_heapG_update_pre (@grove_preG_gen_heapG _ dG) n |}.

Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
  Existing Instances grove_op grove_model.

  Local Definition chan_msg_bounds (g : gmap chan (gset message)) : Prop :=
    ∀ c ms m, g !! c = Some ms → m ∈ ms → 0 < length m ∧ length m < 2^64.

  Local Program Instance grove_interp: ffi_interp grove_model :=
    {| ffiG := groveG;
       ffi_local_names := unit;
       ffi_global_names := gen_heap_names;
       ffi_get_local_names _ hD := tt;
       ffi_get_global_names _ hD := gen_heapG_get_names (groveG_gen_heapG);
       ffi_update_local  _ hD names := hD;
       ffi_ctx _ _ _ := True%I;
       ffi_global_ctx _ _ g := (gen_heap_interp g ∗ ⌜chan_msg_bounds g⌝)%I;
       ffi_local_start := fun _ _ _ (g: grove_global_state) =>
                      ([∗ map] e↦ms ∈ g, (gen_heap.mapsto (L:=chan) (V:=gset message) e (DfracOwn 1) ms))%I;
       ffi_restart _ _ _ := True%I;
       ffi_crash_rel Σ hF1 σ1 hF2 σ2 := True%I;
    |}.
  Next Obligation. intros ? [[]] [] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
End grove.

Notation "c c↦ ms" := (mapsto (L:=chan) (V:=gset message) c (DfracOwn 1) ms)
                       (at level 20, format "c  c↦  ms") : bi_scope.

Section lifting.
  Existing Instances grove_op grove_model grove_semantics grove_interp.
  Context `{!heapG Σ}.
  Instance groveG0 : groveG Σ := heapG_ffiG.

  Definition send_endpoint (c : string) : val :=
    ExtV (SendEndp, c).
  Definition recv_endpoint (c : string) : val :=
    ExtV (RecvEndp, c).

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
          rewrite /head_step /= in H;
          monad_inv; repeat (simpl in H; monad_inv)
        | H : ext_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        end.

  Lemma wp_MkSendOp c s E :
    {{{ True }}}
      ExternalOp MkSendOp (LitV $ LitString c) @ s; E
    {{{ RET send_endpoint c; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /head_step/=.
      monad_simpl. }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    inv_head_step.
    simpl.
    iFrame.
    iIntros "!>".
    iSplit; first done.
    by iApply "HΦ".
  Qed.

  Lemma wp_MkRecvOp c s E :
    {{{ True }}}
      ExternalOp MkRecvOp (LitV $ LitString c) @ s; E
    {{{ RET recv_endpoint c; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /head_step/=.
      monad_simpl. }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    inv_head_step.
    simpl.
    iFrame.
    iIntros "!>".
    iSplit; first done.
    by iApply "HΦ".
  Qed.

  Lemma mapsto_vals_bytes_valid l (m : message) q (σ : gmap _ _) :
    na_heap.na_heap_ctx tls σ -∗ mapsto_vals l q ((λ b, #(LitByte b)) <$> m) -∗
    ⌜ (forall (i:Z), (0 <= i)%Z -> (i < length m)%Z ->
              match σ !! (l +ₗ i) with
           | Some (Reading _, LitV (LitByte v)) => m !! Z.to_nat i = Some v
           | _ => False
              end) ⌝.
  Proof.
    iIntros "Hh Hv". iDestruct (mapsto_vals_valid with "Hh Hv") as %Hl.
    iPureIntro. intros i Hlb Hub.
    rewrite fmap_length in Hl. specialize (Hl _ Hlb Hub).
    destruct (σ !! (l +ₗ i)) as [[[] v]|]; [done| |done].
    move: Hl. rewrite list_lookup_fmap /=.
    intros [b [? ->]]%fmap_Some_1. done.
  Qed.

  Lemma wp_SendOp c ms (l : loc) (len : u64) (m : message) (q : Qp) s E :
    0 < length m → length m = int.nat len →
    {{{ c c↦ ms ∗ mapsto_vals l q ((λ b, #(LitByte b)) <$> m) }}}
      ExternalOp SendOp (send_endpoint c, (#l, #len))%V @ s; E
    {{{ RET #(); c c↦ (ms ∪ {[m]}) ∗ mapsto_vals l q ((λ b, #(LitByte b)) <$> m) }}}.
  Proof.
    iIntros (Hnonemp Hmlen Φ) "[Hc Hl] HΦ". iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns κ κs nt) "(Hσ&$&Htr) [Hg %Hg] !>".
    iDestruct (@gen_heap_valid with "Hg Hc") as %Hc.
    iDestruct (mapsto_vals_bytes_valid with "Hσ Hl") as %Hl.
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /head_step/=.
      monad_simpl. econstructor; first by econstructor.
      monad_simpl. econstructor; first by econstructor.
      monad_simpl.
    }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    inv_head_step.
    iFrame.
    iMod (@gen_heap_update with "Hg Hc") as "[$ Hc]".
    assert (m = m0) as <-.
    { apply list_eq=>i.
      rename select (length m0 = _ ∧ _) into Hm0. destruct Hm0 as [Hm0len Hm0].
      assert (length m = length m0) as Hlen by rewrite Hmlen //.
      destruct (m !! i) as [v|] eqn:Hm; last first.
      { rewrite Hm. move: Hm. rewrite lookup_ge_None Hlen -lookup_ge_None. done. }
      apply lookup_lt_Some in Hm. apply inj_lt in Hm.
      feed pose proof (Hl i) as Hl; [lia..|].
      feed pose proof (Hm0 i) as Hm0; [lia..|].
      destruct (σ1.(heap) !! (l +ₗ i)) as [[[] v'']|]; try done.
      destruct v'' as [lit| | | | |]; try done.
      destruct lit; try done.
      rewrite Nat2Z.id in Hl Hm0. rewrite Hl Hm0. done. }
    iIntros "!> /=".
    iSplit; first done.
    iSplit.
    { iPureIntro. intros c' ms' m'. destruct (decide (c=c')) as [<-|Hne].
      - rewrite lookup_insert=>-[<-]. rewrite elem_of_union=>-[Hm'|Hm'].
        + eapply Hg; done.
        + rewrite ->elem_of_singleton in Hm'. subst m'. split; first done.
          rewrite Hmlen. word.
      - rewrite lookup_insert_ne //. eapply Hg. }
    iApply "HΦ".
    by iFrame.
  Qed.

  Lemma wp_RecvOp e ms s E :
    {{{ e c↦ ms }}}
      ExternalOp RecvOp (recv_endpoint e) @ s; E
    {{{ (err : bool) (l : loc) (len : u64), RET (#err, (#l, #len));
        e c↦ ms ∗ if err then True else
          ∃ m : message, ⌜m ∈ ms ∧ length m = int.nat len⌝ ∗
            mapsto_vals l 1 ((λ b, #(LitByte b)) <$> m)
    }}}.
  Proof.
    iIntros (Φ) "He HΦ". iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns κ κs nt) "(Hσ&$&Htr) [Hg %Hg] !>".
    iDestruct (@gen_heap_valid with "Hg He") as %He.
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /head_step/=.
      monad_simpl. econstructor; first by econstructor.
      monad_simpl. econstructor.
      { constructor. left. done. }
      monad_simpl. econstructor; first by econstructor.
      monad_simpl.
    }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    inv_head_step.
    monad_inv.
    rename select (m = None ∨ _) into Hm. simpl in Hm.
    destruct Hm as [->|(m' & -> & Hm)].
    { (* Returning no message. *)
      monad_inv. iFrame. simpl. iModIntro. do 2 (iSplit; first done).
      iApply "HΦ". by iFrame. }
    (* Returning a message *)
    repeat match goal with
           | H : relation.bind _ _ _ _ _ |- _ => simpl in H; monad_inv
           end.
    move: (Hg _ _ _ He Hm)=>Hlen.
    rename select (isFresh _ _) into Hfresh.
    iMod (na_heap_alloc_list tls (heap σ1) l
                             ((λ b : u8, #b) <$> m')
                             (Reading O) with "Hσ")
      as "(Hσ & Hblock & Hl)".
    { rewrite fmap_length. apply Nat2Z.inj_lt. apply Hlen. }
    { destruct Hfresh as (?&?); eauto. }
    { destruct Hfresh as (H'&?); eauto. eapply H'. }
    { destruct Hfresh as (H'&?); eauto. destruct (H' 0) as (?&Hfresh).
      by rewrite (loc_add_0) in Hfresh. }
    { eauto. }
    iModIntro. iEval simpl. iFrame "Htr Hg Hσ".
    do 2 (iSplit; first done).
    iApply "HΦ". iFrame "He".
    iExists m'. iSplit.
    { iPureIntro. split; first done.
      trans (Z.to_nat (Z.of_nat (length m'))); first by rewrite Nat2Z.id //.
      f_equal. word. }
    rewrite /mapsto_vals. iApply (big_sepL_mono with "Hl").
    clear -Hfresh. simpl. iIntros (i v _) "[Hmapsto _]".
    iApply (na_mapsto_to_heap with "Hmapsto").
    destruct Hfresh as (Hfresh & _). eapply Hfresh.
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
