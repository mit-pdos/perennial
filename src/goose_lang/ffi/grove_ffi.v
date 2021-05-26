(** FFI module for distributed Perennial (Grove). So far, consist only of a
network *)
From stdpp Require Import gmap vector fin_maps.
From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import numbers.
From Perennial.algebra Require Import gen_heap_names.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Import ectx_lifting atomic.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import prelude typing struct lang lifting slice typed_slice proofmode.
From Perennial.goose_lang Require Import crash_modality.

Set Default Proof Using "Type".
(* this is purely cosmetic but it makes printing line up with how the code is
usually written *)
Set Printing Projections.

(** * The Grove extension to GooseLang: primitive operations [Trusted definitions!] *)

Inductive GroveOp := ListenOp | ConnectOp | AcceptOp | SendOp | RecvOp.
Instance eq_GroveOp : EqDecision GroveOp.
Proof. solve_decision. Defined.
Instance GroveOp_fin : Countable GroveOp.
Proof. solve_countable GroveOp_rec 10%nat. Qed.

(** [char] corresponds to a host-IP-pair *)
Definition chan := u64.
Inductive GroveVal :=
(** Corresponds to a 2-tuple. *)
| ListenSocketV (c : chan)
(** Corresponds to a 4-tuple. [c_l] is the local part, [c_r] the remote part. *)
| ConnectionSocketV (c_l : chan) (c_r : chan)
(** A bad (error'd) connection *)
| BadSocketV.
Instance GroveVal_eq_decision : EqDecision GroveVal.
Proof. solve_decision. Defined.
Instance GroveVal_countable : Countable GroveVal.
Proof.
  refine (inj_countable'
    (λ x, match x with
          | ListenSocketV c => inl c
          | ConnectionSocketV c_l c_r => inr $ inl (c_l, c_r)
          | BadSocketV => inr $ inr ()
          end)
    (λ x, match x with
          | inl c => ListenSocketV c
          | inr (inl (c_l, c_r)) => ConnectionSocketV c_l c_r
          | inr (inr ()) => BadSocketV
          end)
    _);
  by intros [].
Qed.

Definition grove_op : ffi_syntax.
Proof.
  refine (mkExtOp GroveOp _ _ GroveVal _ _).
Defined.

Inductive GroveTys := GroveListenTy | GroveConnectionTy.

(* TODO: Why is this an instance but the ones above are not? *)
Instance grove_val_ty: val_types :=
  {| ext_tys := GroveTys; |}.
Definition grove_ty: ext_types grove_op :=
  {| val_tys := grove_val_ty;
     get_ext_tys _ _ := False |}. (* currently we just don't give types for the GroveOps *)

Record message := Message { msg_sender : chan; msg_data : list u8 }.
Add Printing Constructor message. (* avoid printing with record syntax *)
Instance message_eq_decision : EqDecision message.
Proof. solve_decision. Defined.
Instance message_countable : Countable message.
Proof.
  refine (inj_countable'
    (λ x, (msg_sender x, msg_data x))
    (λ i, Message i.1 i.2)
    _).
  by intros [].
Qed.

(** The global network state: a map from endpoint names to the set of messages sent to
those endpoints. *)
Definition grove_global_state : Type := gmap chan (gset message).

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

  Definition isFreshChan (σg : state * global_state) (c : option chan) : Prop :=
    match c with
    | None => True (* failure (to allocate a channel) is always an option *)
    | Some c => σg.2 !! c = None
    end.

  Definition gen_isFreshChan σg : isFreshChan σg None.
  Proof. rewrite /isFreshChan //. Defined.

  Global Instance alloc_chan_gen : GenPred (option chan) (state*global_state) isFreshChan.
  Proof. intros _ σg. refine (Some (exist _ _ (gen_isFreshChan σg))). Defined.

  Global Instance chan_GenType Σ : GenType chan Σ :=
    fun z _ => Some (exist _ (U64 z) I).

  Definition ffi_step (op: GroveOp) (v: val): transition (state*global_state) val :=
    match op, v with
    | ListenOp, LitV (LitInt c) =>
      ret (ExtV (ListenSocketV c))
    | ConnectOp, LitV (LitInt c_r) =>
      c_l ← suchThat isFreshChan;
      match c_l with
      | None => ret ((*err*)#true, ExtV BadSocketV)%V
      | Some c_l =>
        modify (λ '(σ,g), (σ, <[ c_l := ∅ ]> g));;
        ret ((*err*)#false, ExtV (ConnectionSocketV c_l c_r))%V
      end
    | AcceptOp, ExtV (ListenSocketV c_l) =>
      c_r ← any chan;
      ret (ExtV (ConnectionSocketV c_l c_r))
    | SendOp, (ExtV (ConnectionSocketV c_l c_r), (LitV (LitLoc l), LitV (LitInt len)))%V =>
      err_early ← any bool;
      if err_early is true then ret (*err*)#true else
      data ← suchThat (gen:=fun _ _ => None) (λ '(σ,g) (data : list byte),
            length data = int.nat len ∧ forall (i:Z), 0 <= i -> i < length data ->
                match σ.(heap) !! (l +ₗ i) with
                | Some (Reading _, LitV (LitByte v)) => data !! Z.to_nat i = Some v
                | _ => False
                end);
      ms ← reads (λ '(σ,g), g !! c_r) ≫= unwrap;
      modify (λ '(σ,g), (σ, <[ c_r := ms ∪ {[Message c_l data]} ]> g));;
      err_late ← any bool;
      ret (*err*)#(err_late : bool)
    | RecvOp, ExtV (ConnectionSocketV c_l c_r) =>
      ms ← reads (λ '(σ,g), g !! c_l) ≫= unwrap;
      m ← suchThat (gen:=fun _ _ => None) (λ _ (m : option message),
            m = None ∨ ∃ m', m = Some m' ∧ m' ∈ ms ∧ m'.(msg_sender) = c_r);
      match m with
      | None =>
        (* We errored, non-deterministically pick error code 1 (timeout) or 2 (other error). *)
        timeout ← any bool;
        ret ((*err*)#(if timeout is true then 1 else 2), (#locations.null, #0))%V
      | Some m =>
        l ← allocateN;
        modify (λ '(σ,g), (state_insert_list l ((λ b, #(LitByte b)) <$> m.(msg_data)) σ, g));;
        ret  ((*err*)#0, (#(l : loc), #(length m.(msg_data))))%V
      end
    | _, _ => undefined
    end.

  Local Instance grove_semantics : ffi_semantics grove_op grove_model :=
    { ffi_step := ffi_step;
      ffi_crash_step := eq; }.
End grove.

(** * Grove semantic interpretation and lifting lemmas *)
Class groveG Σ :=
  { groveG_gen_heapG :> gen_heap.gen_heapGS chan (gset message) Σ; }.

Class grove_preG Σ :=
  { grove_preG_gen_heapG :> gen_heap.gen_heapGpreS chan (gset message) Σ; }.

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

  Local Definition data_vals (data : list u8) : list val :=
    ((λ b, #(LitByte b)) <$> data).

  Local Definition chan_msg_bounds (g : gmap chan (gset message)) : Prop :=
    ∀ c ms m, g !! c = Some ms → m ∈ ms → length m.(msg_data) < 2^64.

  Local Program Instance grove_interp: ffi_interp grove_model :=
    {| ffiG := groveG;
       ffi_local_names := unit;
       ffi_global_names := gen_heap_names;
       ffi_get_local_names _ hD := tt;
       ffi_get_global_names _ hD := gen_heapG_get_names (groveG_gen_heapG);
       ffi_update_local  _ hD names := hD;
       ffi_ctx _ _ _ := True%I;
       ffi_global_ctx _ _ g := (gen_heap_interp g ∗ ⌜chan_msg_bounds g⌝)%I;
       ffi_local_start := fun _ _ _ (g: grove_global_state) => True%I;
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
  Context `{!heapGS Σ}.
  Instance heapG_groveG : groveG Σ := heapG_ffiG.

  Definition chan_meta_token (c : chan) (E: coPset) : iProp Σ :=
    gen_heap.meta_token (hG := groveG_gen_heapG) c E.
  Definition chan_meta `{Countable A} (c : chan) N (x : A) : iProp Σ :=
    gen_heap.meta (hG := groveG_gen_heapG) c N x.

  Definition connection_socket (c_l : chan) (c_r : chan) : val :=
    ExtV (ConnectionSocketV c_l c_r).
  Definition listen_socket (c : chan) : val :=
    ExtV (ListenSocketV c).
  Definition bad_socket : val :=
    ExtV BadSocketV.

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
        | H : ffi_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        end.

  Lemma wp_ListenOp c s E :
    {{{ True }}}
      ExternalOp ListenOp (LitV $ LitInt c) @ s; E
    {{{ RET listen_socket c; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /head_step/=.
      monad_simpl. }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    inv_head_step.
    simpl.
    iFrame.
    iIntros "!>".
    iSplit; first done.
    by iApply "HΦ".
  Qed.

  Lemma wp_ConnectOp c_r s E :
    {{{ True }}}
      ExternalOp ConnectOp (LitV $ LitInt c_r) @ s; E
    {{{ (err : bool) (c_l : chan),
      RET (#err, if err then bad_socket else connection_socket c_l c_r);
      if err then True else c_l c↦ ∅
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /head_step/=.
      monad_simpl. econstructor.
      { econstructor. eapply gen_isFreshChan. }
      monad_simpl. econstructor; first by econstructor.
      monad_simpl.
    }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    iDestruct "Hg" as "([Hg %Hg]&?)".
    inv_head_step.
    match goal with
    | H : isFreshChan _ ?c |- _ => rename H into Hfresh; rename c into c_l
    end.
    destruct c_l as [c_l|]; last first.
    { (* Failed to pick a fresh channel. *)
      monad_inv. simpl. iFrame. iModIntro.
      do 2 (iSplit; first done).
      iApply ("HΦ" $! true (U64 0)). done. }
    simpl in *. monad_inv. simpl.
    iMod (@gen_heap_alloc with "Hg") as "[$ [Hr _]]"; first done.
    iIntros "!> /=".
    iFrame.
    iSplit; first done.
    iSplit.
    { iPureIntro. clear c_r. intros c ms m. destruct (decide (c = c_l)) as [->|Hne].
      - rewrite lookup_insert=>-[<-]. rewrite elem_of_empty. done.
      - rewrite lookup_insert_ne //. apply Hg. }
    by iApply ("HΦ" $! false).
  Qed.

  Lemma wp_AcceptOp c_l s E :
    {{{ True }}}
      ExternalOp AcceptOp (listen_socket c_l) @ s; E
    {{{ c_r, RET connection_socket c_l c_r; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /head_step/=.
      monad_simpl. econstructor.
      1:by eapply (relation.suchThat_runs _ _ (U64 0)).
      monad_simpl. }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    inv_head_step.
    simpl.
    iFrame.
    iIntros "!>".
    iSplit; first done.
    by iApply "HΦ".
  Qed.

  Lemma mapsto_vals_bytes_valid l (data : list u8) q (σ : gmap _ _) :
    na_heap.na_heap_ctx tls σ -∗ mapsto_vals l q (data_vals data) -∗
    ⌜ (forall (i:Z), (0 <= i)%Z -> (i < length data)%Z ->
              match σ !! (l +ₗ i) with
           | Some (Reading _, LitV (LitByte v)) => data !! Z.to_nat i = Some v
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

  Lemma wp_SendOp c_l c_r ms (l : loc) (len : u64) (data : list u8) (q : Qp) s E :
    length data = int.nat len →
    {{{ c_r c↦ ms ∗ mapsto_vals l q (data_vals data) }}}
      ExternalOp SendOp (connection_socket c_l c_r, (#l, #len))%V @ s; E
    {{{ (err_early err_late : bool), RET #(err_early || err_late);
       c_r c↦ (if err_early then ms else ms ∪ {[Message c_l data]}) ∗
       mapsto_vals l q (data_vals data) }}}.
  Proof.
    iIntros (Hmlen Φ) "[Hc Hl] HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&$&Htr) Hg".
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    iDestruct "Hg" as "([Hg %Hg]&?)".
    iDestruct (@gen_heap_valid with "Hg Hc") as %Hc.
    iDestruct (mapsto_vals_bytes_valid with "Hσ Hl") as %Hl.
    iModIntro.
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /head_step/=.
      monad_simpl. econstructor. 1:by eapply (relation.suchThat_runs _ _ true).
      monad_simpl. econstructor; first by econstructor.
      monad_simpl.
    }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    inv_head_step.
    rename x into err_early. clear H.
    destruct err_early.
    { monad_inv. iFrame. iModIntro.
      do 2 (iSplitR; first done).
      iApply ("HΦ" $! true true). by iFrame. }
    inv_head_step.
    monad_inv.
    rename x into err_late.
    iFrame.
    iMod (@gen_heap_update with "Hg Hc") as "[$ Hc]".
    assert (data = data0) as <-.
    { apply list_eq=>i.
      rename select (length _ = _ ∧ _) into Hm0. destruct Hm0 as [Hm0len Hm0].
      assert (length data0 = length data) as Hlen by rewrite Hmlen //.
      destruct (data !! i) as [v|] eqn:Hm; last first.
      { move: Hm. rewrite lookup_ge_None -Hlen -lookup_ge_None. done. }
      rewrite -Hm. apply lookup_lt_Some in Hm. apply inj_lt in Hm.
      feed pose proof (Hl i) as Hl; [lia..|].
      feed pose proof (Hm0 i) as Hm0; [lia..|].
      destruct (σ1.(heap) !! (l +ₗ i)) as [[[] v'']|]; try done.
      destruct v'' as [lit| | | | |]; try done.
      destruct lit; try done.
      rewrite Nat2Z.id in Hl Hm0. rewrite Hl -Hm0. done. }
    iIntros "!> /=".
    iSplit; first done.
    iSplit.
    { iPureIntro. intros c' ms' m'. destruct (decide (c_r = c')) as [<-|Hne].
      - rewrite lookup_insert=>-[<-]. rewrite elem_of_union=>-[Hm'|Hm'].
        + eapply Hg; done.
        + rewrite ->elem_of_singleton in Hm'. subst m'.
          rewrite Hmlen. word.
      - rewrite lookup_insert_ne //. eapply Hg. }
    iApply ("HΦ" $! false err_late).
    by iFrame.
  Qed.

  Inductive recv_err := RecvErrTimeout | RecvErrOther.
  Definition recv_errno (err : option recv_err) : Z :=
    match err with
    | None => 0
    | Some RecvErrTimeout => 1
    | Some RecvErrOther => 2
    end.

  Lemma wp_RecvOp c_l c_r ms s E :
    {{{ c_l c↦ ms }}}
      ExternalOp RecvOp (connection_socket c_l c_r) @ s; E
    {{{ (err : option recv_err) (l : loc) (len : u64) (data : list u8),
        RET (#(recv_errno err), (#l, #len));
        ⌜if err is Some _ then l = null ∧ data = [] ∧ len = 0 else
          Message c_r data ∈ ms ∧ length data = int.nat len⌝ ∗
        c_l c↦ ms ∗ mapsto_vals l 1 (data_vals data)
    }}}.
  Proof.
    iIntros (Φ) "He HΦ". iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&$&Htr) Hg".
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    iDestruct "Hg" as "([Hg %Hg]&?)".
    iModIntro.
    iDestruct (@gen_heap_valid with "Hg He") as %He.
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /head_step/=.
      monad_simpl. econstructor; first by econstructor.
      monad_simpl. econstructor.
      { constructor. left. done. }
      monad_simpl. econstructor.
      { econstructor. 1: by eapply (relation.suchThat_runs _ _ true). done. }
      monad_simpl.
    }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    inv_head_step.
    monad_inv.
    rename select (m = None ∨ _) into Hm. simpl in Hm.
    destruct Hm as [->|(m' & -> & Hm & <-)].
    { (* Returning no message. *)
      inv_head_step.
      monad_inv.
      rename x into timeout.
      iFrame. simpl. iModIntro. do 2 (iSplit; first done). destruct timeout.
      1: iApply ("HΦ" $! (Some RecvErrTimeout)).
      2: iApply ("HΦ" $! (Some RecvErrOther)).
      all: iFrame; (iSplit; first done); rewrite /mapsto_vals big_sepL_nil //.
    }
    (* Returning a message *)
    repeat match goal with
           | H : relation.bind _ _ _ _ _ |- _ => simpl in H; monad_inv
           end.
    move: (Hg _ _ _ He Hm)=>Hlen.
    rename select (isFresh _ _) into Hfresh.
    iAssert (na_heap_ctx tls (heap_array l ((λ v : val, (Reading 0, v)) <$> data_vals m'.(msg_data)) ∪ σ1.(heap)) ∗
      [∗ list] i↦v ∈ data_vals m'.(msg_data), na_heap_mapsto (addr_plus_off l i) 1 v)%I
      with "[> Hσ]" as "[Hσ Hl]".
    { destruct (decide (length m'.(msg_data) = 0%nat)) as [Heq%nil_length_inv|Hne].
      { (* Zero-length message... no actually new memory allocation, so the proof needs
           to work a bit differently. *)
        rewrite Heq big_sepL_nil fmap_nil /= left_id. by iFrame. }
      iMod (na_heap_alloc_list tls (heap σ1) l
                               (data_vals m'.(msg_data))
                               (Reading O) with "Hσ")
        as "(Hσ & Hblock & Hl)".
      { rewrite fmap_length. apply Nat2Z.inj_lt. lia. }
      { destruct Hfresh as (?&?); eauto. }
      { destruct Hfresh as (H'&?); eauto. eapply H'. }
      { destruct Hfresh as (H'&?); eauto. destruct (H' 0) as (?&Hfresh).
          by rewrite (loc_add_0) in Hfresh. }
      { eauto. }
      iModIntro. iFrame "Hσ". iApply (big_sepL_impl with "Hl").
      iIntros "!#" (???) "[$ _]".
    }
    iModIntro. iEval simpl. iFrame "Htr Hg Hσ ∗".
    do 2 (iSplit; first done).
    iApply ("HΦ" $! None _ _ m'.(msg_data)). iFrame "He".
    iSplit.
    { iPureIntro. split; first by destruct m'.
      trans (Z.to_nat (Z.of_nat (length m'.(msg_data)))); first by rewrite Nat2Z.id //.
      f_equal. word. }
    rewrite /mapsto_vals. iApply (big_sepL_mono with "Hl").
    clear -Hfresh. simpl. iIntros (i v _) "Hmapsto".
    iApply (na_mapsto_to_heap with "Hmapsto").
    destruct Hfresh as (Hfresh & _). eapply Hfresh.
  Qed.

End lifting.

(** * Grove user-facing operations and their specs *)
Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
  (* FIXME: figure out which of these clients need to set *)
  Existing Instances grove_op grove_model grove_ty grove_semantics grove_interp heapG_groveG.
  Local Coercion Var' (s:string) : expr := Var s.

  (** We only use these types behind a ptr indirection so their size should not matter. *)
  (* FIXME: This is a bit strange; not sure how to think about "axiomatizing" a struct *)
  Definition Listener : ty := extT GroveListenTy.
  Definition Connection : ty := extT GroveConnectionTy.
  Definition Address : ty := uint64T.

  Definition ConnectRet := (struct.decl [
                              "Err" :: boolT;
                              "Connection" :: Connection
                            ])%struct.

  Definition ReceiveRet := (struct.decl [
                              "Err" :: uint64T;
                              "Data" :: slice.T byteT
                            ])%struct.

  (** Type: func(uint64) Listener *)
  Definition Listen : val :=
    λ: "e", ExternalOp ListenOp "e".

  (** Type: func(uint64) (bool, Connection) *)
  Definition Connect : val :=
    λ: "e",
      let: "c" := ExternalOp ConnectOp "e" in
      let: "err" := Fst "c" in
      let: "socket" := Snd "c" in
      struct.mk ConnectRet [
        "Err" ::= "err";
        "Connection" ::= "socket"
      ].

  (** Type: func(Listener) Connection *)
  Definition Accept : val :=
    λ: "e", ExternalOp AcceptOp "e".

  (** Type: func(Connection, []byte) *)
  Definition Send : val :=
    λ: "e" "m", ExternalOp SendOp ("e", (slice.ptr "m", slice.len "m")).

  (** Type: func(Connection, uint64) (bool, []byte) *)
  Definition Receive : val :=
    λ: "e" "timeout_ms",
      let: "r" := ExternalOp RecvOp "e" in
      let: "err" := Fst "r" in
      let: "slice" := Snd "r" in
      let: "ptr" := Fst "slice" in
      let: "len" := Snd "slice" in
      struct.mk ReceiveRet [
        "Err" ::= "err";
        "Data" ::= ("ptr", "len", "len")
      ].

  Context `{!heapGS Σ}.

  Lemma wp_Listen c_l s E :
    {{{ True }}}
      Listen #(LitInt c_l) @ s; E
    {{{ RET listen_socket c_l; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_apply wp_ListenOp. by iApply "HΦ".
  Qed.

  Lemma wp_Connect c_r s E :
    {{{ True }}}
      Connect #(LitInt c_r) @ s; E
    {{{ (err : bool) (c_l : chan),
        RET struct.mk_f ConnectRet [
              "Err" ::= #err;
              "Connection" ::= if err then bad_socket else connection_socket c_l c_r
            ];
      if err then True else c_l c↦ ∅
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_apply wp_ConnectOp.
    iIntros (err recv) "Hr". wp_pures.
    by iApply ("HΦ" $! err). (* Wow, Coq is doing magic here *)
  Qed.

  Lemma wp_Accept c_l s E :
    {{{ True }}}
      Accept (listen_socket c_l)  @ s; E
    {{{ (c_r : chan), RET connection_socket c_l c_r; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_apply wp_AcceptOp. by iApply "HΦ".
  Qed.

  Lemma is_slice_small_byte_mapsto_vals (s : Slice.t) (data : list u8) (q : Qp) :
    is_slice_small s byteT q data -∗ mapsto_vals (Slice.ptr s) q (data_vals data).
  Proof.
    iIntros "[Hs _]". rewrite /array.array /mapsto_vals.
    change (list.untype data) with (data_vals data).
    iApply (big_sepL_impl with "Hs"). iIntros "!#" (i v Hv) "Hl".
    move: Hv. rewrite /data_vals list_lookup_fmap.
    intros (b & _ & ->)%fmap_Some_1.
    rewrite byte_mapsto_untype byte_offset_untype //.
  Qed.

  Lemma mapsto_vals_is_slice_small_byte (s : Slice.t) (data : list u8) (q : Qp) :
    length data = int.nat (Slice.sz s) →
    mapsto_vals (Slice.ptr s) q (data_vals data) -∗
    is_slice_small s byteT q data.
  Proof.
    iIntros (Hlen) "Hl". iSplit; last first.
    { iPureIntro. rewrite /list.untype fmap_length. done. }
    rewrite /array.array /mapsto_vals.
    change (list.untype data) with (data_vals data).
    iApply (big_sepL_impl with "Hl"). iIntros "!#" (i v Hv) "Hl".
    move: Hv. rewrite /data_vals list_lookup_fmap.
    intros (b & _ & ->)%fmap_Some_1.
    rewrite byte_mapsto_untype byte_offset_untype //.
  Qed.

  Lemma wp_Send c_l c_r (s : Slice.t) (data : list u8) (q : Qp) :
    ⊢ {{{ is_slice_small s byteT q data }}}
      <<< ∀∀ ms, c_r c↦ ms >>>
        Send (connection_socket c_l c_r) (slice_val s) @ ⊤
      <<<▷ ∃∃ (msg_sent : bool),
        c_r c↦ (if msg_sent then ms ∪ {[Message c_l data]} else ms)
      >>>
      {{{ (err : bool), RET #err; ⌜if err then True else msg_sent⌝ ∗
        is_slice_small s byteT q data }}}.
  Proof.
    iIntros "!#" (Φ) "Hs HΦ". wp_lam. wp_let.
    wp_apply wp_slice_ptr.
    wp_apply wp_slice_len.
    wp_pures.
    iAssert (⌜length data = int.nat (Slice.sz s)⌝)%I as %?.
    { iDestruct "Hs" as "[_ %Hlen]". iPureIntro. revert Hlen.
      rewrite /list.untype fmap_length. done. }
    iMod "HΦ" as (ms) "[Hc HΦ]".
    wp_apply (wp_SendOp with "[$Hc Hs]"); [done..| |].
    { iApply is_slice_small_byte_mapsto_vals. done. }
    iIntros (err_early err_late) "[Hc Hl]".
    iApply ("HΦ" $! (negb err_early) with "[Hc]").
    { by destruct err_early. }
    iSplit.
    - iPureIntro. by destruct err_early, err_late.
    - iApply mapsto_vals_is_slice_small_byte; done.
  Qed.

  Lemma wp_Receive c_l c_r (timeout_ms : u64) :
    ⊢ <<< ∀∀ ms, c_l c↦ ms >>>
        Receive (connection_socket c_l c_r) #timeout_ms @ ⊤
      <<<▷ ∃∃ (err : option recv_err) (data : list u8),
        c_l c↦ ms ∗ if err then True else ⌜Message c_r data ∈ ms⌝
      >>>
      {{{ (s : Slice.t),
        RET struct.mk_f ReceiveRet [
              "Err" ::= #(recv_errno err);
              "Data" ::= slice_val s
            ];
          is_slice s byteT 1 data
      }}}.
  Proof.
    iIntros "!#" (Φ) "HΦ". wp_lam. wp_pures.
    wp_bind (ExternalOp _ _).
    iMod "HΦ" as (ms) "[Hc HΦ]".
    wp_apply (wp_RecvOp with "Hc").
    iIntros (err l len data) "(%Hm & Hc & Hl)".
    iMod ("HΦ" $! err data with "[Hc]") as "HΦ".
    { iFrame. destruct err; first done. iPureIntro. apply Hm. }
    iModIntro. wp_pures. iModIntro.
    destruct err.
    { iApply ("HΦ" $! (Slice.mk _ _ _)). simpl. destruct Hm as (-> & -> & ->).
      iApply is_slice_zero. }
    destruct Hm as [Hin Hlen].
    iApply ("HΦ" $! (Slice.mk _ _ _)).
    iSplitL.
    - iApply mapsto_vals_is_slice_small_byte; done.
    - iExists []. simpl. iSplit; first by eauto with lia.
      iApply array.array_nil. done.
  Qed.
End grove.

From Perennial.goose_lang Require Import adequacy.

Program Instance grove_interp_adequacy:
  @ffi_interp_adequacy grove_model grove_interp grove_op grove_semantics :=
  {| ffi_preG := grove_preG;
     ffiΣ := groveΣ;
     subG_ffiPreG := subG_groveG;
     ffi_initgP := λ g, chan_msg_bounds g;
     ffi_initP := λ _ g, True;
     ffi_update_pre := (λ _ hP _ names, @grove_update_pre _ hP names);
     ffi_pre_global_start _ hP names g :=
       let hG := @grove_update_pre _ hP names in
       (([∗ map] e↦ms ∈ g, (gen_heap.mapsto (L:=chan) (V:=gset message) e (DfracOwn 1) ms)) ∗
        ([∗ map] e↦_ ∈ g, (gen_heap.meta_token e ⊤)))%I;
     ffi_pre_global_ctx  _ hP names g :=
       let hG := @grove_update_pre _ hP names in
       (gen_heap_interp g ∗ ⌜chan_msg_bounds g⌝)%I;
  |}.
Next Obligation. rewrite //=. Qed.
Next Obligation. rewrite //=. intros ?? [] => //=. Qed.
Next Obligation. rewrite //=. intros ?? [] [] => //=. Qed.
Next Obligation. rewrite //=. Qed.
Next Obligation.
  rewrite //=. iIntros (Σ hPre g Hchan). eauto.
  iMod (gen_heap_name_strong_init' g) as (names) "(H1&H2&H3)".
  iExists names. iFrame. eauto.
Qed.
Next Obligation.
  rewrite //=.
  iIntros (Σ hPre σ ???) "H".
  iExists tt. eauto.
Qed.
Next Obligation.
  iIntros (Σ σ σ' g Hcrash Hold) "Hinterp Hg".
  iExists (ffi_get_local_names _ Hold) => //=.
  inversion Hcrash; subst.
  iFrame. eauto.
Qed.
