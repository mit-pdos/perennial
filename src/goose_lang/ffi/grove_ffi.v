(** FFI module for distributed Perennial (Grove). So far, consist only of a
network *)
From stdpp Require Import gmap vector fin_maps.
From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import numbers.
From Perennial.algebra Require Import gen_heap_names.
From iris.proofmode Require Import tactics.
From Perennial.base_logic Require Import ghost_map mono_nat.
From Perennial.program_logic Require Import ectx_lifting atomic.

From Perennial.Helpers Require Import CountableTactics Transitions Integers.
From Perennial.goose_lang Require Import prelude typing struct lang lifting slice typed_slice proofmode control.
From Perennial.goose_lang Require Import wpc_proofmode crash_modality.

Set Default Proof Using "Type".
(* this is purely cosmetic but it makes printing line up with how the code is
usually written *)
Set Printing Projections.

(** * The Grove extension to GooseLang: primitive operations [Trusted definitions!] *)

Inductive GroveOp : Set :=
  (* Network ops *)
  ListenOp | ConnectOp | AcceptOp | SendOp | RecvOp |
  (* File ops *)
  FileReadOp | FileWriteOp | FileAppendOp |
  (* Time ops *)
  GetTscOp |
  GetTimeRangeOp
.
#[global]
Instance eq_GroveOp : EqDecision GroveOp.
Proof. solve_decision. Defined.
#[global]
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
#[global]
Instance GroveVal_eq_decision : EqDecision GroveVal.
Proof. solve_decision. Defined.
#[global]
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

Inductive GroveTys : Set := GroveListenTy | GroveConnectionTy.

(* TODO: Why is this an instance but the ones above are not? *)
#[global]
Instance grove_val_ty: val_types :=
  {| ext_tys := GroveTys; |}.
Definition grove_ty: ext_types grove_op :=
  {| val_tys := grove_val_ty;
     get_ext_tys _ _ := False |}. (* currently we just don't give types for the GroveOps *)

Record message := Message { msg_sender : chan; msg_data : list u8 }.
Add Printing Constructor message. (* avoid printing with record syntax *)
#[global]
Instance message_eq_decision : EqDecision message.
Proof. solve_decision. Defined.
#[global]
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
Record grove_global_state : Type := {
  grove_net: gmap chan (gset message);
  grove_global_time: u64;
}.

Global Instance grove_global_state_settable : Settable _ :=
  settable! Build_grove_global_state <grove_net; grove_global_time>.

Global Instance grove_global_state_inhabited : Inhabited grove_global_state :=
  populate {| grove_net := ∅; grove_global_time := 0 |}.

(** The per-node state *)
Record grove_node_state : Type := {
  grove_node_tsc : u64;
  grove_node_files: gmap string (list byte);
}.

Global Instance grove_node_state_settable : Settable _ :=
  settable! Build_grove_node_state <grove_node_tsc; grove_node_files>.

Global Instance grove_node_state_inhabited : Inhabited grove_node_state :=
  populate {| grove_node_tsc := 0; grove_node_files := ∅ |}.

Definition grove_model : ffi_model.
Proof.
  refine (mkFfiModel grove_node_state grove_global_state _ _).
Defined.

Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
  Existing Instances grove_op grove_model.

  Existing Instances r_mbind r_fmap.

  Definition isFreshChan (σg : state * global_state) (c : option chan) : Prop :=
    match c with
    | None => True (* failure (to allocate a channel) is always an option *)
    | Some c => σg.2.(global_world).(grove_net) !! c = None
    end.

  Definition gen_isFreshChan σg : isFreshChan σg None.
  Proof. rewrite /isFreshChan //. Defined.

  Global Instance alloc_chan_gen : GenPred (option chan) (state*global_state) isFreshChan.
  Proof. intros _ σg. refine (Some (exist _ _ (gen_isFreshChan σg))). Defined.

  Global Instance chan_GenType Σ : GenType chan Σ :=
    fun z _ => Some (exist _ (W64 z) I).

  Local Definition modify_g (f : grove_global_state → grove_global_state) : transition (state*global_state) () :=
    modify (λ '(σ, g), (σ, set global_world f g)).

  Local Definition modify_n (f : grove_node_state → grove_node_state) : transition (state*global_state) () :=
    modify (λ '(σ, g), (set world f σ, g)).

  Definition ffi_step (op: GroveOp) (v: val): transition (state*global_state) expr :=
    match op, v with
    (* Network *)
    | ListenOp, LitV (LitInt c) =>
      ret $ Val $ (ExtV (ListenSocketV c))
    | ConnectOp, LitV (LitInt c_r) =>
      c_l ← suchThat isFreshChan;
      match c_l with
      | None => ret $ Val $ ((*err*)#true, ExtV BadSocketV)%V
      | Some c_l =>
        modify_g (set grove_net $ λ g, <[ c_l := ∅ ]> g);;
        ret $ Val $ ((*err*)#false, ExtV (ConnectionSocketV c_l c_r))%V
      end
    | AcceptOp, ExtV (ListenSocketV c_l) =>
      c_r ← any chan;
      ret $ Val $ (ExtV (ConnectionSocketV c_l c_r))
    | SendOp, (ExtV (ConnectionSocketV c_l c_r), (LitV (LitLoc l), LitV (LitInt len)))%V =>
      err_early ← any bool;
      if err_early is true then ret $ Val $ (*err*)#true else
      data ← suchThat (gen:=fun _ _ => None) (λ '(σ,g) (data : list byte),
            length data = uint.nat len ∧ forall (i:Z), 0 <= i -> i < length data ->
                match σ.(heap) !! (l +ₗ i) with
                | Some (Reading _, LitV (LitByte v)) => data !! Z.to_nat i = Some v
                | _ => False
                end);
      ms ← reads (λ '(σ,g), g.(global_world).(grove_net) !! c_r) ≫= unwrap;
      modify_g (set grove_net $ λ g, <[ c_r := ms ∪ {[Message c_l data]} ]> g);;
      err_late ← any bool;
      ret $ Val $ (*err*)#(err_late : bool)
    | RecvOp, ExtV (ConnectionSocketV c_l c_r) =>
      ms ← reads (λ '(σ,g), g.(global_world).(grove_net) !! c_l) ≫= unwrap;
      m ← suchThat (gen:=fun _ _ => None) (λ _ (m : option message),
            m = None ∨ ∃ m', m = Some m' ∧ m' ∈ ms ∧ m'.(msg_sender) = c_r);
      match m with
      | None =>
        (* We errored *)
        ret $ Val $ ((*err*)#true, (#locations.null, #0))%V
      | Some m =>
        l ← allocateN;
        modify (λ '(σ,g), (state_insert_list l ((λ b, #(LitByte b)) <$> m.(msg_data)) σ, g));;
        ret $ Val $ ((*err*)#false, (#(l : loc), #(length m.(msg_data))))%V
      end
    (* File *)
    | FileReadOp, LitV (LitString name) =>
      err ← any bool;
      if err is true then ret $ Val ((*err*)#true, (#locations.null, #0))%V else
      content ← reads (λ '(σ,g), σ.(world).(grove_node_files) !! name) ≫= unwrap;
      l ← allocateN;
      modify (λ '(σ,g), (state_insert_list l ((λ b, #(LitByte b)) <$> content) σ, g));;
      ret $ Val ((*err*)#false, (#(l : loc), #(length content)))%V
    | FileWriteOp, (LitV (LitString name), (LitV (LitLoc l), LitV (LitInt len)))%V =>
      err_early ← any bool;
      if err_early is true then ret $ Val $ (*err*)#true else
      new_content ← suchThat (gen:=fun _ _ => None) (λ '(σ,g) (data : list byte),
            length data = uint.nat len ∧ forall (i:Z), 0 <= i -> i < length data ->
                match σ.(heap) !! (l +ₗ i) with
                | Some (Reading _, LitV (LitByte v)) => data !! Z.to_nat i = Some v
                | _ => False
                end);
      (* we read the content just to ensure the file exists *)
      old_content ← reads (λ '(σ,g), σ.(world).(grove_node_files) !! name) ≫= unwrap;
      modify_n (set grove_node_files $ <[ name := new_content ]>);;
      ret $ Val $ (*err*)#false
    | FileAppendOp, (LitV (LitString name), (LitV (LitLoc l), LitV (LitInt len)))%V =>
      err_early ← any bool;
      if err_early is true then ret $ Val $ (*err*)#true else
      new_content ← suchThat (gen:=fun _ _ => None) (λ '(σ,g) (data : list byte),
            length data = uint.nat len ∧ forall (i:Z), 0 <= i -> i < length data ->
                match σ.(heap) !! (l +ₗ i) with
                | Some (Reading _, LitV (LitByte v)) => data !! Z.to_nat i = Some v
                | _ => False
                end);
      old_content ← reads (λ '(σ,g), σ.(world).(grove_node_files) !! name) ≫= unwrap;
      (* Files cannot become bigger than 2^64 bytes on real systems, so we also
      reject that here. *)
      if bool_decide (length (old_content ++ new_content) >= 2^64) then ret $ Val #true else
      modify_n (set grove_node_files $ <[ name := old_content ++ new_content ]>);;
      ret $ Val $ (*err*)#false
    (* Time *)
    | GetTscOp, LitV LitUnit =>
      time_since_last ← any u64;
      modify_n (set grove_node_tsc (λ old_time,
        let new_time := word.add old_time time_since_last in
        (* Make sure we did not overflow *)
        if word.ltu old_time new_time then new_time else old_time
      ));;
      new_time ← reads (λ '(σ,g), σ.(world).(grove_node_tsc));
      ret $ Val $ (#(new_time: u64))
    | GetTimeRangeOp, LitV LitUnit =>
      time_since_last ← any u64;
      modify_g (set grove_global_time (λ old_time,
        let new_time := word.add old_time time_since_last in
        (* Make sure we did not overflow *)
        if Z.leb (word.unsigned old_time) (word.unsigned new_time) then new_time else old_time
      ));;
      low_time ← suchThat (gen:=fun _ _ => None) (λ '(σ,g) (low_time: u64),
         Z.leb (word.unsigned low_time) (word.unsigned g.(global_world).(grove_global_time)));
      high_time ← suchThat (gen:=fun _ _ => None) (λ '(σ,g) (high_time: u64),
         Z.leb (word.unsigned g.(global_world).(grove_global_time)) (word.unsigned high_time));
      ret $ Val $ PairV #(low_time:u64) #(high_time:u64)
    (* Everything else is UB *)
    | _, _ => undefined
    end.

  Local Instance grove_semantics : ffi_semantics grove_op grove_model :=
    { ffi_step := ffi_step;
      ffi_crash_step := eq; }. (* TSC and files are preserved on crash *)
End grove.

(** * Grove semantic interpretation and lifting lemmas *)
Class groveGS Σ : Set := GroveGS {
  groveG_net_heapG :> gen_heap.gen_heapGS chan (gset message) Σ;
  grove_time_name : gname;
  groveG_timeG :> mono_natG Σ;
}.

Class groveGpreS Σ : Set := {
  grove_preG_net_heapG :> gen_heap.gen_heapGpreS chan (gset message) Σ;
  grove_preG_files_heapG :> gen_heap.gen_heapGpreS string (list byte) Σ;
  grove_preG_tscG :> mono_natG Σ;
}.
Class groveNodeGS Σ : Set := GroveNodeGS {
  groveG_preS :> groveGpreS Σ;
  grove_tsc_name : gname;
  groveG_files_heapG :> gen_heap.gen_heapGS string (list byte) Σ;
}.

Definition groveΣ : gFunctors :=
  #[gen_heapΣ chan (gset message); gen_heapΣ string (list byte); mono_natΣ].

#[global]
Instance subG_groveGpreS Σ : subG groveΣ Σ → groveGpreS Σ.
Proof. solve_inG. Qed.

Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
  Existing Instances grove_op grove_model.

  Local Definition data_vals (data : list u8) : list val :=
    ((λ b, #(LitByte b)) <$> data).

  Definition chan_msg_bounds (g : gmap chan (gset message)) : Prop :=
    ∀ c ms m, g !! c = Some ms → m ∈ ms → length m.(msg_data) < 2^64.

  Definition file_content_bounds (g : gmap string (list byte)) : Prop :=
    ∀ f c, g !! f = Some c → length c < 2^64.

  Local Program Instance grove_interp: ffi_interp grove_model :=
    {| ffiGlobalGS := groveGS;
       ffiLocalGS := groveNodeGS;
       ffi_local_ctx _ _ σ :=
         (mono_nat_auth_own grove_tsc_name 1 (uint.nat σ.(grove_node_tsc)) ∗
          ⌜file_content_bounds σ.(grove_node_files)⌝ ∗ gen_heap_interp σ.(grove_node_files))%I;
       ffi_global_ctx _ _ g :=
         (gen_heap_interp g.(grove_net) ∗ ⌜chan_msg_bounds g.(grove_net)⌝ ∗
          mono_nat_auth_own grove_time_name 1 (uint.nat g.(grove_global_time))
         )%I;
       ffi_local_start _ _ σ :=
         ([∗ map] f↦c ∈ σ.(grove_node_files), (pointsto (L:=string) (V:=list byte) f (DfracOwn 1) c))%I;
       ffi_global_start _ _ g :=
         ([∗ map] e↦ms ∈ g.(grove_net), (pointsto (L:=chan) (V:=gset message) e (DfracOwn 1) ms))%I;
       ffi_restart _ _ _ := True%I;
      ffi_crash_rel Σ hF1 σ1 hF2 σ2 :=
        (* TODO: you could also assume the tsc is non-decreasing across a crash *)
       ⌜ hF1 = hF2 ∧ σ1.(grove_node_files) = σ2.(grove_node_files) ⌝%I;
    |}.
End grove.

Notation "c c↦ ms" := (pointsto (L:=chan) (V:=gset message) c (DfracOwn 1) ms)
                       (at level 20, format "c  c↦  ms") : bi_scope.

Notation "s f↦{ q } c" := (pointsto (L:=string) (V:=list byte) s q c)
                            (at level 20, q at level 50, format "s  f↦{ q } c") : bi_scope.

Notation "s f↦ c" := (s f↦{DfracOwn 1} c)%I
                       (at level 20, format "s  f↦ c") : bi_scope.

Section lifting.
  Existing Instances grove_op grove_model grove_semantics grove_interp.
  Context `{!gooseGlobalGS Σ, !gooseLocalGS Σ}.
  Local Instance goose_groveGS : groveGS Σ := goose_ffiGlobalGS.
  Local Instance goose_groveNodeGS : groveNodeGS Σ := goose_ffiLocalGS.

  Definition chan_meta_token (c : chan) (E: coPset) : iProp Σ :=
    gen_heap.meta_token (hG := groveG_net_heapG) c E.
  Definition chan_meta `{Countable A} (c : chan) N (x : A) : iProp Σ :=
    gen_heap.meta (hG := groveG_net_heapG) c N x.

  (** "The TSC is at least" *)
  Definition tsc_lb (time : nat) : iProp Σ :=
    mono_nat_lb_own grove_tsc_name time.

  (* FIXME: have to manually put some of this stuff here because of two mono_natG's in context *)
  Definition is_time_lb (t:u64) := @mono_nat_lb_own Σ (goose_groveGS.(groveG_timeG)) grove_time_name (uint.nat t).
  Definition own_time (t:u64) := @mono_nat_auth_own Σ (goose_groveGS.(groveG_timeG)) grove_time_name 1 (uint.nat t).

  Lemma own_time_get_lb t :
    own_time t -∗ is_time_lb t.
  Proof.
    rewrite /own_time /is_time_lb. destruct goose_groveGS.
    iApply mono_nat_lb_own_get.
  Qed.

  Lemma is_time_lb_mono t t':
    uint.nat t <= uint.nat t' →
    is_time_lb t' -∗ is_time_lb t.
  Proof.
    rewrite /own_time /is_time_lb. destruct goose_groveGS.
    intros.
    iApply mono_nat_lb_own_le.
    word.
  Qed.

  Definition connection_socket (c_l : chan) (c_r : chan) : val :=
    ExtV (ConnectionSocketV c_l c_r).
  Definition listen_socket (c : chan) : val :=
    ExtV (ListenSocketV c).
  Definition bad_socket : val :=
    ExtV BadSocketV.

  (* Lifting automation *)
  Local Hint Extern 0 (base_reducible _ _ _) => eexists _, _, _, _, _; simpl : core.
  Local Hint Extern 0 (base_reducible_no_obs _ _ _) => eexists _, _, _, _; simpl : core.
  (** The tactic [inv_base_step] performs inversion on hypotheses of the shape
[base_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
  Ltac inv_base_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : base_step_atomic _ _ _ _ _ _ _ _ |- _ =>
          apply base_step_atomic_inv in H; [ | by inversion 1 ]
        | H : base_step ?e _ _ _ _ _ _ _ |- _ =>
          rewrite /base_step /= in H;
          monad_inv; repeat (simpl in H; monad_inv)
        | H : ffi_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        end.

  Lemma wp_ListenOp c s E :
    {{{ True }}}
      ExternalOp ListenOp (LitV $ LitInt c) @ s; E
    {{{ RET listen_socket c; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /base_step/=.
      monad_simpl. }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    inv_base_step.
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
    iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /base_step/=.
      monad_simpl. econstructor.
      { econstructor. eapply gen_isFreshChan. }
      monad_simpl. econstructor; first by econstructor.
      monad_simpl.
    }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    iDestruct "Hg" as "((Hg & %Hg & ?)&?)".
    inv_base_step.
    match goal with
    | H : isFreshChan _ ?c |- _ => rename H into Hfresh; rename c into c_l
    end.
    destruct c_l as [c_l|]; last first.
    { (* Failed to pick a fresh channel. *)
      monad_inv. simpl. iFrame. iModIntro.
      do 2 (iSplit; first done).
      iApply ("HΦ" $! true (W64 0)). done. }
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
    iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /base_step/=.
      monad_simpl. econstructor.
      1:by eapply (relation.suchThat_runs _ _ (W64 0)).
      monad_simpl. }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    inv_base_step.
    simpl.
    iFrame.
    iIntros "!>".
    iSplit; first done.
    by iApply "HΦ".
  Qed.

  Lemma pointsto_vals_bytes_valid l (data : list u8) q (σ : gmap _ _) :
    na_heap.na_heap_ctx tls σ -∗ pointsto_vals l q (data_vals data) -∗
    ⌜ (forall (i:Z), (0 <= i)%Z -> (i < length data)%Z ->
              match σ !! (l +ₗ i) with
           | Some (Reading _, LitV (LitByte v)) => data !! Z.to_nat i = Some v
           | _ => False
              end) ⌝.
  Proof.
    iIntros "Hh Hv". iDestruct (pointsto_vals_valid with "Hh Hv") as %Hl.
    iPureIntro. intros i Hlb Hub.
    rewrite fmap_length in Hl. specialize (Hl _ Hlb Hub).
    destruct (σ !! (l +ₗ i)) as [[[] v]|]; [done| |done].
    move: Hl. rewrite list_lookup_fmap /=.
    intros [b [? ->]]%fmap_Some_1. done.
  Qed.

  Lemma wp_SendOp c_l c_r ms (l : loc) (len : u64) (data : list u8) (q : dfrac) s E :
    length data = uint.nat len →
    {{{ c_r c↦ ms ∗ pointsto_vals l q (data_vals data) }}}
      ExternalOp SendOp (connection_socket c_l c_r, (#l, #len))%V @ s; E
    {{{ (err_early err_late : bool), RET #(err_early || err_late);
       c_r c↦ (if err_early then ms else ms ∪ {[Message c_l data]}) ∗
       pointsto_vals l q (data_vals data) }}}.
  Proof.
    iIntros (Hmlen Φ) "[Hc Hl] HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hw&Htr) Hg".
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    iDestruct "Hg" as "((Hg & %Hg & ?)&?)".
    iDestruct (@gen_heap_valid with "Hg Hc") as %Hc.
    iDestruct (pointsto_vals_bytes_valid with "Hσ Hl") as %Hl.
    iModIntro.
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /base_step/=.
      monad_simpl. econstructor. 1:by eapply (relation.suchThat_runs _ _ true).
      monad_simpl. econstructor; first by econstructor.
      monad_simpl.
    }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    inv_base_step.
    rename x into err_early. clear H.
    destruct err_early.
    { monad_inv. iFrame. iModIntro.
      do 2 (iSplitR; first done).
      iApply ("HΦ" $! true true). by iFrame. }
    inv_base_step.
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
      opose proof (Hl i _ _) as Hl; [lia..|].
      opose proof (Hm0 i _ _) as Hm0; [lia..|].
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

  Lemma wp_RecvOp c_l c_r ms s E :
    {{{ c_l c↦ ms }}}
      ExternalOp RecvOp (connection_socket c_l c_r) @ s; E
    {{{ (err : bool) (l : loc) (len : u64) (data : list u8),
        RET (#err, (#l, #len));
        ⌜if err then l = null ∧ data = [] ∧ len = 0 else
          Message c_r data ∈ ms ∧ length data = uint.nat len⌝ ∗
        c_l c↦ ms ∗ pointsto_vals l (DfracOwn 1) (data_vals data)
    }}}.
  Proof.
    iIntros (Φ) "He HΦ". iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hw&Htr) Hg".
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    iDestruct "Hg" as "((Hg & %Hg & ?)&?)".
    iModIntro.
    iDestruct (@gen_heap_valid with "Hg He") as %He.
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /base_step/=.
      monad_simpl. econstructor; first by econstructor.
      monad_simpl. econstructor.
      { constructor. left. done. }
      monad_simpl. econstructor.
      { econstructor. done. }
      monad_simpl.
    }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    inv_base_step.
    monad_inv.
    rename select (m = None ∨ _) into Hm. simpl in Hm.
    destruct Hm as [->|(m' & -> & Hm & <-)].
    { (* Returning no message. *)
      inv_base_step.
      monad_inv.
      iFrame. simpl. iModIntro. do 2 (iSplit; first done).
      iApply ("HΦ" $! true).
      iFrame; (iSplit; first done); rewrite /pointsto_vals big_sepL_nil //.
    }
    (* Returning a message *)
    repeat match goal with
           | H : relation.bind _ _ _ _ _ |- _ => simpl in H; monad_inv
           end.
    move: (Hg _ _ _ He Hm)=>Hlen.
    rename select (isFresh _ _) into Hfresh.
    iAssert (na_heap_ctx tls (heap_array l ((λ v : val, (Reading 0, v)) <$> data_vals m'.(msg_data)) ∪ σ1.(heap)) ∗
      [∗ list] i↦v ∈ data_vals m'.(msg_data), na_heap_pointsto (addr_plus_off l i) (DfracOwn 1) v)%I
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
    iApply ("HΦ" $! false _ _ m'.(msg_data)). iFrame "He".
    iSplit.
    { iPureIntro. split; first by destruct m'. word. }
    rewrite /pointsto_vals. iApply (big_sepL_mono with "Hl").
    clear -Hfresh. simpl. iIntros (i v _) "Hpointsto".
    iApply (na_pointsto_to_heap with "Hpointsto").
    destruct Hfresh as (Hfresh & _). eapply Hfresh.
  Qed.

  Lemma wp_FileReadOp (f : string) q c E :
    {{{ f f↦{q} c }}}
      ExternalOp FileReadOp #(str f) @ E
    {{{ (err : bool) (l : loc) (len : u64), RET (#err, (#l, #len));
      f f↦{q} c ∗ if err then True else ⌜length c = uint.nat len⌝ ∗ pointsto_vals l (DfracOwn 1) (data_vals c)
    }}}.
  Proof.
    iIntros (Φ) "Hf HΦ". iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hw&Htr) Hg".
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    iDestruct "Hw" as "(Htsc & %Hfilebound & Hfiles)".
    iDestruct (@gen_heap_valid with "Hfiles Hf") as %Hf.
    iModIntro. iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /base_step/=.
      monad_simpl. econstructor.
      1:by eapply (relation.suchThat_runs _ _ true). (* set early_err to true *)
      monad_simpl. econstructor.
      { constructor. done. }
      monad_simpl.
    }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    inv_base_step.
    rename x into err_early.
    destruct err_early.
    { monad_inv. iFrame. iModIntro. do 2 (iSplitR; first done).
      simpl. iApply "HΦ". by iFrame. }
    inv_base_step. monad_inv.
    move: (Hfilebound _ _ Hf)=>Hlen.
    rename select (isFresh _ _) into Hfresh.
    iAssert (na_heap_ctx tls (heap_array l ((λ v : val, (Reading 0, v)) <$> data_vals c) ∪ σ1.(heap)) ∗
      [∗ list] i↦v ∈ data_vals c, na_heap_pointsto (addr_plus_off l i) (DfracOwn 1) v)%I
      with "[> Hσ]" as "[Hσ Hl]".
    { destruct (decide (length c = 0%nat)) as [Heq%nil_length_inv|Hne].
      { (* Zero-length file... no actually new memory allocation, so the proof needs
           to work a bit differently. *)
        rewrite Heq big_sepL_nil fmap_nil /= left_id. by iFrame. }
      iMod (na_heap_alloc_list tls (heap σ1) l
                               (data_vals c)
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
    do 2 (iSplitR; first done).
    iApply "HΦ". iFrame "Hf".
    rewrite /pointsto_vals. iSplitR.
    { iPureIntro. word. }
    iApply (big_sepL_mono with "Hl").
    clear -Hfresh. simpl. iIntros (i v _) "Hpointsto".
    iApply (na_pointsto_to_heap with "Hpointsto").
    destruct Hfresh as (Hfresh & _). eapply Hfresh.
  Qed.

  Lemma wp_FileWriteOp (f : string) old new l q (len : u64) E :
    length new = uint.nat len →
    {{{ f f↦ old ∗ pointsto_vals l q (data_vals new) }}}
      ExternalOp FileWriteOp (#(str f), (#l, #len))%V @ E
    {{{ (err : bool), RET #err; f f↦ (if err then old else new) ∗ pointsto_vals l q (data_vals new) }}}.
  Proof.
    iIntros (Hmlen Φ) "[Hf Hl] HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hw&Htr) Hg".
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    iDestruct "Hw" as "(Htsc & %Hfilebound & Hfiles)".
    iDestruct (@gen_heap_valid with "Hfiles Hf") as %Hf.
    iDestruct (pointsto_vals_bytes_valid with "Hσ Hl") as %Hl.
    iModIntro. iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /base_step/=.
      monad_simpl. econstructor.
      1:by eapply (relation.suchThat_runs _ _ true). (* set early_err to true *)
      monad_simpl. econstructor.
      { econstructor. done. }
      monad_simpl.
    }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    inv_base_step.
    rename x into err_early.
    destruct err_early.
    { monad_inv. iFrame. do 2 (iSplitR; first done). simpl. iApply "HΦ". by iFrame. }
    inv_base_step. monad_inv.
    iFrame.
    iMod (@gen_heap_update with "Hfiles Hf") as "[$ Hf]".
    assert (data = new) as <-.
    { apply list_eq=>i.
      rename select (length _ = _ ∧ _) into Hm0. destruct Hm0 as [Hm0len Hm0].
      assert (length new = length data) as Hlen by rewrite Hmlen //.
      destruct (data !! i) as [v|] eqn:Hm; last first.
      { move: Hm. rewrite lookup_ge_None -Hlen -lookup_ge_None. done. }
      rewrite -Hm. apply lookup_lt_Some in Hm. apply inj_lt in Hm.
      opose proof (Hl i _ _) as Hl; [lia..|].
      opose proof (Hm0 i _ _) as Hm0; [lia..|].
      destruct (σ1.(heap) !! (l +ₗ i)) as [[[] v'']|]; try done.
      destruct v'' as [lit| | | | |]; try done.
      destruct lit; try done.
      rewrite Nat2Z.id in Hl Hm0. rewrite Hl -Hm0. done. }
    iIntros "!> /=".
    iSplit; first done. iSplitR.
    { iPureIntro. clear -Hmlen Hfilebound.
      intros f' c'. destruct (decide (f = f')) as [<-|Hne].
      - rewrite lookup_insert=>-[<-]. word.
      - rewrite lookup_insert_ne //. eapply Hfilebound. } 
    iApply "HΦ".
    by iFrame.
  Qed.

  Lemma wp_FileAppendOp (f : string) old new l q (len : u64) E :
    length new = uint.nat len →
    {{{ f f↦ old ∗ pointsto_vals l q (data_vals new) }}}
      ExternalOp FileAppendOp (#(str f), (#l, #len))%V @ E
    {{{ (err : bool), RET #err; f f↦ (if err then old else (old ++ new)) ∗ pointsto_vals l q (data_vals new) }}}.
  Proof.
    iIntros (Hmlen Φ) "[Hf Hl] HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hw&Htr) Hg".
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    iDestruct "Hw" as "(Htsc & %Hfilebound & Hfiles)".
    iDestruct (@gen_heap_valid with "Hfiles Hf") as %Hf.
    iDestruct (pointsto_vals_bytes_valid with "Hσ Hl") as %Hl.
    iModIntro. iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /base_step/=.
      monad_simpl. econstructor.
      1:by eapply (relation.suchThat_runs _ _ true). (* set early_err to true *)
      monad_simpl. econstructor.
      { econstructor. done. }
      monad_simpl.
    }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    inv_base_step.
    rename x into err_early.
    destruct err_early.
    { monad_inv. iFrame. do 2 (iSplitR; first done). simpl. iApply "HΦ". by iFrame. }
    inv_base_step. monad_inv.
    iFrame.
    case_bool_decide.
    { monad_inv. iFrame. do 2 (iSplitR; first done). simpl. iApply "HΦ". by iFrame. }
    inv_base_step. monad_inv. iFrame.
    rename select (¬ length _ >= _) into Halen.
    iMod (@gen_heap_update with "Hfiles Hf") as "[$ Hf]".
    assert (data = new) as <-.
    { apply list_eq=>i.
      rename select (length _ = _ ∧ _) into Hm0. destruct Hm0 as [Hm0len Hm0].
      assert (length new = length data) as Hlen by rewrite Hmlen //.
      destruct (data !! i) as [v|] eqn:Hm; last first.
      { move: Hm. rewrite lookup_ge_None -Hlen -lookup_ge_None. done. }
      rewrite -Hm. apply lookup_lt_Some in Hm. apply inj_lt in Hm.
      opose proof (Hl i _ _) as Hl; [lia..|].
      opose proof (Hm0 i _ _) as Hm0; [lia..|].
      destruct (σ1.(heap) !! (l +ₗ i)) as [[[] v'']|]; try done.
      destruct v'' as [lit| | | | |]; try done.
      destruct lit; try done.
      rewrite Nat2Z.id in Hl Hm0. rewrite Hl -Hm0. done. }
    iIntros "!> /=".
    iSplit; first done. iSplitR.
    { iPureIntro. clear -Halen Hfilebound.
      intros f' c'. destruct (decide (f = f')) as [<-|Hne].
      - rewrite lookup_insert=>-[<-]. word.
      - rewrite lookup_insert_ne //. eapply Hfilebound. } 
    iApply "HΦ".
    by iFrame.
  Qed.

  Lemma wp_GetTscOp prev_time s E :
    {{{ tsc_lb prev_time }}}
      ExternalOp GetTscOp #() @ s; E
    {{{ (new_time: u64), RET #new_time;
      ⌜prev_time ≤ uint.nat new_time⌝ ∗ tsc_lb (uint.nat new_time)
    }}}.
  Proof.
    iIntros (Φ) "Hprev HΦ". iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hw&Htr) Hg !>".
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /base_step/=.
      monad_simpl. econstructor.
      1:by eapply (relation.suchThat_runs _ _ (W64 0)).
      monad_simpl. }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    inv_base_step. iFrame. simpl.
    iSplitR; first done.
    iDestruct "Hw" as "[Htsc Hfiles]".
    set old := σ1.(world).(grove_node_tsc).
    iDestruct (mono_nat_lb_own_valid with "Htsc Hprev") as %[_ Hlb].
    iClear "Hprev".
    evar (new: u64).
    assert (uint.nat old <= uint.nat new) as Hupd.
    2: iMod (mono_nat_own_update (uint.nat new) with "Htsc") as "[Htsc Hnew]"; first lia.
    2: subst new; iFrame "Htsc Hfiles".
    { subst new. rewrite word.unsigned_ltu. clear.
      destruct (_ <? _)%Z eqn:Hlt; last by word.
      (* FIXME Why can word not do this? *)
      apply Zlt_is_lt_bool in Hlt.
      apply Z2Nat.inj_le; [word..|].
      lia. }
    iApply "HΦ". iFrame. iPureIntro. lia.
  Qed.

  Lemma wp_GetTimeRangeOp s E :
   ∀ Φ, (∀ (l h t:u64), ⌜uint.nat t <= uint.nat h⌝ -∗ ⌜uint.nat l <= uint.nat t⌝ -∗
                  own_time t -∗ |NC={E}=> (own_time t ∗ Φ (#l, #h)%V)) -∗
   WP ExternalOp GetTimeRangeOp #() @ s; E {{ Φ }}.
  Proof.
    iIntros (Φ) "HΦ". iApply wp_lift_atomic_base_step_no_fork_nc; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    iSplit.
    { iPureIntro. eexists _, _, _, _, _; simpl.
      econstructor. rewrite /base_step/=.
      monad_simpl.
      econstructor.
      1:by eapply (relation.suchThat_runs _ _ (W64 0)).
      monad_simpl.
      econstructor.
      1: {
        eapply (relation.suchThat_runs _ _ (W64 0)).
        apply Is_true_true_2.
        word.
      }
      monad_simpl.
      econstructor.
      {
        eapply (relation.suchThat_runs _ _ (W64 (2^64-1))).
        apply Is_true_true_2.
        word.
      }
      monad_simpl.
    }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    inv_base_step.
    simpl.
    iFrame.
    iSplitR; first done.
    iDestruct "Hg" as "((? & %Hg & Ht)&?)".
    iMod (mono_nat_own_update with "Ht") as "[Ht _]".
    {
      instantiate (1:=(uint.nat ((if
           uint.Z g1.(global_world).(grove_global_time) <=?
           uint.Z (word.add g1.(global_world).(grove_global_time) x)
          then word.add g1.(global_world).(grove_global_time) x
          else g1.(global_world).(grove_global_time))))).
      destruct (Z.leb (uint.Z _) (uint.Z (word.add _ _))) eqn:Hlt.
      {
        rewrite Z.leb_le in Hlt.
        apply Z2Nat.inj_le; [try word..|].
        { apply word.unsigned_range. }
        done.
      }
      { word. }
    }
    iMod ("HΦ" $! low_time high_time _ with "[] [] Ht") as "[Ht HΦ]".
    { iPureIntro.
      apply Is_true_true_1 in H1. rewrite Z.leb_le in H1.
      by do 2 rewrite u64_Z_through_nat.
    }
    { iPureIntro.
      apply Is_true_true_1 in H0. rewrite Z.leb_le in H0.
      by do 2 rewrite u64_Z_through_nat.
    }
    iModIntro.
    iFrame "HΦ".
    by iFrame.
  Qed.

  Lemma wp_time_acc e s E Φ:
  goose_lang.(language.to_val) e = None →
   (∀ t, own_time t ={E}=∗ own_time t ∗ WP e @ s; E {{ Φ }}) -∗
   WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "Hacc_wp".
    wp_apply wp_acc_global_state_interp.
    { rewrite H. done. }
    iIntros (?????) "[(? & ? & Ht) ?]".
    unfold own_time.
    iMod ("Hacc_wp" with "Ht") as "[Ht Hacc_wp]".
    by iFrame.
  Qed.

End lifting.

(** * Grove user-facing operations and their specs *)
Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
  (* FIXME: figure out which of these clients need to set *)
  Existing Instances grove_op grove_model grove_ty grove_semantics grove_interp goose_groveGS goose_groveNodeGS.
  Local Coercion Var' (s:string) : expr := Var s.

  (** [extT] have size 1 so this fits with them being pointers in Go. *)
  Definition Listener : ty := extT GroveListenTy.
  Definition Connection : ty := extT GroveConnectionTy.
  Definition Address : ty := uint64T.

  Definition ConnectRet := (struct.decl [
                              "Err" :: boolT;
                              "Connection" :: Connection
                            ])%struct.

  Definition ReceiveRet := (struct.decl [
                              "Err" :: boolT;
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

  (** Type: func(Connection) (bool, []byte) *)
  Definition Receive : val :=
    λ: "e",
      let: "r" := ExternalOp RecvOp "e" in
      let: "err" := Fst "r" in
      let: "slice" := Snd "r" in
      let: "ptr" := Fst "slice" in
      let: "len" := Snd "slice" in
      struct.mk ReceiveRet [
        "Err" ::= "err";
        "Data" ::= ("ptr", "len", "len")
      ].

  (** FileRead pretends that the operation can never fail.
      The Go implementation will accordingly abort the program if an I/O error occurs. *)
  Definition FileRead : val :=
    λ: "f",
      let: "ret" := ExternalOp FileReadOp "f" in
      let: "err" := Fst "ret" in
      let: "slice" := Snd "ret" in
      if: "err" then control.impl.Exit #() else
      let: "ptr" := Fst "slice" in
      let: "len" := Snd "slice" in
      ("ptr", "len", "len").

  (** FileWrite pretends that the operation can never fail.
      The Go implementation will accordingly abort the program if an I/O error occurs. *)
  Definition FileWrite : val :=
    λ: "f" "c",
      let: "err" := ExternalOp FileWriteOp ("f", (slice.ptr "c", slice.len "c")) in
      if: "err" then control.impl.Exit #() else
      #().

  (** FileAppend pretends that the operation can never fail.
      The Go implementation will accordingly abort the program if an I/O error occurs. *)
  Definition FileAppend : val :=
    λ: "f" "c", 
      let: "err" := ExternalOp FileAppendOp ("f", (slice.ptr "c", slice.len "c")) in
      if: "err" then control.impl.Exit #() else
      #().

  (** Type: func() uint64 *)
  Definition GetTSC : val :=
    λ: <>, ExternalOp GetTscOp #().

  (** Type: func() (uint64, uint64) *)
  Definition GetTimeRange : val :=
    λ: <>, ExternalOp GetTimeRangeOp #().

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

  (* FIXME move the next 2 lemmas some place more general *)
  Lemma own_slice_small_byte_pointsto_vals (s : Slice.t) (data : list u8) (q : dfrac) :
    own_slice_small s byteT q data -∗ pointsto_vals (Slice.ptr s) q (data_vals data).
  Proof.
    rewrite /own_slice_small /slice.own_slice_small.
    iIntros "[Hs _]". rewrite /array.array /pointsto_vals.
    change (list.untype data) with (data_vals data).
    iApply (big_sepL_impl with "Hs"). iIntros "!#" (i v Hv) "Hl".
    move: Hv. rewrite /data_vals list_lookup_fmap.
    intros (b & _ & ->)%fmap_Some_1.
    rewrite byte_pointsto_untype byte_offset_untype //.
  Qed.

  Lemma pointsto_vals_own_slice_small_byte (s : Slice.t) (data : list u8) (q : dfrac) :
    uint.Z s.(Slice.sz) ≤ uint.Z s.(Slice.cap) →
    length data = uint.nat (Slice.sz s) →
    pointsto_vals (Slice.ptr s) q (data_vals data) -∗
    own_slice_small s byteT q data.
  Proof.
    iIntros (? Hlen) "Hl". rewrite /own_slice_small /slice.own_slice_small. iSplit; last first.
    { iPureIntro. rewrite /list.untype fmap_length. auto. }
    rewrite /array.array /pointsto_vals.
    change (list.untype data) with (data_vals data).
    iApply (big_sepL_impl with "Hl"). iIntros "!#" (i v Hv) "Hl".
    move: Hv. rewrite /data_vals list_lookup_fmap.
    intros (b & _ & ->)%fmap_Some_1.
    rewrite byte_pointsto_untype byte_offset_untype //.
  Qed.

Ltac inv_undefined :=
  match goal with
  | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] =>
    destruct e; try (apply suchThat_false in H; contradiction)
  end.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
  [ apply heap_base_atomic; cbn [relation.denote base_trans]; intros * H;
    repeat inv_undefined;
    try solve [ apply atomically_is_val in H; auto ]
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].
Local Ltac solve_atomic2 :=
  solve_atomic;
  (* TODO(Joe): Cleanup *)
  repeat match goal with 
    | [ H: relation.denote _ ?s1 ?s2 ?v |- _ ] => inversion_clear H
    | _ => progress monad_inv
    | _ => case_match
    end; eauto.

  Lemma wp_Send c_l c_r (s : Slice.t) (data : list u8) (q : dfrac) :
    ⊢ {{{ own_slice_small s byteT q data }}}
      <<< ∀∀ ms, c_r c↦ ms >>>
        Send (connection_socket c_l c_r) (slice_val s) @ ∅
      <<< ∃∃ (msg_sent : bool),
        c_r c↦ (if msg_sent then ms ∪ {[Message c_l data]} else ms)
      >>>
      {{{ (err : bool), RET #err; ⌜if err then True else msg_sent⌝ ∗
        own_slice_small s byteT q data }}}.
  Proof.
    iIntros "!#" (Φ) "Hs HΦ". wp_lam. wp_let.
    wp_apply wp_slice_ptr.
    wp_apply wp_slice_len.
    wp_pures.
    iDestruct (own_slice_small_sz with "Hs") as "%Hlen".
    iDestruct (own_slice_small_wf with "Hs") as "%Hwf".
    rewrite difference_empty_L.
    iMod "HΦ" as (ms) "[Hc HΦ]".
    { solve_atomic2. }
    wp_apply (wp_SendOp with "[$Hc Hs]"); [done..| |].
    { iApply own_slice_small_byte_pointsto_vals. done. }
    iIntros (err_early err_late) "[Hc Hl]".
    iApply ("HΦ" $! (negb err_early) with "[Hc]").
    { by destruct err_early. }
    iSplit.
    - iPureIntro. by destruct err_early, err_late.
    - iApply pointsto_vals_own_slice_small_byte; done.
  Qed.

  Lemma wp_Receive c_l c_r :
    ⊢ <<< ∀∀ ms, c_l c↦ ms >>>
        Receive (connection_socket c_l c_r) @ ∅
      <<< ∃∃ (err : bool) (data : list u8),
        c_l c↦ ms ∗ if err then True else ⌜Message c_r data ∈ ms⌝
      >>>
      {{{ (s : Slice.t),
        RET struct.mk_f ReceiveRet [
              "Err" ::= #err;
              "Data" ::= slice_val s
            ];
          own_slice s byteT (DfracOwn 1) data
      }}}.
  Proof.
    iIntros "!#" (Φ) "HΦ". wp_call. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iMod "HΦ" as (ms) "[Hc HΦ]".
    { solve_atomic2. }
    wp_apply (wp_RecvOp with "Hc").
    iIntros (err l len data) "(%Hm & Hc & Hl)".
    iMod ("HΦ" $! err data with "[Hc]") as "HΦ".
    { iFrame. destruct err; first done. iPureIntro. apply Hm. }
    iModIntro. wp_pures. iModIntro.
    destruct err.
    { iApply ("HΦ" $! (Slice.mk _ _ _)). simpl. destruct Hm as (-> & -> & ->).
      iApply own_slice_zero. }
    destruct Hm as [Hin Hlen].
    iApply ("HΦ" $! (Slice.mk _ _ _)).
    rewrite /own_slice.
    iSplitL.
    - iApply pointsto_vals_own_slice_small_byte; done.
    - iExists []. simpl. iSplit; first by eauto with lia.
      iApply array.array_nil. done.
  Qed.

  Lemma wpc_FileRead f dq c E :
    ⊢ {{{ f f↦{dq} c }}}
        FileRead #(str f) @ E
      {{{ (s : Slice.t), RET slice_val s; f f↦{dq} c ∗ own_slice s byteT (DfracOwn 1) c }}}
      {{{ f f↦{dq} c }}}.
  Proof.
    iIntros "!#" (Φ Φc) "Hf HΦ". wpc_call; first done.
    iCache with "HΦ Hf". { iApply "HΦ". done. }
    wpc_bind (ExternalOp _ _).
    iApply wpc_atomic.
    { solve_atomic2. }
    iSplit.
    { iApply "HΦ". done. }
    wp_apply (wp_FileReadOp with "Hf").
    iIntros (err l len) "(Hf & Hl)".
    iSplit; last first.
    { iApply "HΦ". done. }
    iModIntro.
    destruct err.
    { wpc_pures.
      wpc_frame. wp_apply wp_Exit. iIntros "?". done. }
    iDestruct "Hl" as "[%Hl Hl]".
    wpc_pures.
    iDestruct "HΦ" as "[_ HΦ]".
    iApply ("HΦ" $! (Slice.mk _ _ _)). iFrame. iModIntro.
    rewrite /own_slice.
    iSplitL.
    - iApply pointsto_vals_own_slice_small_byte; done.
    - iExists []. simpl. iSplit; first by eauto with lia.
      iApply array.array_nil. done.
  Qed.

  Lemma wpc_FileWrite f s q old data E :
    ⊢ {{{ f f↦ old ∗ own_slice_small s byteT q data }}}
        FileWrite #(str f) (slice_val s) @ E
      {{{ RET #(); f f↦ data ∗ own_slice_small s byteT q data }}}
      {{{ f f↦ old ∨ f f↦ data }}}.
  Proof.
    iIntros "!#" (Φ Φc) "[Hf Hs] HΦ".
    wpc_call. { by iLeft. } { by iLeft. }
    iCache with "HΦ Hf". { iApply "HΦ". by iLeft. }
    (* Urgh so much manual work just calling a WP lemma... *)
    wpc_pures. wpc_bind (slice.ptr _). wpc_frame. wp_apply wp_slice_ptr. iNamed 1.
    wpc_pures. wpc_bind (slice.len _). wpc_frame. wp_apply wp_slice_len. iNamed 1.
    wpc_pures.
    iDestruct (own_slice_small_sz with "Hs") as "%Hlen".
    iDestruct (own_slice_small_wf with "Hs") as "%Hwf".
    wpc_bind (ExternalOp _ _).
    iApply wpc_atomic.
    { solve_atomic2. }
    iSplit.
    { iApply "HΦ". by iLeft. }
    wp_apply (wp_FileWriteOp with "[$Hf Hs]"); [done..| |].
    { iApply own_slice_small_byte_pointsto_vals. done. }
    iIntros (err) "[Hf Hs]".
    iSplit; last first.
    { iApply "HΦ". destruct err; by eauto. }
    iModIntro. destruct err.
    { wpc_pures. wpc_frame. wp_apply wp_Exit. iIntros "?". done. }
    wpc_pures.
    { iApply "HΦ". eauto. }
    iApply "HΦ". iFrame.
    iApply pointsto_vals_own_slice_small_byte; done.
  Qed.

  Lemma wpc_FileAppend f s q old data E :
    ⊢ {{{ f f↦ old ∗ own_slice_small s byteT q data }}}
        FileAppend #(str f) (slice_val s) @ E
      {{{ RET #(); f f↦ (old ++ data) ∗ own_slice_small s byteT q data }}}
      {{{ f f↦ old ∨ f f↦ (old ++ data) }}}.
  Proof.
    iIntros "!#" (Φ Φc) "[Hf Hs] HΦ".
    wpc_call. { by iLeft. } { by iLeft. }
    iCache with "HΦ Hf". { iApply "HΦ". by iLeft. }
    (* Urgh so much manual work just calling a WP lemma... *)
    wpc_pures. wpc_bind (slice.ptr _). wpc_frame. wp_apply wp_slice_ptr. iNamed 1.
    wpc_pures. wpc_bind (slice.len _). wpc_frame. wp_apply wp_slice_len. iNamed 1.
    wpc_pures.
    iDestruct (own_slice_small_sz with "Hs") as "%Hlen".
    iDestruct (own_slice_small_wf with "Hs") as "%Hwf".
    wpc_bind (ExternalOp _ _).
    iApply wpc_atomic.
    { solve_atomic2. }
    iSplit.
    { iApply "HΦ". by iLeft. }
    wp_apply (wp_FileAppendOp with "[$Hf Hs]"); [done..| |].
    { iApply own_slice_small_byte_pointsto_vals. done. }
    iIntros (err) "[Hf Hs]".
    iSplit; last first.
    { iApply "HΦ". destruct err; eauto. }
    iModIntro. destruct err.
    { wpc_pures. wpc_frame. wp_apply wp_Exit. iIntros "?". done. }
    wpc_pures.
    { iApply "HΦ". eauto. }
    iApply "HΦ". iFrame.
    iApply pointsto_vals_own_slice_small_byte; done.
  Qed.

  Lemma wp_GetTSC :
  ⊢ <<< ∀∀ prev_time, tsc_lb prev_time >>>
      GetTSC #() @ ∅
    <<< ∃∃ (new_time: u64), ⌜prev_time ≤ uint.nat new_time⌝ ∗ tsc_lb (uint.nat new_time) >>>
    {{{ RET #new_time; True }}}.
  Proof.
    iIntros "!>" (Φ) "HAU". wp_lam.
    rewrite difference_empty_L.
    iMod "HAU" as (prev_time) "[Hlb HΦ]".
    { solve_atomic2. }
    wp_apply (wp_GetTscOp with "Hlb").
    iIntros (new_time) "[%Hprev Hlb]".
    iMod ("HΦ" with "[Hlb]") as "HΦ".
    { eauto with iFrame. }
    by iApply "HΦ".
  Qed.

  Lemma wp_GetTimeRange :
    ⊢ ∀ (Φ:goose_lang.val → iProp Σ),
    (∀ (l h t:u64), ⌜uint.nat t <= uint.nat h⌝ -∗ ⌜uint.nat l <= uint.nat t⌝ -∗
                    own_time t -∗ |NC={⊤}=> (own_time t ∗ Φ (#l, #h)%V)) -∗
  WP GetTimeRange #() {{ Φ }}.
  Proof.
    iIntros (?) "HΦ".
    wp_call. wp_apply (wp_GetTimeRangeOp with "HΦ").
  Qed.

  Lemma tsc_lb_0 :
    ⊢ |==> tsc_lb 0.
  Proof. iApply mono_nat_lb_own_0. Qed.

  Lemma tsc_lb_weaken t1 t2 :
    (t1 ≤ t2)%nat →
    tsc_lb t2 -∗ tsc_lb t1.
  Proof. intros. apply mono_nat_lb_own_le. done. Qed.
End grove.

From Perennial.goose_lang Require Import adequacy.

#[global]
Program Instance grove_interp_adequacy:
  @ffi_interp_adequacy grove_model grove_interp grove_op grove_semantics :=
  {| ffiGpreS := groveGpreS;
     ffiΣ := groveΣ;
     subG_ffiPreG := subG_groveGpreS;
     ffi_initgP := λ g, chan_msg_bounds g.(grove_net);
     ffi_initP := λ σ g, file_content_bounds σ.(grove_node_files);
  |}.
Next Obligation.
  rewrite //=. iIntros (Σ hPre g Hchan). eauto.
  iMod (gen_heap_init g.(grove_net)) as (names) "(H1&H2&H3)".
  iMod (mono_nat_own_alloc (uint.nat g.(grove_global_time))) as (?) "[Ht _]".
  iExists (GroveGS _ names _ _). iFrame. eauto.
Qed.
Next Obligation.
  rewrite //=.
  iIntros (Σ hPre σ ??).
  iMod (mono_nat_own_alloc (uint.nat σ.(grove_node_tsc))) as (tsc_name) "[Htsc _]".
  iMod (gen_heap_init σ.(grove_node_files)) as (names) "(H1&H2&_)".
  iExists (GroveNodeGS _ _ tsc_name _). eauto with iFrame.
Qed.
Next Obligation.
  iIntros (Σ σ σ' Hcrash Hold) "(Htsc_old & %Hfilebound & Hfiles_old)".
  simpl in Hold. destruct Hcrash.
  iExists Hold. iFrame. iPureIntro. done.
Qed.

Section crash.
  Existing Instances grove_op grove_model grove_ty.
  Existing Instances grove_semantics grove_interp.
  Existing Instance goose_groveNodeGS.

  Lemma file_pointsto_post_crash `{!heapGS Σ} f q v:
    f f↦{q} v ⊢@{_} post_crash (λ _, f f↦{q} v).
  Proof.
    iIntros "H". iIntros (???) "#Hrel".
    iDestruct "Hrel" as %(Heq1&Heq2).
    rewrite /goose_groveNodeGS.
    rewrite Heq1. eauto.
  Qed.

  Global Instance file_pointsto_crash `{!heapGS Σ} fname data q:
    IntoCrash (fname f↦{q} data)%I (λ hG, fname f↦{q} data)%I.
  Proof.
    apply file_pointsto_post_crash.
  Qed.

End crash.
