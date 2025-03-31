(** FFI module for distributed Perennial (Grove). Consist only of a network and
    per-node file storage. *)
From stdpp Require Import gmap vector fin_maps.
From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Import CountableTactics Transitions Integers ByteString.
From Perennial.goose_lang Require Import lang notation lib.control.impl.

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

(** [chan] corresponds to a host-IP-pair *)
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
  populate {| grove_net := ∅; grove_global_time := W64 0 |}.

(** The per-node state *)
Record grove_node_state : Type := {
  grove_node_tsc : u64;
  grove_node_files: gmap byte_string (list byte);
}.

Global Instance grove_node_state_settable : Settable _ :=
  settable! Build_grove_node_state <grove_node_tsc; grove_node_files>.

Global Instance grove_node_state_inhabited : Inhabited grove_node_state :=
  populate {| grove_node_tsc := W64 0; grove_node_files := ∅ |}.

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
            Z.of_nat (length data) = uint.Z len ∧ forall (i:Z), 0 <= i -> i < length data ->
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
            Z.of_nat (length data) = uint.Z len ∧ forall (i:Z), 0 <= i -> i < length data ->
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
            Z.of_nat (length data) = uint.Z len ∧ forall (i:Z), 0 <= i -> i < length data ->
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
        (* TODO: why does this use [word.ltu] rather than a [decide] over the Z values? *)
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
