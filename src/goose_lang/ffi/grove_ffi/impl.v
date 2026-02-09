(** FFI module for distributed Perennial (Grove). Consist only of a network and
    per-node file storage. *)
From stdpp Require Import gmap vector fin_maps.
From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Import CountableTactics Transitions Integers ByteString.
From Perennial.goose_lang Require Import lang.

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

(** [endpoint] corresponds to a host-IP-pair *)
Definition endpoint := u64.
Inductive GroveVal :=
(** Corresponds to a 2-tuple. *)
| ListenSocketV (c : endpoint)
(** Corresponds to a 4-tuple. [c_l] is the local part, [c_r] the remote part. *)
| ConnectionSocketV (c_l : endpoint) (c_r : endpoint)
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

Record message := Message { msg_sender : endpoint; msg_data : list u8 }.
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
  grove_net: gmap endpoint (gset message);
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
  Context {go_gctx : GoGlobalContext}.

  Definition isFreshChan (fg : ffi_global_state) (c : option endpoint) : Prop :=
    match c with
    | None => True (* failure (to allocate a channel) is always an option *)
    | Some c => fg.(grove_net) !! c = None
    end.

  Definition gen_isFreshChan σg : isFreshChan σg None.
  Proof. rewrite /isFreshChan //. Defined.

  Local Definition modify_g (f : grove_global_state → grove_global_state) : transition (state*global_state) () :=
    modify (λ '(σ, g), (σ, set global_world f g)).

  Local Definition modify_n (f : grove_node_state → grove_node_state) : transition (state*global_state) () :=
    modify (λ '(σ, g), (set world f σ, g)).

  Local Definition is_grove_ffi_step (op : GroveOp) (v : val) (e' : expr)
    (σ σ' : ffi_state) (g g' : ffi_global_state) : Prop :=
    match op with
    (* Network *)
    | ListenOp =>
        σ = σ' ∧ g = g' ∧ (∀ c, v = #c → e' = (ExtV (ListenSocketV c)))
    | ConnectOp =>
        σ = σ' ∧
        (∀ c_l c_r,
           isFreshChan g c_l →
           match c_l with
           | None => g = g' ∧ e' = Val $ ((*err*)#true, ExtV BadSocketV)%V
           | Some c_l => g' = ((set grove_net <[ c_l := ∅ ]>) g) ∧
                        e' = ((*err*)#false, ExtV (ConnectionSocketV c_l c_r))%V
           end)
    | AcceptOp =>
        σ = σ' ∧ g = g' ∧ (∀ c_l c_r, v = ExtV (ListenSocketV c_l) →
                                      g = g' ∧ e' = Val $ (ExtV (ConnectionSocketV c_l c_r)))
    | SendOp =>
        σ = σ' ∧
        (∀ data c_l c_r (b : bool),
           v = (ExtV (ConnectionSocketV c_l c_r), #data)%V ∧
           match g.(grove_net) !! c_r with
           | Some ms => g' = (set grove_net <[ c_r := ms ∪ {[Message c_l data]} ]> g) ∧ e' = #b
           | _ => e' = Panic "invalid"
           end)
    | RecvOp =>
        σ = σ' ∧ g = g' ∧
        (∀ c_l c_r (err : bool),
           v = ExtV (ConnectionSocketV c_l c_r) ∧
           match g.(grove_net) !! c_l with
           | Some ms => (if err then e' = (#true, #(@nil w8))%V
                        else ∀ m, m ∈ ms → e' = (#false, #m)%V)
           | _ => e' = Panic "invalid"
           end)
    | FileReadOp =>
        σ = σ' ∧ g = g' ∧
        (∀ (name : go_string) (err : bool),
           v = #name ∧
           if err then e' = (#true, #(@nil w8))%V
           else match σ.(grove_node_files) !! name with
                | Some data => e' = (#true, #data)%V
                | _ => e' = Panic "invalid"
                end)
    | FileWriteOp =>
        g = g' ∧
        (∀ (name : go_string) (data : list w8),
           v = (#name, #data)%V ∧ e' = #() ∧
           σ' = (set grove_node_files <[ name := data ]> σ))
    | FileAppendOp =>
        g = g' ∧
        (∀ (name : go_string) (data : list w8),
           v = (#name, #data)%V ∧
           match σ.(grove_node_files) !! name with
           | Some old =>
               σ' = (set grove_node_files <[ name := old ++ data ]> σ) ∧ e' = #()
           | _ => e' = Panic "invalid"
           end)
    | GetTscOp =>
        g = g' ∧
        (∀ (new_time : w64),
           sint.nat σ.(grove_node_tsc) ≤ sint.nat new_time →
           σ' = set grove_node_tsc (const new_time) σ ∧ e' = #new_time)
    | GetTimeRangeOp =>
        σ = σ' ∧
        (∀ (new_time low high : w64),
           sint.nat g.(grove_global_time) ≤ sint.nat new_time →
           sint.nat low ≤ sint.nat new_time ≤ sint.nat high →
           g' = set grove_global_time (const new_time) g ∧
           e' = (#low, #high)%V
        )
    end.

  Definition ffi_step (op : GroveOp) (v : val) : transition (state*global_state) expr :=
    '(e', s', w') ← suchThat
      (λ '(σ, g) '(e', σ', w'),
         let _ := σ.(go_state).(go_lctx) in
         let w := g.(global_world) in
         is_grove_ffi_step op v e' σ.(world) σ' g.(global_world) w')
      (gen:=fallback_genPred _);
  modify (λ '(σ, g), (set world (const s') σ, set global_world (const w') g));;
  ret e'.


  Local Instance grove_semantics : ffi_semantics grove_op grove_model :=
    { ffi_step := ffi_step;
      ffi_crash_step := eq; }. (* TSC and files are preserved on crash *)
End grove.
