From New.proof Require Import proof_prelude.
From iris.base_logic.lib Require Import saved_prop.
From iris.algebra Require Import auth gset.
Require Import New.proof.sync.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.

(* Inductive mathematical representation *)
Module chan_state.
  
  (* Core channel states *)
  Inductive BufferedChannel (V : Type) : Type :=
  | Buffer : list V -> nat -> BufferedChannel V.
  
  Inductive UnbufferedChannel (V : Type) : Type :=
  | Idle : UnbufferedChannel V
  | SndWait : V -> UnbufferedChannel V  (* Blocking Sender arrives first *)
  | RcvWait : UnbufferedChannel V       (* Blocking Receiver arrives first *)
  | SndDone : V -> UnbufferedChannel V  (* Sender completes exch *)
  | RcvDone : UnbufferedChannel V.      (* Receiver completes exch *)
  
  (* Sum type for either buffered or unbuffered *)
  Inductive ChannelType (V : Type) : Type :=
  | Buffered : BufferedChannel V -> ChannelType V
  | Unbuffered : UnbufferedChannel V -> ChannelType V.
  
  (* Sum type for not-yet-closed or closed *)
  Inductive Channel (V : Type) : Type :=
  | Open : ChannelType V -> Channel V
  | Closed : Channel V.
  
  (* Global Arguments for clean syntax *)
  Global Arguments Buffer {V}.
  Global Arguments Idle {V}.
  Global Arguments SndWait {V}.
  Global Arguments RcvWait {V}.
  Global Arguments SndDone {V}.
  Global Arguments RcvDone {V}.
  Global Arguments Buffered {V}.
  Global Arguments Unbuffered {V}.
  Global Arguments Open {V}.
  Global Arguments Closed {V}.
  
  (* Helper functions for protocol development *)
  Definition is_buffered {V} (c : Channel V) : Prop :=
    match c with
    | Open (Buffered _) => True
    | _ => False
    end.
    
  Definition is_unbuffered {V} (c : Channel V) : Prop :=
    match c with
    | Open (Unbuffered _) => True
    | _ => False
    end.
    
  Definition is_open {V} (c : Channel V) : Prop :=
    match c with
    | Open _ => True
    | Closed => False
    end.

End chan_state.

(* Ghost state management *)
Record chan_names := {
  offer_name : gname;   (* For unbuffered offer/accept protocol *)
  state_name : gname;   (* For the main channel state *)
}.

Class chanGhostStateG Σ V := ChanGhostStateG {
  offer_tokG :: ghost_varG Σ (option V);
  chan_stateG :: ghost_varG Σ (chan_state.Channel V);
}.

Definition chanGhostStateΣ V : gFunctors :=
  #[ ghost_varΣ (option V); ghost_varΣ (chan_state.Channel V) ].

#[global] Instance subG_chanGhostStateG Σ V :
  subG (chanGhostStateΣ V) Σ → chanGhostStateG Σ V.
Proof. solve_inG. Qed.

Section base.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!goGlobalsGS Σ}.  
Context `{!chanGhostStateG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

(* Package initialization from chan_init.v *)
Local Notation deps := (ltac2:(build_pkg_init_deps 'channel) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit channel :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.
  
  (* Offer tokens for unbuffered channels *)
  Definition idle_tok (γ : gname) : iProp Σ :=
    ghost_var γ 1%Qp None.
  
  (* Send offer is outgoing, we can unlock the channel and know that the channel was
  untouched other then by a receiver accepting the offer *)
  Definition snd_wait_tok (γ : gname) (v: V) : iProp Σ :=
    ghost_var γ (1/2%Qp) (Some v).

  (* Almost symmetric to snd_wait_tok, but we don't need to encode a value *)
  Definition rcv_wait_tok (γ : gname) : iProp Σ :=
    ghost_var γ (1/2%Qp) None.
    
  (* Main channel state authoritative/fragment copies *)
  Definition chan_state_auth (γ : gname) (s : chan_state.Channel V) : iProp Σ :=
    ghost_var γ (1/2%Qp) s.
  Definition chan_state_frag (γ : gname) (s : chan_state.Channel V) : iProp Σ :=
    ghost_var γ (1/2%Qp) s.
  (* Full ownership, allows us to:
     1. Use a buffered channel as a single threaded queue with typical queue specs
     2. Persistently know a channel is closed
  *)
  Definition chan_state_full (γ : gname) (s : chan_state.Channel V) : iProp Σ :=
    ghost_var γ (1%Qp) s.

(* Physical state helper utility for the channel model that uses a simple blocking
   queue for buffered channels and an offer state machine for unbuffered channels
*)
  
  (* The unbuffered channel implementation uses a 4-state enum(including closed) 
     with the value pointer's nullity representing whether it is a receive offer/accept 
     or a send offer/accept.
  *)
  Definition encode_offer_state (s : chan_state.UnbufferedChannel V) : u64 :=
    match s with
    | chan_state.Idle => W64 0
    | chan_state.SndWait _ | chan_state.RcvWait => W64 1
    | chan_state.SndDone _ | chan_state.RcvDone => W64 2
    end.
  
  (* The state enum is used for closing only in buffered channels, this wraps the 
     shared state for buffered/unbuffered channels.
  *)
  Definition encode_channel_state (s : chan_state.Channel V) : u64 :=
    match s with
    (* Always idle/closed for buffered *) 
    | chan_state.Open (chan_state.Buffered _) => W64 0  
    | chan_state.Open (chan_state.Unbuffered ub) => encode_offer_state ub
    | chan_state.Closed => W64 3
    end.

  (* Helper for mathematically representing a go ptr as an option monad.
  *)
  Definition opt_mathrep_to_go_ptr_phys {V} `{!IntoVal V} `{!IntoValTyped V t} 
  (ub: chan_state.UnbufferedChannel V) (v_go_ptr: loc) : iProp Σ :=
   match ub with 
       | chan_state.SndWait v | chan_state.SndDone v => (v_go_ptr ↦ v)%I
       | _ => ⌜ v_go_ptr = null ⌝ 
       end.
  
  (* Physical heap predicates - what the mutex owns *)
  Definition chan_phys_buffered (ch: loc) (bc: chan_state.BufferedChannel V) 
      (slice_val: slice.t) : iProp Σ :=
    let (queue, cap) := match bc with chan_state.Buffer q c => (q, c) end in
    "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 0) ∗
    "slice" ∷ own_slice slice_val (DfracOwn 1) queue ∗
    "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val.

  Definition chan_phys_unbuffered (ch: loc) (ub: chan_state.UnbufferedChannel V) 
   : iProp Σ :=
    "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (encode_offer_state ub) ∗
    (∃ (v_go_ptr: loc),
    "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] v_go_ptr ∗ 
    "vptr" ∷ opt_mathrep_to_go_ptr_phys ub v_go_ptr).
       
  (* Once we are closed, we don't need to own physical state for internals, they 
     are effectively rendered useless.
  *)
  Definition chan_phys_closed (ch: loc): iProp Σ :=
    "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 3).
    
  (* Unified physical state predicate *)
  Definition chan_phys (ch: loc) (s: chan_state.Channel V) 
       : iProp Σ :=
    match s with
    (* Buffered, not yet closed *)
    | chan_state.Open (chan_state.Buffered bc) => 
        (∃ (slice_val: slice.t), chan_phys_buffered ch bc slice_val)
    (* Unbuffered, not yet closed *)
    | chan_state.Open (chan_state.Unbuffered ub) => 
        chan_phys_unbuffered ch ub
    | chan_state.Closed => 
        chan_phys_closed ch 
    end.

(* TODO: Add select physical state *)

(* Ownership *)

  (* Persistent capacity field - this is what allows clients to determine
     buffered vs unbuffered outside critical sections *)
  Definition chan_cap_persistent  (ch: loc) (s: chan_state.Channel V) : iProp Σ :=
    match s with
    | chan_state.Open (chan_state.Buffered (chan_state.Buffer _ cap)) =>
        "cap" ∷ ch ↦s[(channel.Channel.ty t) :: "cap"]□ (W64 cap)
    | chan_state.Open (chan_state.Unbuffered _) =>
        "cap" ∷ ch ↦s[(channel.Channel.ty t) :: "cap"]□ (W64 0)
    | chan_state.Closed => 
        (* Capacity remains readable even when closed. This is necessary to handle
           the conditional buff/unbuff logic in receive before observing closed.
        *)
        ∃ cap_val, "cap" ∷ ch ↦s[(channel.Channel.ty t) :: "cap"]□ (W64 cap_val)
    end.
  
  (* What goes inside the mutex invariant *)
  Definition chan_inv_inner (ch: loc) (γ: chan_names) : iProp Σ :=
    ∃ (s : chan_state.Channel V),
      "phys" ∷ chan_phys ch s ∗
      "auth" ∷ chan_state_auth γ.(state_name) s ∗
      (* Offer ghost state for unbuffered channels *)
      match s with
      | chan_state.Open (chan_state.Unbuffered ub) =>
          match ub with
          | chan_state.Idle => idle_tok γ.(offer_name)
          | chan_state.SndWait v => snd_wait_tok γ.(offer_name) v  
          | chan_state.RcvWait => rcv_wait_tok γ.(offer_name)
          | chan_state.SndDone v => snd_wait_tok γ.(offer_name) v
          | chan_state.RcvDone => rcv_wait_tok γ.(offer_name)
          end
      | _ => True  (* No offer tokens for buffered/closed *)
      end.
      
  (* Public channel interface - what clients see *)
  Definition is_channel (ch: loc) (γ: chan_names) : iProp Σ :=
    ∃ (mu_loc: loc) (s: chan_state.Channel V),
      "#mu" ∷ ch ↦s[(channel.Channel.ty t) :: "lock"]□ mu_loc ∗
      "#cap" ∷ chan_cap_persistent ch s ∗
      "#lock" ∷ is_Mutex mu_loc (chan_inv_inner ch γ).
      
  (* Fractional ownership for protocol development *)
  Definition own_channel (ch: loc) (s: chan_state.Channel V) (γ: chan_names) : iProp Σ :=
    chan_state_frag γ.(state_name) s.

(* Helper lemmas *)
  
  (* Persistence *)
  Global Instance is_channel_pers ch γ : Persistent (is_channel ch γ).
  Proof.
  Admitted.
  
  (* Timelessness *)
  Global Instance own_channel_timeless ch s γ : Timeless (own_channel ch s γ).
  Proof.
  Admitted.

  Lemma is_channel_not_null ch γ :
    is_channel ch γ -∗ ⌜ch ≠ null⌝.
  Proof.
  Admitted.
End base.



