From New.proof Require Import proof_prelude.
From iris.base_logic.lib Require Import saved_prop.
From iris.algebra Require Import auth gset.
Require Import New.proof.sync.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.

(* Inductive mathematical representation *)
Module chan_rep.
  
Inductive Channel (V : Type) : Type :=
| Buffered (buff : list V) (cap : nat)
| Idle
| SndWait (v : V)
| RcvWait  
| SndDone (v : V)
| RcvDone
| Closed (draining : list V) (cap : nat).
  
  (* Global Arguments for clean syntax *)
  Global Arguments Buffered {V}.
  Global Arguments Idle {V}.
  Global Arguments SndWait {V}.
  Global Arguments RcvWait {V}.
  Global Arguments SndDone {V}.
  Global Arguments RcvDone {V}.
  Global Arguments Buffered {V}.
  Global Arguments Closed {V}.

  Definition buffer_valid {V} (c : chan_rep.Channel V) : Prop :=
  match c with
  | chan_rep.Buffered buff cap =>
    length buff ≤ cap
  | chan_rep.Closed draining cap =>
    length draining ≤ cap
  | _ => True (* Invariant is vacuously true for unbuffered or empty closed states *)
  end.

End chan_rep.

(* Ghost state management *)
Record chan_names := {
  offer_name : gname;   (* For unbuffered offer/accept protocol *)
  state_name : gname;   (* For the main channel state *)
}.

Class chanGhostStateG Σ V := ChanGhostStateG {
  offer_tokG :: ghost_varG Σ (option V);
  chan_repG :: ghost_varG Σ (chan_rep.Channel V);
}.

Definition chanGhostStateΣ V : gFunctors :=
  #[ ghost_varΣ (option V); ghost_varΣ (chan_rep.Channel V) ].

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
  Definition chan_rep_auth (γ : gname) (s : chan_rep.Channel V) : iProp Σ :=
    ghost_var γ (1/2%Qp) s.
  Definition chan_rep_frag (γ : gname) (s : chan_rep.Channel V) : iProp Σ :=
    ghost_var γ (1/2%Qp) s.
  (* Full ownership, allows us to:
     1. Use a buffered channel as a single threaded queue with typical queue specs
     2. Persistently know a channel is closed
  *)
  Definition chan_rep_full (γ : gname) (s : chan_rep.Channel V) : iProp Σ :=
    ghost_var γ (1%Qp) s.

(* Physical state helper utility for the channel model that uses a simple blocking
   queue for buffered channels and an offer state machine for unbuffered channels
*)

  (* Unified physical state predicate *)
  Definition chan_phys (ch: loc) (s: chan_rep.Channel V) 
       : iProp Σ :=
    match s with
    | chan_rep.Closed [] cap => 
        "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 3)
    (* Buffered, not yet closed *)
    | chan_rep.Buffered buff cap | chan_rep.Closed buff cap => 
        ∃ (slice_val: slice.t),
        "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 0) ∗
        "slice" ∷ own_slice slice_val (DfracOwn 1) buff ∗
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    (* Unbuffered, not yet closed *)
    | chan_rep.Idle => 
      "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 0) ∗
      "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] null
    | chan_rep.SndWait v => 
      "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 1) ∗
      (∃ (v_go_ptr: loc),
      "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] v_go_ptr ∗ 
      "vptr" ∷ v_go_ptr ↦ v)
    | chan_rep.RcvWait => 
      "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 1) ∗
      "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] null
    | chan_rep.SndDone v => 
      "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 2) ∗
      (∃ (v_go_ptr: loc),
      "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] v_go_ptr ∗ 
      "vptr" ∷ v_go_ptr ↦ v)
    | chan_rep.RcvDone => 
      "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 2) ∗
      "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] null
    end.

(* TODO: Add select physical state *)

(* Ownership *)

  (* Persistent capacity field - this is what allows clients to determine
     buffered vs unbuffered outside critical sections *)
  Definition chan_cap_persistent  (ch: loc) (s: chan_rep.Channel V) : iProp Σ :=
    match s with
    | chan_rep.Buffered _ cap | chan_rep.Closed _ cap =>
        "cap" ∷ ch ↦s[(channel.Channel.ty t) :: "cap"]□ (W64 cap)
    | _ =>
        "cap" ∷ ch ↦s[(channel.Channel.ty t) :: "cap"]□ (W64 0)
    end.
  
  (* What goes inside the mutex invariant *)
  Definition chan_inv_inner (ch: loc) (γ: chan_names) : iProp Σ :=
    ∃ (s : chan_rep.Channel V),
      "phys" ∷ chan_phys ch s ∗
      "auth" ∷ chan_rep_auth γ.(state_name) s ∗
      (* Offer ghost state for unbuffered channels *)
      match s with
          | chan_rep.Idle => idle_tok γ.(offer_name)
          | chan_rep.SndWait v => snd_wait_tok γ.(offer_name) v  
          | chan_rep.RcvWait => rcv_wait_tok γ.(offer_name)
          | chan_rep.SndDone v => snd_wait_tok γ.(offer_name) v
          | chan_rep.RcvDone => rcv_wait_tok γ.(offer_name)
          | _ => True
      end.
      
  (* Public channel interface - what clients see *)
  Definition is_channel (ch: loc) (γ: chan_names) : iProp Σ :=
    ∃ (mu_loc: loc) (s: chan_rep.Channel V),
      "#mu" ∷ ch ↦s[(channel.Channel.ty t) :: "lock"]□ mu_loc ∗
      "#cap" ∷ chan_cap_persistent ch s ∗
      "#lock" ∷ is_Mutex mu_loc (chan_inv_inner ch γ).
      
  (* Fractional ownership for protocol development *)
  Definition own_channel (ch: loc) (s: chan_rep.Channel V) (γ: chan_names) : iProp Σ :=
    chan_rep_frag γ.(state_name) s ∗ ⌜ chan_rep.buffer_valid s ⌝.

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



