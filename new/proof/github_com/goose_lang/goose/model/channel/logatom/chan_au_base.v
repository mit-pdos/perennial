From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_init.
From New.proof Require Import proof_prelude.
From New.golang.theory Require Import lock.
From iris.base_logic.lib Require Import saved_prop.
From iris.algebra Require Import auth gset.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.

(** The specification state for a channel. *)
Module chanstate.
Inductive t (V : Type) : Type :=
| Buffered (buff : list V)     (* Buffered channel with pending messages *)
| Idle                        (* Empty unbuffered channel, ready for operations *)
| SndPending (v : V)          (* Unbuffered channel with sender waiting *)
| RcvPending                 (* Unbuffered channel with receiver waiting *)
| SndCommit (v : V)           (* Sender committed, waiting for receiver to complete *)
| RcvCommit                  (* Receiver committed, waiting for sender to complete *)
| Closed (drain : list V)  (* Closed channel, possibly drain remaining messages *)
.
#[global] Instance witness V : Inhabited (t V) := populate!.

Global Arguments Buffered {V}.
Global Arguments Idle {V}.
Global Arguments SndPending {V}.
Global Arguments RcvPending {V}.
Global Arguments SndCommit {V}.
Global Arguments RcvCommit {V}.
Global Arguments Closed {V}.

End chanstate.

(** The state machine representation matching the model implementation.
    This is slightly different from the mathematical representation
    in that we don't go to the SndWait state logically until an offer
    is about to be accepted. *)
Inductive chan_phys_state (V : Type) : Type :=
| Buffered (buffer : list V)     (* Channel with buffered messages *)
| Idle                        (* Ready for operations *)
| SndWait (v : V)            (* Sender offers *)
| RcvWait                    (* Receiver offers *)
| SndDone (v : V)            (* Sender operation completed, handshake in progress *)
| RcvDone            (* Receiver operation completed, handshake in progress *)
| Closed (buffer : list V)  (* Closed channel *)
.

Global Arguments Idle {V}.
Global Arguments SndWait {V}.
Global Arguments RcvWait {V}.
Global Arguments SndDone {V}.
Global Arguments RcvDone {V}.
Global Arguments Closed {V}.
Global Arguments Buffered {V}.

(** The offer protocol coordinates handshakes between senders and receivers
    in unbuffered channels. An "offer" represents a pending operation that
    can be accepted by the other party. This ghost state ensures that
    an outstanding offer can only be accepted or left as-is for when we lock
    the channel to check the status. *)
Inductive offer_lock (V : Type) : Type :=
| Snd (v : V)                (* Sender has made an offer *)
| Rcv                        (* Receiver has made an offer *)
.

Global Arguments Snd {V}.
Global Arguments Rcv {V}.

(** Ghost names for tracking various aspects of channel state in the logic *)
Record chan_names := {
  state_name : gname;                    (* Main channel state *)
  offer_lock_name : gname;               (* Offer protocol lock *)
  offer_parked_prop_name : gname;        (* The saved prop that we can leave with the channel to support select *)
  offer_parked_pred_name : gname;        (* The saved continuation for receive, which is a predicate on v, ok *)
  offer_continuation_name : gname;       (* The continuation for send *)
  chan_cap : w64;                        (* The channel capacity *)
}.

Class chanG Σ V := ChanG {
  offerG :: ghost_varG Σ (chanstate.t V);
  offer_lockG :: ghost_varG Σ (option (offer_lock V));
  offer_parked_propG :: savedPropG Σ;
  offer_parked_predG :: savedPredG Σ (V * bool);
}.
Global Hint Mode chanG - + : typeclass_instances.
Local Hint Mode chanG - - : typeclass_instances.

Definition chanΣ V : gFunctors :=
  #[ ghost_varΣ (chanstate.t V); ghost_varΣ (option (offer_lock V));
     savedPropΣ; savedPredΣ  (V * bool) ].

#[global] Instance subG_chanG Σ V :
  subG (chanΣ V) Σ → chanG Σ V.
Proof. solve_inG. Qed.

Section au_defns.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  {sem : go.ChanSemantics}.

Context (ch : loc) (γ : chan_names) (V : Type) (v : V) `{!chanG Σ V}.
Context `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.

Definition chanstate (q : Qp) (s : chanstate.t V) : iProp Σ :=
  ghost_var γ.(state_name) q s.

Definition chan_cap_valid (s : chanstate.t V) (cap : Z) : Prop :=
  match s with
  | chanstate.Buffered buf =>
      (* Buffered is only used for buffered channels, and buffer size is bounded
      by capacity *)
      (length buf ≤ cap)%Z ∧ (0 < cap)
  | chanstate.Closed [] => (0 ≤ cap)
  | chanstate.Closed drain =>
      (* Draining closed channels are buffered channels, and draining elements
      are bounded by capacity *)
      (Z.of_nat (length drain) ≤ cap) ∧ (0 < cap)
  | _ => cap = 0                            (* All other states are unbuffered *)
  end.

(** Represents ownership of a channel with its logical state *)
Definition own_chan (s: chanstate.t V) : iProp Σ :=
  "Hchanrepfrag" ∷ chanstate (1/2) s ∗
  "%Hcapvalid" ∷ ⌜ chan_cap_valid s (sint.Z $ chan_cap γ) ⌝.

(** Inner atomic update for receive completion (second phase of handshake) *)
Definition recv_nested_au (Φ : V → bool → iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hocinner" ∷ own_chan s ∗
     "Hcontinner" ∷
    (match s with
    (* Case: Sender has committed, complete the exchange *)
    | chanstate.SndCommit v => own_chan chanstate.Idle ={∅,⊤}=∗ Φ v true
    (* Case: Channel is closed with no messages *)
    | chanstate.Closed [] => own_chan s ={∅,⊤}=∗ Φ (zero_val V) false
    | _ => True
    end).

(** Slow path receive: may need to block and wait *)
Definition recv_au (Φ : V → bool → iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_chan s ∗
     "Hcont" ∷
    (match s with
    (* Case: Sender is waiting, can complete immediately *)
    | chanstate.SndPending v =>
          own_chan chanstate.RcvCommit ={∅,⊤}=∗ Φ v true
    (* Case: Channel is idle, need to wait for sender *)
    | chanstate.Idle =>
          own_chan (chanstate.RcvPending) ={∅,⊤}=∗
              recv_nested_au Φ
    (* Case: Channel is closed *)
    | chanstate.Closed [] => own_chan s ={∅,⊤}=∗ Φ (zero_val V) false
    (* Case: Closed but still have values to drain *)
    | chanstate.Closed (v::rest) => (own_chan (chanstate.Closed rest) ={∅,⊤}=∗ Φ v true)
    (* Case: Buffered channel with values in buffer *)
    | chanstate.Buffered (v::rest) => (own_chan (chanstate.Buffered rest) ={∅,⊤}=∗ Φ v true)
    | _ => True
    end).

(** Fast path receive: immediate completion when possible *)
Definition nonblocking_recv_au (Φ : V → bool → iProp Σ) Φnotready : iProp Σ :=
  (|={⊤,∅}=>
     ▷∃ s, "Hoc" ∷ own_chan s ∗
           "Hcont" ∷
             match s with
             (* Case: Sender is waiting, can complete immediately *)
             | chanstate.SndPending v =>
                 own_chan chanstate.RcvCommit ={∅,⊤}=∗ Φ v true
             (* Case: Channel is closed *)
             | chanstate.Closed [] => own_chan s ={∅,⊤}=∗ Φ (zero_val V) false
             (* Case: Channel is closed but still has values to drain *)
             | chanstate.Closed (v::rest) => (own_chan (chanstate.Closed rest) ={∅,⊤}=∗ Φ v true)
             (* Case: Buffered channel with values *)
             | chanstate.Buffered (v::rest) => (own_chan (chanstate.Buffered rest) ={∅,⊤}=∗ Φ v true)
             | _ => True
             end) ∧
  Φnotready.

(** See [nonblocking_send_au_alt] documentation below.  *)
Definition nonblocking_recv_au_alt (Φ : V → bool → iProp Σ) Φnotready : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_chan s ∗
     "Hcont" ∷
    (match s with
    (* Case: Sender is waiting, can complete immediately *)
    | chanstate.SndPending v =>
          own_chan chanstate.RcvCommit ={∅,⊤}=∗ Φ v true
    (* Case: Channel is closed *)
    | chanstate.Closed [] => own_chan s ={∅,⊤}=∗ Φ (zero_val V) false
    (* Case: Channel is closed but still has values to drain *)
    | chanstate.Closed (v::rest) => (own_chan (chanstate.Closed rest) ={∅,⊤}=∗ Φ v true)
    (* Case: Buffered channel with values *)
    | chanstate.Buffered (v::rest) => (own_chan (chanstate.Buffered rest) ={∅,⊤}=∗ Φ v true)
    | _ => (own_chan s ={∅,⊤}=∗ Φnotready)
    end).

(** Inner atomic update for send completion (second phase of handshake) *)
Definition send_nested_au (Φ : iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hocinner" ∷ own_chan s ∗
     "Hcontinner" ∷
    (match s with
    (* Case: Receiver has committed, complete the exchange *)
    | chanstate.RcvCommit =>
           own_chan chanstate.Idle ={∅,⊤}=∗ Φ
    (* Case: Channel is closed, operation fails *)
    | chanstate.Closed drain => False
    | _ => True
    end).

(** Slow path send: may need to block and wait *)
Definition send_au (Φ : iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_chan s ∗
     "Hcont" ∷
    (match s with
    (* Case: Receiver is waiting, can complete immediately *)
    | chanstate.RcvPending =>
        own_chan (chanstate.SndCommit v) ={∅,⊤}=∗ Φ
    (* Case: Channel is idle, need to wait for receiver *)
    | chanstate.Idle =>
          own_chan (chanstate.SndPending v) ={∅,⊤}=∗
              send_nested_au Φ
    (* Case: Channel is closed, client must rule this out *)
    | chanstate.Closed drain => False
    (* Case: Buffered channel *)
    | chanstate.Buffered buff =>
        (* own_chan implies new buffer size is <= cap, so the whole update is
        equivalent to True if no space is available *)
        (own_chan (chanstate.Buffered (buff ++ [v])) ={∅,⊤}=∗ Φ)
    | _ => True
    end).

(** Fast path send: immediate completion when possible *)
Definition nonblocking_send_au Φ Φnotready : iProp Σ :=
  (|={⊤,∅}=>
     ▷∃ s, "Hoc" ∷ own_chan s ∗
           "Hcont" ∷
             match s with
             (* Case: Receiver is waiting, can complete immediately *)
             | chanstate.RcvPending =>
                 own_chan (chanstate.SndCommit v) ={∅,⊤}=∗ Φ
             (* Case: Channel is closed, client must rule this out *)
             | chanstate.Closed drain => False
             (* Case: Buffered channel *)
             | chanstate.Buffered buff =>
                   (own_chan (chanstate.Buffered (buff ++ [v])) ={∅,⊤}=∗ Φ)
             | _ => True
             end) ∧
  Φnotready.

(* Special case update that only works if the channel is known to be buffered.
   This is only an illustrative example. Proofs and specs should always use [send_au_slow] *)
Definition buffered_send_au Φ : iProp Σ :=
  |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_chan s ∗
          "Hcont" ∷
            match s with
            | chanstate.Buffered buf => own_chan (chanstate.Buffered (buf ++ [v])) ={∅,⊤}=∗ Φ
            | chanstate.Closed _ => False
            | _ => True
            end.

(** This is an alternate specification for nonblocking chan send that allows for
    proving a caller-chosen [Φnotready] in case the send does not occur. If no
    cases are ready in the containing select statement, the [Φnotready]s will be
    passed as a precondition to the default handler, allowing for reasoning
    about programs in which it should be _impossible_ to reach the default.

    This is not implied by nor does it imply [nonblocking_send_au].
    - [nonblocking_send_au -∗ nonblocking_send_au_alt]: the default spec does not provide
      [|={∅,⊤}=>] in the notready case, but it's necessary to somehow close all
      invariants in [nonblocking_send_au_alt].
    - [nonblocking_send_au_alt -∗ nonblocking_send_au]: under [nonblocking_send_au_alt], the notready
      predicate is only known to be true if the channel is _actually_ not ready,
      whereas [nonblocking_send_au] requires proving it's always OK to skip a case.

    The writer of this spec does not know a different au which is weaker than
    both [nonblocking_send_au] and [nonblocking_send_au_alt] and which is provable with
    [TrySend]. If such a thing exists, it may enable having a canonical spec for
    nonblocking channel operations. To be worth it, it would also require having
    a canonical version of the select spec, for which there are currently two
    (see [golang/theory/chan.v]). *)
Definition nonblocking_send_au_alt Φ Φnotready : iProp Σ :=
  |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_chan s ∗
          "Hcont" ∷
            match s with
            (* Case: Receiver is waiting, can complete immediately *)
            | chanstate.RcvPending =>
                own_chan (chanstate.SndCommit v) ={∅,⊤}=∗ Φ
            (* Case: Channel is closed, client must rule this out *)
            | chanstate.Closed drain => False
            (* Case: Buffered channel *)
            | chanstate.Buffered buff =>
                if decide (length buff < sint.Z $ chan_cap γ) then
                  (own_chan (chanstate.Buffered (buff ++ [v])) ={∅,⊤}=∗ Φ)
                else
                  (own_chan s ={∅,⊤}=∗ Φnotready)
            | _ => (own_chan s ={∅,⊤}=∗ Φnotready)
            end.

Definition close_au (Φ : iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hocinner" ∷ own_chan s ∗
     "Hcontinner" ∷
    (match s with
    (* Case: Ready to close unbuffered *)
    | chanstate.Idle =>
           own_chan (chanstate.Closed []) ={∅,⊤}=∗ Φ
    (* Case: Buffered, go to drain *)
    | chanstate.Buffered buff =>
          own_chan (chanstate.Closed buff) ={∅,⊤}=∗ Φ
    (* Case: Channel is closed already, panic *)
    | chanstate.Closed drain => False
    | _ => True
    end).

End au_defns.

Global Arguments own_chan {_} (γ) {V _} (s).
Global Arguments send_au {_ _ _ _ _ _} (γ) {V} (v) {_} (Φ).
Global Arguments nonblocking_send_au {_ _ _ _ _ _} (γ) {V} (v) {_} (Φ).
Global Arguments nonblocking_send_au_alt {_ _ _ _ _ _} (γ) {V} (v) {_} (Φ).
Global Arguments chan_cap_valid {_} (s cap).

Section defns.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  {sem : go.ChanSemantics}.

Context (ch : loc) (γ : chan_names) (V : Type) `{!chanG Σ V}.
Context `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.

(** Maps physical channel states to their heap representations.
    Each state corresponds to specific field values in the Go struct. *)
Definition chan_phys (s: chan_phys_state V) : iProp Σ :=
  match s with
    | Closed [] =>
        (∃ (slice_val: slice.t),
            "state" ∷ (ch.[channel.Channel.t V , "state"] ↦ (W64 6)) ∗
            "slice" ∷ slice_val ↦* ([] : list V) ∗
            "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
            "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val)
    | Closed drain =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 6) ∗
        "slice" ∷ slice_val ↦* drain ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    | Buffered buff =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 0) ∗
        "slice" ∷ slice_val ↦* buff ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    | Idle =>
        ∃ (v:V) (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 1) ∗
        "v" ∷ ch.[channel.Channel.t V, "v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    | SndWait v =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 2) ∗
        "v" ∷ ch.[channel.Channel.t V, "v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    | RcvWait =>
        ∃ (v:V) (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 3) ∗
        "v" ∷ ch.[channel.Channel.t V, "v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    | SndDone v =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 4) ∗
        "v" ∷ ch.[channel.Channel.t V, "v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    | RcvDone =>
        ∃ (v : V) (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 5) ∗
        "v" ∷ ch.[channel.Channel.t V, "v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    end.

(** Bundles together offer-related ghost state for atomic operations *)
Definition saved_offer (q : Qp)
  (lock_val : option (offer_lock V))
  (parked_prop continuation_prop : iProp Σ) : iProp Σ :=
  ghost_var γ.(offer_lock_name) q lock_val ∗
  saved_prop_own γ.(offer_parked_prop_name) (DfracOwn q) parked_prop ∗
  saved_prop_own γ.(offer_continuation_name) (DfracOwn q) continuation_prop.

(** Maps physical states to their logical representations with ghost state.
    This is the key invariant that connects the physical implementation
    to the logical specifications. *)
Definition chan_logical (s : chan_phys_state V): iProp Σ :=
  match s with
  | Idle =>
       ∃ (Φr: V → bool → iProp Σ),
           "Hoffer" ∷ saved_offer 1 None True True ∗
           "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn 1) (uncurry Φr) ∗
            own_chan γ chanstate.Idle

  | SndWait v =>
       ∃ (P: iProp Σ) (Φ: iProp Σ) (Φr: V → bool → iProp Σ),
          "Hoffer" ∷ saved_offer (1/2) (Some (Snd v)) P Φ ∗
          "HP" ∷ P ∗
          "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn 1) (uncurry Φr) ∗
          "Hau" ∷ (P -∗ send_au γ v Φ) ∗
           own_chan γ chanstate.Idle

  | RcvWait =>
       ∃ (P: iProp Σ) (Φr: V → bool → iProp Σ),
         "Hoffer" ∷ saved_offer (1/2) (Some Rcv) P True ∗
         "HP" ∷ P ∗
         "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn (1/2)) (uncurry Φr) ∗
         "Hau" ∷ (P -∗ recv_au γ V Φr) ∗
         own_chan γ chanstate.Idle

  | SndDone v =>
       ∃ (P: iProp Σ) (Φr: V → bool → iProp Σ),
       "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn (1/2)) (uncurry Φr) ∗
       "Hoffer" ∷ saved_offer (1/2) (Some Rcv) P True ∗
       "Hau" ∷ recv_nested_au γ V Φr ∗
       own_chan γ (chanstate.SndCommit v)

  | RcvDone =>
       ∃ (P: iProp Σ) (Φ: iProp Σ) (Φr: V → bool → iProp Σ) (v:V),
         "Hoffer" ∷ saved_offer (1/2) (Some (Snd v)) P Φ ∗
         "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn 1) (uncurry Φr) ∗
         "Hau" ∷ send_nested_au γ V Φ ∗
       own_chan γ chanstate.RcvCommit

  | Closed [] =>
          own_chan γ (chanstate.Closed []) ∗
           "Hoffer" ∷ (⌜chan_cap γ = 0⌝ -∗ saved_offer 1 None True True)

  | Closed drain =>
          own_chan γ (chanstate.Closed drain)

  | Buffered buff =>
          own_chan γ (chanstate.Buffered buff)
  end.

(** The main invariant protected by the channel's mutex.
    This connects the physical heap state with the logical state. *)
Definition chan_inv_inner : iProp Σ :=
  ∃ (s : chan_phys_state V),
    "phys" ∷ chan_phys s ∗
    "offer" ∷ chan_logical s
.

(** The public predicate that clients use to interact with channels.
    This is persistent and provides access to the channel's capabilities. *)
Definition is_chan : iProp Σ :=
  ∃ (mu_loc: loc),
    "#cap" ∷ ch.[channel.Channel.t V, "cap"] ↦□ (chan_cap γ) ∗
    "#mu" ∷ ch.[channel.Channel.t V, "mu"] ↦□ mu_loc ∗
    "#lock" ∷ is_lock mu_loc chan_inv_inner ∗
    "%Hnotnull" ∷ ⌜ ch ≠ chan.nil ⌝ ∗
    "%Hcap" ∷ ⌜ 0 ≤ sint.Z γ.(chan_cap) ⌝.
#[global] Typeclasses Opaque is_chan.
#[global] Opaque is_chan.
#[local] Transparent is_chan.
#[local] Typeclasses Transparent is_chan.

Lemma blocking_rcv_implies_nonblocking (Φ : V → bool → iProp Σ) :
  recv_au γ V Φ -∗
  nonblocking_recv_au γ V Φ True.
Proof.
  iIntros "Hau".
  iSplitL; last done. iMod "Hau" as (s) "[Hoc Hcont]".
  iModIntro. iExists s. iFrame "Hoc".
  destruct s; try done.
Qed.

Lemma blocking_send_implies_nonblocking (Φ : iProp Σ) v :
  send_au γ v Φ -∗
  nonblocking_send_au γ v Φ True.
Proof.
  iIntros "Hchan".
  iSplitL; last done.
  iMod "Hchan" as (s) "[Hoc Hcont]".
  iModIntro. iExists s. iFrame "Hoc".
  destruct s; try done.
Qed.

Lemma offer_idle_to_send parked_prop cont v :
  saved_offer 1 None True True ==∗
  saved_offer (1/2) (Some (Snd v)) parked_prop cont ∗
  saved_offer (1/2) (Some (Snd v)) parked_prop cont.
Proof.
  iIntros "[Hlock [Hoffer Hcont]]".
  iMod (ghost_var_update (Some (Snd v)) with "Hlock") as "[Hlock1 Hlock2]".
  iMod (saved_prop_update cont with "Hcont") as "[Hcont1 Hcont2]".
  iMod (saved_prop_update parked_prop with "Hoffer") as "[Hoffer1 Hoffer2]".
  iModIntro. iFrame.
Qed.

Lemma offer_halves_to_idle x y parked_prop cont :
  saved_offer (1/2) (Some x) parked_prop cont -∗
  saved_offer (1/2) (Some y) parked_prop cont ==∗
  saved_offer 1 None True True.
Proof.
  iIntros "[Hlock [Hoffer Hcont]]".
  iIntros "[Hlock2 [Hoffer2 Hcont2]]".
  iCombine "Hlock Hlock2" gives %Heq.
  assert (x = y) by (destruct_and!; congruence); subst.
  iCombine "Hlock Hlock2" as "Hlock".
  iMod (saved_prop_update_halves True with "Hoffer Hoffer2") as "[Hoffer Hoffer2]".
  iMod (saved_prop_update_halves True with "Hcont Hcont2") as "[Hcont Hcont2]".
  iCombine "Hcont Hcont2" as "Hcont".
  iCombine "Hoffer Hoffer2" as "Hoffer".
  iMod (ghost_var_update None with "Hlock") as "Hlock".
  iModIntro. iFrame.
  unfold saved_prop_own.
  rewrite dfrac_op_own.
  rewrite Qp.half_half.
  iFrame.
Qed.

Lemma offer_idle_to_recv parked_prop cont:
  saved_offer 1 None True True ==∗
  saved_offer (1/2) (Some Rcv) parked_prop cont ∗
  saved_offer (1/2) (Some Rcv) parked_prop cont.
Proof.
   iIntros "[Hlock [Hoffer Hcont]]".
  iMod (ghost_var_update (Some (Rcv)) with "Hlock") as "[Hlock1 Hlock2]".
  iMod (saved_prop_update cont with "Hcont") as "[Hcont1 Hcont2]".
  iMod (saved_prop_update parked_prop with "Hoffer") as "[Hoffer1 Hoffer2]".
  iModIntro. iFrame.
Qed.

Lemma offer_reset parked_prop cont state :
  saved_offer 1 state parked_prop cont ==∗
  saved_offer 1 None True True.
Proof.
  iIntros "[Hlock [Hoffer Hcont]]".
  iMod (ghost_var_update None with "Hlock") as "Hlock".
  iMod (saved_prop_update True with "Hcont") as "Hcont".
  iMod (saved_prop_update True with "Hoffer") as "Hoffer".
  iModIntro.
  iFrame.
Qed.

Lemma saved_offer_agree q1 q2
  lock1 parked1 cont1 lock2 parked2 cont2 :
  saved_offer q1 lock1 parked1 cont1 ∗
  saved_offer q2 lock2 parked2 cont2 ⊢
  ⌜lock1 = lock2⌝ ∗
  ▷(parked1 ≡ parked2) ∗ ▷(cont1 ≡ cont2).
Proof.
  iIntros "[[Hl1 [Hp1 Hc1]] [Hl2 [Hp2 Hc2]]]".
  iDestruct (ghost_var_agree with "Hl1 Hl2") as %->.
  iDestruct (saved_prop_agree with "Hp1 Hp2") as "Hp_eq".
  iDestruct (saved_prop_agree with "Hc1 Hc2") as "Hc_eq".
  auto.
Qed.

Lemma saved_offer_lc_agree
  lock1 parked1 cont1 lock2 parked2 cont2 :
  £ 1 -∗
  saved_offer (1/2) lock1 parked1 cont1 -∗
  saved_offer (1/2) lock2 parked2 cont2 -∗
  |={⊤}=> ⌜lock1 = lock2⌝ ∗
         (parked1 ≡ parked2) ∗ (cont1 ≡ cont2) ∗
         saved_offer 1 None True True.
Proof.
  iIntros "Hlc1".
  iIntros "[Hl1 [Hp1 Hc1]]".
  iIntros "[Hl2 [Hp2 Hc2]]".
  iDestruct (ghost_var_agree with "[$Hl1] [$Hl2]") as %->.
  iDestruct (saved_prop_agree with "[$Hp1] [$Hp2]") as "#Hp_eq".
  iDestruct (saved_prop_agree with "[$Hc1] [$Hc2]") as "#Hc_eq".

  iCombine "Hp_eq Hc_eq" as "Heq".
  iClear "Hp_eq Hc_eq".
  iMod (lc_fupd_elim_later with "Hlc1 Heq") as "[Hp_eq Hc_eq]".
  iFrame.
  iSplitR; first done.  (* ⌜lock2 = lock2⌝ is trivial *)

  (* Combine and update ghost variable *)
  iCombine "Hl1 Hl2" as "Hlock".
  iMod ((ghost_var_update None) with "Hlock") as "Hlock".

  (* Update saved propositions using halves lemmas *)
  iMod (saved_prop_update_halves True with "Hp1 Hp2") as "[Hp1 Hp2]".
  iMod (saved_prop_update_halves True with "Hc1 Hc2") as "[Hc1 Hc2]".

  (* Combine the updated halves to get full ownership *)
  iCombine "Hp1 Hp2" as "Hparked".
  iCombine "Hc1 Hc2" as "Hcont".

  (* Simplify the combined fractions *)
  rewrite dfrac_op_own Qp.half_half.

  iFrame.
  auto.
Qed.

Lemma saved_offer_fractional_invalid q1 q2 lock1 parked1 cont1 lock2 parked2 cont2 :
  (1 < q1 + q2)%Qp →
  saved_offer q1 lock1 parked1 cont1 -∗
  saved_offer q2 lock2 parked2 cont2 -∗
  False.
Proof.
  iIntros (Hq) "[Hlock1 [Hp1 Hc1]] [Hlock2 [Hp2 Hc2]]".
  iDestruct (ghost_var_valid_2 with "Hlock1 Hlock2") as "[%Hvalid _]".
  iPureIntro.
apply Qp.lt_nge in Hq.
contradiction.
Qed.

Lemma saved_offer_half_full_invalid lock1 parked1 cont1 lock2 parked2 cont2 :
  saved_offer (1/2) lock1 parked1 cont1 -∗
  saved_offer 1 lock2 parked2 cont2 -∗
  False.
Proof.
  iApply saved_offer_fractional_invalid.
  compute_done. (* 1/2 + 1 = 3/2 > 1 *)
Qed.

Lemma chanstate_update s s' :
  chanstate γ V 1 s ==∗ chanstate γ V 1 s'.
Proof.
  iApply ghost_var_update.
Qed.

Lemma chanstate_agree q1 q2 s s' :
  chanstate γ V q1 s -∗ chanstate γ V q2 s' -∗ ⌜s = s'⌝.
Proof.
  iIntros "H1 H2". by iApply (ghost_var_agree with "H1 H2").
Qed.

(* NOTE: unused *)
#[local] Lemma chanstate_combine s s' :
  chanstate γ V (1/2) s -∗ chanstate γ V (1/2) s' -∗ chanstate γ V 1 s.
Proof.
  iIntros "H1 H2". iDestruct (chanstate_agree with "H1 H2") as %->.
  iCombine "H1 H2" as "H". done.
Qed.

Lemma chanstate_halves_update s1 s2 s' :
  chanstate γ V (1/2) s1 -∗ chanstate γ V (1/2) s2 ==∗
  chanstate γ V (1/2) s' ∗ chanstate γ V (1/2) s'.
Proof.
  rewrite /chanstate.
  apply ghost_var_update_halves.
Qed.

(* FIXME: iCombine instances. *)
Lemma own_chan_agree s s' :
   own_chan γ s -∗ own_chan γ s' -∗ ⌜s = s'⌝.
Proof.
  iIntros "H1 H2". iNamedSuffix "H1" "1". iNamedSuffix "H2" "2".
  iDestruct (ghost_var_agree with "[$Hchanrepfrag1] [$Hchanrepfrag2]") as "%Hag".
  unfold chan_cap_valid in *.
  by iApply (ghost_var_agree with "Hchanrepfrag1 Hchanrepfrag2").
Qed.

(* Needs [chan_cap_valid s'' cap] as precondition? *)
Lemma own_chan_halves_update s'' s s' :
  chan_cap_valid s'' (sint.Z $ chan_cap γ) →
  own_chan γ s -∗ own_chan γ s' ==∗
  own_chan γ s'' ∗ own_chan γ s''.
Proof.
  intros Hvalid.
  iIntros "(Hv1 & %) (Hv2 & %)". rewrite /named.
  iMod (chanstate_halves_update with "Hv1 Hv2") as "[$ $]".
  iFrame "#∗".
  iPureIntro.
  auto.
Qed.

Lemma own_chan_buffer_size buf :
  own_chan γ (chanstate.Buffered buf) -∗
  ⌜Z.of_nat (length buf) ≤ sint.Z $ chan_cap γ⌝.
Proof.
  iNamed 1.
  simpl in Hcapvalid.
  iPureIntro. lia.
Qed.

Lemma own_chan_drain_size drain :
  own_chan γ (chanstate.Closed drain) -∗
  ⌜Z.of_nat (length drain) ≤ sint.Z $ chan_cap γ⌝.
Proof.
  iNamed 1.
  simpl in Hcapvalid.
  destruct drain.
  { simpl. iPureIntro; lia. }
  iPureIntro. lia.
Qed.

Global Instance is_chan_pers : Persistent is_chan.
Proof. apply _. Qed.

Global Instance own_chan_timeless s : Timeless (own_chan γ s).
Proof. apply _. Qed.

Lemma is_chan_not_null :
  is_chan -∗ ⌜ch ≠ null⌝.
Proof. iNamed 1. done. Qed.

End defns.

#[global] Opaque is_chan own_chan.

Global Arguments own_chan_halves_update {_ _ _ _} (_).
