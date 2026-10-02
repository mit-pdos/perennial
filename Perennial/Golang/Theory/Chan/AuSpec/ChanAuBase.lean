/-
Port of `new/golang/theory/chan/au_spec/chan_au_base.v`: the logical state of a
channel (`chanstate.t`), the atomic-update style specifications for channel
operations (`send_au`, `recv_au`, ...), and the channel invariant (`is_chan`).

Lean notes / deviations:
* Ghost state. Rocq stores `chanstate.t V` and `option (offer_lock V)` in
  `ghost_var`s and `V * bool → iProp` in a `saved_pred`, for arbitrary `V`. With
  the `allG` codes (see `Perennial/Ghost/All.lean`) the stored data must be
  `Pos.Countable`, so everything that mentions the ghost state assumes
  `[Pos.Countable V]` (the instances for `chanstate.t V` and `offer_lock V` are
  derived here).
* `1/2` is `(1 : Qp).half`.
* `is_chan` and `own_chan` are sealed (`@[irreducible]` + `_unseal`), as Rocq
  makes them `Opaque`.
-/
import Perennial.Golang.Theory.Chan.AuSpec.ChanInit
import Perennial.Golang.Theory.Lock
import Perennial.Golang.Theory.Slice
import Perennial.Golang.Defn.Chan

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.model

/-! The specification state for a channel. -/
namespace chanstate
inductive t (V : Type) : Type where
  /-- Buffered channel with pending messages -/
  | Buffered (buff : List V)
  /-- Empty unbuffered channel, ready for operations -/
  | Idle
  /-- Unbuffered channel with sender waiting -/
  | SndPending (v : V)
  /-- Unbuffered channel with receiver waiting -/
  | RcvPending
  /-- Sender committed, waiting for receiver to complete -/
  | SndCommit (v : V)
  /-- Receiver committed, waiting for sender to complete -/
  | RcvCommit
  /-- Closed channel, possibly drain remaining messages -/
  | Closed (drain : List V)

instance witness (V : Type) : Inhabited (t V) := ⟨.Idle⟩

/-- Encoding into `Nat × List V` (for `Pos.Countable`). -/
def enc {V : Type} : t V → Nat × List V
  | .Buffered b => (0, b)
  | .Idle => (1, [])
  | .SndPending v => (2, [v])
  | .RcvPending => (3, [])
  | .SndCommit v => (4, [v])
  | .RcvCommit => (5, [])
  | .Closed d => (6, d)

theorem enc_inj {V : Type} : Function.Injective (enc (V := V)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [enc]

instance countable {V : Type} [Pos.Countable V] : Pos.Countable (t V) :=
  .ofInjective (fun s => Pos.Countable.encode (enc s))
    (fun _ _ h => enc_inj (Pos.encode_inj h))

end chanstate

/-- The state machine representation matching the model implementation.
This is slightly different from the mathematical representation in that we
don't go to the `SndWait` state logically until an offer is about to be
accepted. -/
inductive chan_phys_state (V : Type) : Type where
  /-- Channel with buffered messages -/
  | Buffered (buffer : List V)
  /-- Ready for operations -/
  | Idle
  /-- Sender offers -/
  | SndWait (v : V)
  /-- Receiver offers -/
  | RcvWait
  /-- Sender operation completed, handshake in progress -/
  | SndDone (v : V)
  /-- Receiver operation completed, handshake in progress -/
  | RcvDone
  /-- Closed channel -/
  | Closed (buffer : List V)

/-- The offer protocol coordinates handshakes between senders and receivers in
unbuffered channels. An "offer" represents a pending operation that can be
accepted by the other party. This ghost state ensures that an outstanding offer
can only be accepted or left as-is for when we lock the channel to check the
status. -/
inductive offer_lock (V : Type) : Type where
  /-- Sender has made an offer -/
  | Snd (v : V)
  /-- Receiver has made an offer -/
  | Rcv

instance offer_lock.countable {V : Type} [Pos.Countable V] : Pos.Countable (offer_lock V) :=
  .ofInjective
    (fun | .Snd v => Pos.Countable.encode (some v) | .Rcv => Pos.Countable.encode (none : Option V))
    (by
      intro a b h
      cases a <;> cases b <;> simp_all [Pos.encode_eq_iff])

/-- Ghost names for tracking various aspects of channel state in the logic. -/
structure chan_names where
  /-- Main channel state -/
  state_name : GName
  /-- Offer protocol lock -/
  offer_lock_name : GName
  /-- The saved prop that we can leave with the channel to support select -/
  offer_parked_prop_name : GName
  /-- The saved continuation for receive, which is a predicate on `v, ok` -/
  offer_parked_pred_name : GName
  /-- The continuation for send -/
  offer_continuation_name : GName
  /-- The channel capacity -/
  chan_cap : w64

/-- Validity of a logical state for a channel of capacity `cap`. -/
def chan_cap_valid {V : Type} (s : chanstate.t V) (cap : Int) : Prop :=
  match s with
  | .Buffered buf =>
      -- Buffered is only used for buffered channels, and buffer size is bounded
      -- by capacity
      ((buf.length : Int) ≤ cap) ∧ (0 < cap)
  | .Closed [] => (0 ≤ cap)
  | .Closed drain =>
      -- Draining closed channels are buffered channels, and draining elements are
      -- bounded by capacity
      ((drain.length : Int) ≤ cap) ∧ (0 < cap)
  | _ => cap = 0  -- All other states are unbuffered

section au_defns
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF] [allG GF]
variable (γ : chan_names) (V : Type) [Pos.Countable V]

def chanstate (q : Qp) (s : chanstate.t V) : IProp GF :=
  ghost_var γ.state_name q s

def own_chan_def (s : chanstate.t V) : IProp GF :=
  iprop("Hchanrepfrag" ∷ chanstate γ V (1 : Qp).half s ∗
    "%Hcapvalid" ∷ ⌜chan_cap_valid s (sint.Z γ.chan_cap)⌝)
/-- Represents ownership of a channel with its logical state. -/
@[irreducible] def own_chan (s : chanstate.t V) : IProp GF := own_chan_def γ V s
theorem own_chan_unseal : @own_chan = @own_chan_def := by funext; with_unfolding_all rfl

variable [ZeroVal V]

/-- Inner atomic update for receive completion (second phase of handshake). -/
def recv_nested_au (Φ : V → Bool → IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : chanstate.t V, "Hocinner" ∷ own_chan γ V s ∗
    "Hcontinner" ∷
    (match s with
      -- Case: Sender has committed, complete the exchange
      | .SndCommit v => iprop(own_chan γ V .Idle ={∅,⊤}=∗ Φ v true)
      -- Case: Channel is closed with no messages
      | .Closed [] => iprop(own_chan γ V s ={∅,⊤}=∗ Φ (zero_val V) false)
      | _ => iprop(True)))

/-- Slow path receive: may need to block and wait. -/
def recv_au (Φ : V → Bool → IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : chanstate.t V, "Hoc" ∷ own_chan γ V s ∗
    "Hcont" ∷
    (match s with
      -- Case: Sender is waiting, can complete immediately
      | .SndPending v => iprop(own_chan γ V .RcvCommit ={∅,⊤}=∗ Φ v true)
      -- Case: Channel is idle, need to wait for sender
      | .Idle => iprop(own_chan γ V .RcvPending ={∅,⊤}=∗ recv_nested_au γ V Φ)
      -- Case: Channel is closed
      | .Closed [] => iprop(own_chan γ V s ={∅,⊤}=∗ Φ (zero_val V) false)
      -- Case: Closed but still have values to drain
      | .Closed (v :: rest) => iprop(own_chan γ V (.Closed rest) ={∅,⊤}=∗ Φ v true)
      -- Case: Buffered channel with values in buffer
      | .Buffered (v :: rest) => iprop(own_chan γ V (.Buffered rest) ={∅,⊤}=∗ Φ v true)
      | _ => iprop(True)))

/-- The atomic update of `nonblocking_recv_au` (Rocq inlines it). -/
def nonblocking_recv_au_inner (Φ : V → Bool → IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : chanstate.t V, "Hoc" ∷ own_chan γ V s ∗
    "Hcont" ∷
    (match s with
      -- Case: Sender is waiting, can complete immediately
      | .SndPending v => iprop(own_chan γ V .RcvCommit ={∅,⊤}=∗ Φ v true)
      -- Case: Channel is closed
      | .Closed [] => iprop(own_chan γ V s ={∅,⊤}=∗ Φ (zero_val V) false)
      -- Case: Channel is closed but still has values to drain
      | .Closed (v :: rest) => iprop(own_chan γ V (.Closed rest) ={∅,⊤}=∗ Φ v true)
      -- Case: Buffered channel with values
      | .Buffered (v :: rest) => iprop(own_chan γ V (.Buffered rest) ={∅,⊤}=∗ Φ v true)
      | _ => iprop(True)))

/-- Fast path receive: immediate completion when possible. -/
def nonblocking_recv_au (Φ : V → Bool → IProp GF) (Φnotready : IProp GF) : IProp GF :=
  iprop(nonblocking_recv_au_inner γ V Φ ∧ Φnotready)

/-- See `nonblocking_send_au_alt` documentation below. -/
def nonblocking_recv_au_alt (Φ : V → Bool → IProp GF) (Φnotready : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : chanstate.t V, "Hoc" ∷ own_chan γ V s ∗
    "Hcont" ∷
    (match s with
      | .SndPending v => iprop(own_chan γ V .RcvCommit ={∅,⊤}=∗ Φ v true)
      | .Closed [] => iprop(own_chan γ V s ={∅,⊤}=∗ Φ (zero_val V) false)
      | .Closed (v :: rest) => iprop(own_chan γ V (.Closed rest) ={∅,⊤}=∗ Φ v true)
      | .Buffered (v :: rest) => iprop(own_chan γ V (.Buffered rest) ={∅,⊤}=∗ Φ v true)
      | _ => iprop(own_chan γ V s ={∅,⊤}=∗ Φnotready)))

variable {V}

/-- Inner atomic update for send completion (second phase of handshake). -/
def send_nested_au (Φ : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : chanstate.t V, "Hocinner" ∷ own_chan γ V s ∗
    "Hcontinner" ∷
    (match s with
      -- Case: Receiver has committed, complete the exchange
      | .RcvCommit => iprop(own_chan γ V .Idle ={∅,⊤}=∗ Φ)
      -- Case: Channel is closed, operation fails
      | .Closed _ => iprop(False)
      | _ => iprop(True)))

/-- Slow path send: may need to block and wait. -/
def send_au (v : V) (Φ : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : chanstate.t V, "Hoc" ∷ own_chan γ V s ∗
    "Hcont" ∷
    (match s with
      -- Case: Receiver is waiting, can complete immediately
      | .RcvPending => iprop(own_chan γ V (.SndCommit v) ={∅,⊤}=∗ Φ)
      -- Case: Channel is idle, need to wait for receiver
      | .Idle => iprop(own_chan γ V (.SndPending v) ={∅,⊤}=∗ send_nested_au (V := V) γ Φ)
      -- Case: Channel is closed, client must rule this out
      | .Closed _ => iprop(False)
      -- Case: Buffered channel. `own_chan` implies new buffer size is ≤ cap, so the
      -- whole update is equivalent to `True` if no space is available
      | .Buffered buff => iprop(own_chan γ V (.Buffered (buff ++ [v])) ={∅,⊤}=∗ Φ)
      | _ => iprop(True)))

/-- The atomic update of `nonblocking_send_au` (Rocq inlines it). -/
def nonblocking_send_au_inner (v : V) (Φ : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : chanstate.t V, "Hoc" ∷ own_chan γ V s ∗
    "Hcont" ∷
    (match s with
      -- Case: Receiver is waiting, can complete immediately
      | .RcvPending => iprop(own_chan γ V (.SndCommit v) ={∅,⊤}=∗ Φ)
      -- Case: Channel is closed, client must rule this out
      | .Closed _ => iprop(False)
      -- Case: Buffered channel
      | .Buffered buff => iprop(own_chan γ V (.Buffered (buff ++ [v])) ={∅,⊤}=∗ Φ)
      | _ => iprop(True)))

/-- Fast path send: immediate completion when possible. -/
def nonblocking_send_au (v : V) (Φ Φnotready : IProp GF) : IProp GF :=
  iprop(nonblocking_send_au_inner γ v Φ ∧ Φnotready)

/-- Special case update that only works if the channel is known to be buffered.
This is only an illustrative example. Proofs and specs should always use
`send_au`. -/
def buffered_send_au (v : V) (Φ : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : chanstate.t V, "Hoc" ∷ own_chan γ V s ∗
    "Hcont" ∷
    (match s with
      | .Buffered buf => iprop(own_chan γ V (.Buffered (buf ++ [v])) ={∅,⊤}=∗ Φ)
      | .Closed _ => iprop(False)
      | _ => iprop(True)))

/-- This is an alternate specification for nonblocking chan send that allows for
proving a caller-chosen `Φnotready` in case the send does not occur. If no cases
are ready in the containing select statement, the `Φnotready`s will be passed as
a precondition to the default handler, allowing for reasoning about programs in
which it should be _impossible_ to reach the default.

This is not implied by nor does it imply `nonblocking_send_au`.
- `nonblocking_send_au -∗ nonblocking_send_au_alt`: the default spec does not
  provide `|={∅,⊤}=>` in the notready case, but it's necessary to somehow close
  all invariants in `nonblocking_send_au_alt`.
- `nonblocking_send_au_alt -∗ nonblocking_send_au`: under
  `nonblocking_send_au_alt`, the notready predicate is only known to be true if
  the channel is _actually_ not ready, whereas `nonblocking_send_au` requires
  proving it's always OK to skip a case.

The writer of this spec does not know a different au which is weaker than both
`nonblocking_send_au` and `nonblocking_send_au_alt` and which is provable with
`TrySend`. If such a thing exists, it may enable having a canonical spec for
nonblocking channel operations. To be worth it, it would also require having a
canonical version of the select spec, for which there are currently two (see
`Perennial/Golang/Theory/Chan.lean`). -/
def nonblocking_send_au_alt (v : V) (Φ Φnotready : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : chanstate.t V, "Hoc" ∷ own_chan γ V s ∗
    "Hcont" ∷
    (match s with
      | .RcvPending => iprop(own_chan γ V (.SndCommit v) ={∅,⊤}=∗ Φ)
      | .Closed _ => iprop(False)
      | .Buffered buff =>
          if (buff.length : Int) < sint.Z γ.chan_cap then
            iprop(own_chan γ V (.Buffered (buff ++ [v])) ={∅,⊤}=∗ Φ)
          else
            iprop(own_chan γ V s ={∅,⊤}=∗ Φnotready)
      | _ => iprop(own_chan γ V s ={∅,⊤}=∗ Φnotready)))

variable (V)

def close_au (Φ : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : chanstate.t V, "Hocinner" ∷ own_chan γ V s ∗
    "Hcontinner" ∷
    (match s with
      -- Case: Ready to close unbuffered
      | .Idle => iprop(own_chan γ V (.Closed []) ={∅,⊤}=∗ Φ)
      -- Case: Buffered, go to drain
      | .Buffered buff => iprop(own_chan γ V (.Closed buff) ={∅,⊤}=∗ Φ)
      -- Case: Channel is closed already, panic
      | .Closed _ => iprop(False)
      | _ => iprop(True)))

end au_defns

section defns
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF] [allG GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics]
variable (ch : loc) (γ : chan_names) (V : Type) [Pos.Countable V]
variable [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- Maps physical channel states to their heap representations. Each state
corresponds to specific field values in the Go struct. -/
def chan_phys (s : chan_phys_state V) : IProp GF :=
  match s with
  | .Closed [] =>
      iprop(∃ (slice_val : slice.t),
        "state" ∷ ch.[channel.Channel.t V, go!"state"] ↦ (W64 6) ∗
        "slice" ∷ slice_val ↦* ([] : List V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, go!"buffer"] ↦ slice_val)
  | .Closed drain =>
      iprop(∃ (slice_val : slice.t),
        "state" ∷ ch.[channel.Channel.t V, go!"state"] ↦ (W64 6) ∗
        "slice" ∷ slice_val ↦* drain ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, go!"buffer"] ↦ slice_val)
  | .Buffered buff =>
      iprop(∃ (slice_val : slice.t),
        "state" ∷ ch.[channel.Channel.t V, go!"state"] ↦ (W64 0) ∗
        "slice" ∷ slice_val ↦* buff ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, go!"buffer"] ↦ slice_val)
  | .Idle =>
      iprop(∃ (v0 : V) (slice_val : slice.t),
        "state" ∷ ch.[channel.Channel.t V, go!"state"] ↦ (W64 1) ∗
        "v" ∷ ch.[channel.Channel.t V, go!"v"] ↦ v0 ∗
        "slice" ∷ slice_val ↦* ([] : List V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, go!"buffer"] ↦ slice_val)
  | .SndWait v =>
      iprop(∃ (slice_val : slice.t),
        "state" ∷ ch.[channel.Channel.t V, go!"state"] ↦ (W64 2) ∗
        "v" ∷ ch.[channel.Channel.t V, go!"v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : List V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, go!"buffer"] ↦ slice_val)
  | .RcvWait =>
      iprop(∃ (v0 : V) (slice_val : slice.t),
        "state" ∷ ch.[channel.Channel.t V, go!"state"] ↦ (W64 3) ∗
        "v" ∷ ch.[channel.Channel.t V, go!"v"] ↦ v0 ∗
        "slice" ∷ slice_val ↦* ([] : List V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, go!"buffer"] ↦ slice_val)
  | .SndDone v =>
      iprop(∃ (slice_val : slice.t),
        "state" ∷ ch.[channel.Channel.t V, go!"state"] ↦ (W64 4) ∗
        "v" ∷ ch.[channel.Channel.t V, go!"v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : List V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, go!"buffer"] ↦ slice_val)
  | .RcvDone =>
      iprop(∃ (v0 : V) (slice_val : slice.t),
        "state" ∷ ch.[channel.Channel.t V, go!"state"] ↦ (W64 5) ∗
        "v" ∷ ch.[channel.Channel.t V, go!"v"] ↦ v0 ∗
        "slice" ∷ slice_val ↦* ([] : List V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, go!"buffer"] ↦ slice_val)

/-- Bundles together offer-related ghost state for atomic operations. -/
def saved_offer (q : Qp) (lock_val : Option (offer_lock V))
    (parked_prop continuation_prop : IProp GF) : IProp GF :=
  iprop(ghost_var γ.offer_lock_name q lock_val ∗
    saved_prop_own γ.offer_parked_prop_name (DFrac.own q) parked_prop ∗
    saved_prop_own γ.offer_continuation_name (DFrac.own q) continuation_prop)

/-- Maps physical states to their logical representations with ghost state. This
is the key invariant that connects the physical implementation to the logical
specifications. -/
def chan_logical (s : chan_phys_state V) : IProp GF :=
  match s with
  | .Idle =>
      iprop(∃ (Φr0 : V → Bool → IProp GF),
        "Hoffer" ∷ saved_offer γ V 1 none iprop(True) iprop(True) ∗
        "Hpred" ∷ saved_pred_own γ.offer_parked_pred_name (DFrac.own 1) (Function.uncurry Φr0) ∗
        own_chan γ V .Idle)
  | .SndWait v =>
      iprop(∃ (P0 : IProp GF) (Φ0 : IProp GF) (Φr0 : V → Bool → IProp GF),
        "Hoffer" ∷ saved_offer γ V (1 : Qp).half (some (.Snd v)) P0 Φ0 ∗
        "HP" ∷ P0 ∗
        "Hpred" ∷ saved_pred_own γ.offer_parked_pred_name (DFrac.own 1) (Function.uncurry Φr0) ∗
        "Hau" ∷ (P0 -∗ send_au γ v Φ0) ∗
        own_chan γ V .Idle)
  | .RcvWait =>
      iprop(∃ (P0 : IProp GF) (Φr0 : V → Bool → IProp GF),
        "Hoffer" ∷ saved_offer γ V (1 : Qp).half (some .Rcv) P0 iprop(True) ∗
        "HP" ∷ P0 ∗
        "Hpred" ∷ saved_pred_own γ.offer_parked_pred_name (DFrac.own (1 : Qp).half)
          (Function.uncurry Φr0) ∗
        "Hau" ∷ (P0 -∗ recv_au γ V Φr0) ∗
        own_chan γ V .Idle)
  | .SndDone v =>
      iprop(∃ (P0 : IProp GF) (Φr0 : V → Bool → IProp GF),
        "Hpred" ∷ saved_pred_own γ.offer_parked_pred_name (DFrac.own (1 : Qp).half)
          (Function.uncurry Φr0) ∗
        "Hoffer" ∷ saved_offer γ V (1 : Qp).half (some .Rcv) P0 iprop(True) ∗
        "Hau" ∷ recv_nested_au γ V Φr0 ∗
        own_chan γ V (.SndCommit v))
  | .RcvDone =>
      iprop(∃ (P0 : IProp GF) (Φ0 : IProp GF) (Φr0 : V → Bool → IProp GF) (v1 : V),
        "Hoffer" ∷ saved_offer γ V (1 : Qp).half (some (.Snd v1)) P0 Φ0 ∗
        "Hpred" ∷ saved_pred_own γ.offer_parked_pred_name (DFrac.own 1) (Function.uncurry Φr0) ∗
        "Hau" ∷ send_nested_au (V := V) γ Φ0 ∗
        own_chan γ V .RcvCommit)
  | .Closed [] =>
      iprop(own_chan γ V (.Closed []) ∗
        "Hoffer" ∷ (⌜γ.chan_cap = W64 0⌝ -∗ saved_offer γ V 1 none iprop(True) iprop(True)))
  | .Closed drain =>
      own_chan γ V (.Closed drain)
  | .Buffered buff =>
      own_chan γ V (.Buffered buff)

/-- The main invariant protected by the channel's mutex. This connects the
physical heap state with the logical state. -/
def chan_inv_inner : IProp GF :=
  iprop(∃ (s : chan_phys_state V),
    "phys" ∷ chan_phys ch V s ∗
    "offer" ∷ chan_logical γ V s)

theorem chan_inv_inner_intro (s : chan_phys_state V) :
    chan_phys ch V s ∗ chan_logical γ V s ⊢ chan_inv_inner (GF := GF) ch γ V := by
  unfold chan_inv_inner
  iintro ⟨H1, H2⟩
  iexists s
  iframe

def is_chan_def : IProp GF :=
  iprop(∃ (mu_loc : loc),
    "#cap" ∷ ch.[channel.Channel.t V, go!"cap"] ↦□ γ.chan_cap ∗
    "#mu" ∷ ch.[channel.Channel.t V, go!"mu"] ↦□ mu_loc ∗
    "#lock" ∷ is_lock mu_loc (chan_inv_inner ch γ V) ∗
    "%Hnotnull" ∷ ⌜ch ≠ chan.nil⌝ ∗
    "%Hcap" ∷ ⌜0 ≤ sint.Z γ.chan_cap⌝)
/-- The public predicate that clients use to interact with channels. This is
persistent and provides access to the channel's capabilities. -/
@[irreducible] def is_chan : IProp GF := is_chan_def ch γ V
theorem is_chan_unseal : @is_chan = @is_chan_def := by funext; with_unfolding_all rfl

end defns

section lemmas
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF] [allG GF]
variable (γ : chan_names) (V : Type) [Pos.Countable V]

theorem blocking_rcv_implies_nonblocking [ZeroVal V] (Φ : V → Bool → IProp GF) :
    ⊢ recv_au γ V Φ -∗ nonblocking_recv_au γ V Φ iprop(True) := by
  iintro Hau
  unfold nonblocking_recv_au nonblocking_recv_au_inner
  isplit
  · unfold recv_au
    imod Hau with ⟨%s, Hoc, Hcont⟩
    imodintro
    inext
    iexists s
    iframe Hoc
    rcases s with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩) <;> first | iexact Hcont | itrivial
  · itrivial

theorem blocking_send_implies_nonblocking (Φ : IProp GF) (v : V) :
    ⊢ send_au γ v Φ -∗ nonblocking_send_au γ v Φ iprop(True) := by
  iintro Hchan
  unfold nonblocking_send_au nonblocking_send_au_inner
  isplit
  · unfold send_au
    imod Hchan with ⟨%s, Hoc, Hcont⟩
    imodintro
    inext
    iexists s
    iframe Hoc
    rcases s with _ | _ | _ | _ | _ | _ | _ <;> first | iexact Hcont | itrivial
  · itrivial

/-! Monotonicity of the atomic updates in their postconditions (not in Rocq, where the
corresponding reasoning is done inline in each proof). -/

theorem send_nested_au_wand (Φ1 Φ2 : IProp GF) :
    ⊢ send_nested_au (V := V) γ Φ1 -∗ (Φ1 -∗ Φ2) -∗ send_nested_au (V := V) γ Φ2 := by
  unfold send_nested_au
  iintro Hau Hw
  imod Hau with Hau
  imodintro
  inext
  icases Hau with ⟨%s, Hoc, Hcont⟩
  iexists s
  iframe Hoc
  rcases s with _ | _ | _ | _ | _ | _ | _
  all_goals first
    | (iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H)
    | iexact Hcont
    | itrivial

theorem send_au_wand (v : V) (Φ1 Φ2 : IProp GF) :
    ⊢ send_au γ v Φ1 -∗ (Φ1 -∗ Φ2) -∗ send_au γ v Φ2 := by
  unfold send_au
  iintro Hau Hw
  imod Hau with Hau
  imodintro
  inext
  icases Hau with ⟨%s, Hoc, Hcont⟩
  iexists s
  iframe Hoc
  rcases s with _ | _ | _ | _ | _ | _ | _
  case Idle =>
    iintro H
    imod Hcont $$ H with H
    imodintro
    iapply send_nested_au_wand $$ H Hw
  all_goals first
    | (iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H)
    | iexact Hcont
    | itrivial

theorem close_au_wand (Φ1 Φ2 : IProp GF) :
    ⊢ close_au γ V Φ1 -∗ (Φ1 -∗ Φ2) -∗ close_au γ V Φ2 := by
  unfold close_au
  iintro Hau Hw
  imod Hau with Hau
  imodintro
  inext
  icases Hau with ⟨%s, Hoc, Hcont⟩
  iexists s
  iframe Hoc
  rcases s with _ | _ | _ | _ | _ | _ | _
  all_goals first
    | (iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H)
    | iexact Hcont
    | itrivial

theorem recv_nested_au_wand [ZeroVal V] (Φ1 Φ2 : V → Bool → IProp GF) :
    ⊢ recv_nested_au γ V Φ1 -∗ (∀ v ok, Φ1 v ok -∗ Φ2 v ok) -∗ recv_nested_au γ V Φ2 := by
  unfold recv_nested_au
  iintro Hau Hw
  imod Hau with Hau
  imodintro
  inext
  icases Hau with ⟨%s, Hoc, Hcont⟩
  iexists s
  iframe Hoc
  rcases s with _ | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals first
    | (iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H)
    | iexact Hcont
    | itrivial

theorem recv_au_wand [ZeroVal V] (Φ1 Φ2 : V → Bool → IProp GF) :
    ⊢ recv_au γ V Φ1 -∗ (∀ v ok, Φ1 v ok -∗ Φ2 v ok) -∗ recv_au γ V Φ2 := by
  unfold recv_au
  iintro Hau Hw
  imod Hau with Hau
  imodintro
  inext
  icases Hau with ⟨%s, Hoc, Hcont⟩
  iexists s
  iframe Hoc
  rcases s with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  case Idle =>
    iintro H
    imod Hcont $$ H with H
    imodintro
    iapply recv_nested_au_wand $$ H Hw
  all_goals first
    | (iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H)
    | iexact Hcont
    | itrivial

theorem nonblocking_send_au_inner_wand (v : V) (Φ1 Φ2 : IProp GF) :
    ⊢ nonblocking_send_au_inner γ v Φ1 -∗ (Φ1 -∗ Φ2) -∗ nonblocking_send_au_inner γ v Φ2 := by
  unfold nonblocking_send_au_inner
  iintro Hau Hw
  imod Hau with Hau
  imodintro
  inext
  icases Hau with ⟨%s, Hoc, Hcont⟩
  iexists s
  iframe Hoc
  rcases s with _ | _ | _ | _ | _ | _ | _
  all_goals first
    | (iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H)
    | iexact Hcont
    | itrivial

theorem nonblocking_recv_au_inner_wand [ZeroVal V] (Φ1 Φ2 : V → Bool → IProp GF) :
    ⊢ nonblocking_recv_au_inner γ V Φ1 -∗ (∀ v ok, Φ1 v ok -∗ Φ2 v ok) -∗
      nonblocking_recv_au_inner γ V Φ2 := by
  unfold nonblocking_recv_au_inner
  iintro Hau Hw
  imod Hau with Hau
  imodintro
  inext
  icases Hau with ⟨%s, Hoc, Hcont⟩
  iexists s
  iframe Hoc
  rcases s with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals first
    | (iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H)
    | iexact Hcont
    | itrivial

theorem nonblocking_send_au_alt_wand (v : V) (Φ1 Φ2 N1 N2 : IProp GF) :
    ⊢ nonblocking_send_au_alt γ v Φ1 N1 -∗ ((Φ1 -∗ Φ2) ∧ (N1 -∗ N2)) -∗
      nonblocking_send_au_alt γ v Φ2 N2 := by
  unfold nonblocking_send_au_alt
  iintro Hau Hw
  imod Hau with Hau
  imodintro
  inext
  icases Hau with ⟨%s, Hoc, Hcont⟩
  iexists s
  iframe Hoc
  rcases s with buff | _ | _ | _ | _ | _ | _
  case Buffered =>
    dsimp only
    split
    · icases Hw with ⟨Hw, -⟩
      iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H
    · icases Hw with ⟨-, Hw⟩
      iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H
  case RcvPending =>
    icases Hw with ⟨Hw, -⟩
    iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H
  case Closed => iexact Hcont
  all_goals
    icases Hw with ⟨-, Hw⟩
    iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H

theorem nonblocking_recv_au_alt_wand [ZeroVal V] (Φ1 Φ2 : V → Bool → IProp GF) (N1 N2 : IProp GF) :
    ⊢ nonblocking_recv_au_alt γ V Φ1 N1 -∗ ((∀ v ok, Φ1 v ok -∗ Φ2 v ok) ∧ (N1 -∗ N2)) -∗
      nonblocking_recv_au_alt γ V Φ2 N2 := by
  unfold nonblocking_recv_au_alt
  iintro Hau Hw
  imod Hau with Hau
  imodintro
  inext
  icases Hau with ⟨%s, Hoc, Hcont⟩
  iexists s
  iframe Hoc
  rcases s with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  case SndPending =>
    icases Hw with ⟨Hw, -⟩
    iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H
  case Closed.nil =>
    icases Hw with ⟨Hw, -⟩
    iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H
  case Closed.cons =>
    icases Hw with ⟨Hw, -⟩
    iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H
  case Buffered.cons =>
    icases Hw with ⟨Hw, -⟩
    iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H
  all_goals
    icases Hw with ⟨-, Hw⟩
    iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H

end lemmas

section ghost_lemmas
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF] [allG GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics]
variable (ch : loc) (γ : chan_names) (V : Type) [Pos.Countable V]

theorem ghost_var_halves {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    ghost_var (GF := GF) γ 1 a ⊢ ghost_var γ (1 : Qp).half a ∗ ghost_var γ (1 : Qp).half a := by
  have h := ghost_var_split (GF := GF) γ a (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact wand_entails h

theorem saved_prop_halves (γ : GName) (P : IProp GF) :
    saved_prop_own γ (DFrac.own 1) P ⊢
      saved_prop_own γ (DFrac.own (1 : Qp).half) P ∗ saved_prop_own γ (DFrac.own (1 : Qp).half) P := by
  have h := (saved_prop_fractional (GF := GF) γ P).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.1

theorem saved_pred_halves {A : Type} [Pos.Countable A] (γ : GName) (Φ : A → IProp GF) :
    saved_pred_own γ (DFrac.own 1) Φ ⊢
      saved_pred_own γ (DFrac.own (1 : Qp).half) Φ ∗ saved_pred_own γ (DFrac.own (1 : Qp).half) Φ := by
  have h := (saved_pred_fractional (GF := GF) γ Φ).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.1

theorem saved_pred_combine_halves {A : Type} [Pos.Countable A] (γ : GName) (Φ Ψ : A → IProp GF) :
    saved_pred_own γ (DFrac.own (1 : Qp).half) Φ ∗ saved_pred_own γ (DFrac.own (1 : Qp).half) Ψ ⊢
      saved_pred_own γ (DFrac.own 1) Φ := by
  have h := (saved_pred_combine_as (GF := GF) γ (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
    Φ Ψ).combine_sep_as
  rw [DFrac.op_own, Qp.half_add_half] at h
  exact h

/-- `saved_pred_agree` without consuming the saved predicates (Rocq's `iDestruct` keeps
the hypotheses when the conclusion is persistent). -/
theorem saved_pred_agree_keep {A : Type} [Pos.Countable A] (γ : GName) (dq1 dq2 : DFrac)
    (Φ Ψ : A → IProp GF) (x : A) :
    saved_pred_own γ dq1 Φ ∗ saved_pred_own γ dq2 Ψ ⊢
      (saved_pred_own γ dq1 Φ ∗ saved_pred_own γ dq2 Ψ) ∗ ▷ (Φ x ≡ Ψ x) := by
  apply persistent_entails_left
  iintro ⟨H1, H2⟩
  iapply saved_pred_agree γ dq1 dq2 Φ Ψ x $$ H1 H2

theorem offer_idle_to_send (parked_prop cont : IProp GF) (v : V) :
    ⊢ saved_offer γ V 1 none iprop(True) iprop(True) ==∗
      saved_offer γ V (1 : Qp).half (some (.Snd v)) parked_prop cont ∗
      saved_offer γ V (1 : Qp).half (some (.Snd v)) parked_prop cont := by
  unfold saved_offer
  iintro ⟨Hlock, Hoffer, Hcont⟩
  imod ghost_var_update (some (offer_lock.Snd v)) _ _ $$ Hlock with Hlock
  icases ghost_var_halves _ _ $$ Hlock with ⟨Hlock1, Hlock2⟩
  imod saved_prop_update cont _ _ $$ Hcont with Hcont
  icases saved_prop_halves _ _ $$ Hcont with ⟨Hcont1, Hcont2⟩
  imod saved_prop_update parked_prop _ _ $$ Hoffer with Hoffer
  icases saved_prop_halves _ _ $$ Hoffer with ⟨Hoffer1, Hoffer2⟩
  imodintro
  iframe

theorem offer_halves_to_idle (x y : offer_lock V) (parked_prop cont : IProp GF) :
    ⊢ saved_offer γ V (1 : Qp).half (some x) parked_prop cont -∗
      saved_offer γ V (1 : Qp).half (some y) parked_prop cont ==∗
      saved_offer γ V 1 none iprop(True) iprop(True) := by
  unfold saved_offer
  iintro ⟨Hlock, Hoffer, Hcont⟩ ⟨Hlock2, Hoffer2, Hcont2⟩
  icombine Hlock Hlock2 gives %Heq
  obtain ⟨_, Heq⟩ := Heq
  cases Heq
  icombine Hlock Hlock2 as Hlock
  icombine Hoffer Hoffer2 as Hoffer
  icombine Hcont Hcont2 as Hcont
  imod ghost_var_update none _ _ $$ Hlock with Hlock
  imod saved_prop_update iprop(True) _ _ $$ Hoffer with Hoffer
  imod saved_prop_update iprop(True) _ _ $$ Hcont with Hcont
  imodintro
  iframe

theorem offer_idle_to_recv (parked_prop cont : IProp GF) :
    ⊢ saved_offer γ V 1 none iprop(True) iprop(True) ==∗
      saved_offer γ V (1 : Qp).half (some .Rcv) parked_prop cont ∗
      saved_offer γ V (1 : Qp).half (some .Rcv) parked_prop cont := by
  unfold saved_offer
  iintro ⟨Hlock, Hoffer, Hcont⟩
  imod ghost_var_update (some (offer_lock.Rcv (V := V))) _ _ $$ Hlock with Hlock
  icases ghost_var_halves _ _ $$ Hlock with ⟨Hlock1, Hlock2⟩
  imod saved_prop_update cont _ _ $$ Hcont with Hcont
  icases saved_prop_halves _ _ $$ Hcont with ⟨Hcont1, Hcont2⟩
  imod saved_prop_update parked_prop _ _ $$ Hoffer with Hoffer
  icases saved_prop_halves _ _ $$ Hoffer with ⟨Hoffer1, Hoffer2⟩
  imodintro
  iframe

theorem offer_reset (parked_prop cont : IProp GF) (state : Option (offer_lock V)) :
    ⊢ saved_offer γ V 1 state parked_prop cont ==∗
      saved_offer γ V 1 none iprop(True) iprop(True) := by
  unfold saved_offer
  iintro ⟨Hlock, Hoffer, Hcont⟩
  imod ghost_var_update none _ _ $$ Hlock with Hlock
  imod saved_prop_update iprop(True) _ _ $$ Hcont with Hcont
  imod saved_prop_update iprop(True) _ _ $$ Hoffer with Hoffer
  imodintro
  iframe

theorem saved_offer_agree (q1 q2 : Qp) (lock1 : Option (offer_lock V)) (parked1 cont1 : IProp GF)
    (lock2 : Option (offer_lock V)) (parked2 cont2 : IProp GF) :
    saved_offer γ V q1 lock1 parked1 cont1 ∗ saved_offer γ V q2 lock2 parked2 cont2 ⊢
      ⌜lock1 = lock2⌝ ∗ ▷ (parked1 ≡ parked2) ∗ ▷ (cont1 ≡ cont2) := by
  unfold saved_offer
  iintro ⟨⟨Hl1, Hp1, Hc1⟩, ⟨Hl2, Hp2, Hc2⟩⟩
  ihave %Heq := ghost_var_agree _ _ _ _ _ $$ Hl1 Hl2
  ihave Hp_eq := saved_prop_agree _ _ _ _ _ $$ Hp1 Hp2
  ihave Hc_eq := saved_prop_agree _ _ _ _ _ $$ Hc1 Hc2
  iframe
  ipureintro
  exact Heq

theorem saved_offer_fractional_invalid (q1 q2 : Qp) (lock1 : Option (offer_lock V))
    (parked1 cont1 : IProp GF) (lock2 : Option (offer_lock V)) (parked2 cont2 : IProp GF)
    (Hq : 1 < (q1 + q2 : Qp).val) :
    ⊢ saved_offer γ V q1 lock1 parked1 cont1 -∗ saved_offer γ V q2 lock2 parked2 cont2 -∗ False := by
  unfold saved_offer
  iintro ⟨Hlock1, _, _⟩ ⟨Hlock2, _, _⟩
  ihave %Hvalid := ghost_var_valid_2 _ _ _ _ _ $$ Hlock1 Hlock2
  exfalso
  have h1 := Hvalid.1
  have : (q1 + q2 : Qp).val ≤ 1 := h1
  grind

theorem saved_offer_half_full_invalid (lock1 : Option (offer_lock V)) (parked1 cont1 : IProp GF)
    (lock2 : Option (offer_lock V)) (parked2 cont2 : IProp GF) :
    ⊢ saved_offer γ V (1 : Qp).half lock1 parked1 cont1 -∗
      saved_offer γ V 1 lock2 parked2 cont2 -∗ False := by
  iapply saved_offer_fractional_invalid
  show (1 : Rat) < (1 : Rat) / 2 + 1
  grind

theorem chanstate_update (s s' : chanstate.t V) :
    ⊢ chanstate (GF := GF) γ V 1 s ==∗ chanstate γ V 1 s' := by
  unfold chanstate
  exact ghost_var_update _ _ _

theorem chanstate_agree (q1 q2 : Qp) (s s' : chanstate.t V) :
    ⊢ chanstate (GF := GF) γ V q1 s -∗ chanstate γ V q2 s' -∗ ⌜s = s'⌝ := by
  unfold chanstate
  exact ghost_var_agree _ _ _ _ _

theorem chanstate_halves_update (s1 s2 s' : chanstate.t V) :
    ⊢ chanstate (GF := GF) γ V (1 : Qp).half s1 -∗ chanstate γ V (1 : Qp).half s2 ==∗
      chanstate γ V (1 : Qp).half s' ∗ chanstate γ V (1 : Qp).half s' := by
  unfold chanstate
  exact ghost_var_update_halves _ _ _ _

-- FIXME (Rocq): iCombine instances.
theorem own_chan_agree (s s' : chanstate.t V) :
    ⊢ own_chan (GF := GF) γ V s -∗ own_chan γ V s' -∗ ⌜s = s'⌝ := by
  rw [own_chan_unseal]; unfold own_chan_def
  iintro ⟨H1, _⟩ ⟨H2, _⟩
  iapply chanstate_agree $$ H1 H2

/-- Needs `chan_cap_valid s'' cap` as precondition. -/
theorem own_chan_halves_update (s'' s s' : chanstate.t V)
    (Hvalid : chan_cap_valid s'' (sint.Z γ.chan_cap)) :
    ⊢ own_chan (GF := GF) γ V s -∗ own_chan γ V s' ==∗ own_chan γ V s'' ∗ own_chan γ V s'' := by
  rw [own_chan_unseal]; unfold own_chan_def
  iintro ⟨Hv1, _⟩ ⟨Hv2, _⟩
  imod chanstate_halves_update γ V s s' s'' $$ Hv1 Hv2 with ⟨H1, H2⟩
  imodintro
  iframe
  isplit <;> ipureintro <;> exact Hvalid

theorem own_chan_cap_valid (s : chanstate.t V) :
    ⊢ own_chan (GF := GF) γ V s -∗ ⌜chan_cap_valid s (sint.Z γ.chan_cap)⌝ := by
  rw [own_chan_unseal]; unfold own_chan_def
  iintro ⟨_, %Hcapvalid⟩
  ipureintro
  exact Hcapvalid

/-- Build `own_chan` from the ghost-state half (Rocq: `iFrame; iPureIntro`). -/
theorem own_chan_intro (s : chanstate.t V) (Hvalid : chan_cap_valid s (sint.Z γ.chan_cap)) :
    ⊢ chanstate (GF := GF) γ V (1 : Qp).half s -∗ own_chan γ V s := by
  rw [own_chan_unseal]; unfold own_chan_def
  iintro H
  iframe
  ipureintro
  exact Hvalid

theorem own_chan_buffer_size (buf : List V) :
    ⊢ own_chan (GF := GF) γ V (.Buffered buf) -∗ ⌜(buf.length : Int) ≤ sint.Z γ.chan_cap⌝ := by
  rw [own_chan_unseal]; unfold own_chan_def
  iintro ⟨_, %Hcapvalid⟩
  ipureintro
  exact Hcapvalid.1

theorem own_chan_drain_size (drain : List V) :
    ⊢ own_chan (GF := GF) γ V (.Closed drain) -∗ ⌜(drain.length : Int) ≤ sint.Z γ.chan_cap⌝ := by
  rw [own_chan_unseal]; unfold own_chan_def
  iintro ⟨_, %Hcapvalid⟩
  ipureintro
  cases drain with
  | nil => simpa [chan_cap_valid] using Hcapvalid
  | cons _ _ => exact Hcapvalid.1

variable [ZeroVal V] [TypedPointsto (GF := GF) V]

instance is_chan_pers : Persistent (is_chan (GF := GF) ch γ V) := by
  rw [is_chan_unseal]; unfold is_chan_def; infer_instance

instance own_chan_timeless (s : chanstate.t V) : Timeless (own_chan (GF := GF) γ V s) := by
  rw [own_chan_unseal]; unfold own_chan_def chanstate; infer_instance

theorem is_chan_not_null : ⊢ is_chan (GF := GF) ch γ V -∗ ⌜ch ≠ null⌝ := by
  rw [is_chan_unseal]; unfold is_chan_def
  iintro H
  iNamed H
  ipureintro
  exact Hnotnull

end ghost_lemmas

theorem internal_eq_rewrite_wand {GF : BundledGFunctors} {P Q : IProp GF} :
    ⊢ (P ≡ Q) -∗ Q -∗ P := by
  iintro #H HQ
  ihave #Hiff := internalEq_iff P Q $$ H
  icases Hiff with ⟨-, H2⟩
  iapply H2
  iexact HQ

theorem val_bool_eq [ffi_syntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]
    [go.PreSemantics] (b1 b2 : Bool) : ((#b1 : val) = #b2) = (b1 = b2) := by
  rw [go.into_val_unfold Bool]
  simp

section lc_lemmas
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable (γ : chan_names) (V : Type) [Pos.Countable V]

theorem saved_offer_lc_agree (lock1 : Option (offer_lock V)) (parked1 cont1 : IProp GF)
    (lock2 : Option (offer_lock V)) (parked2 cont2 : IProp GF) :
    ⊢ £ 1 -∗ saved_offer γ V (1 : Qp).half lock1 parked1 cont1 -∗
      saved_offer γ V (1 : Qp).half lock2 parked2 cont2 -∗
      |={⊤}=> ⌜lock1 = lock2⌝ ∗ (parked1 ≡ parked2) ∗ (cont1 ≡ cont2) ∗
        saved_offer γ V 1 none iprop(True) iprop(True) := by
  unfold saved_offer
  iintro Hlc1 ⟨Hl1, Hp1, Hc1⟩ ⟨Hl2, Hp2, Hc2⟩
  ihave %Heq := ghost_var_agree _ _ _ _ _ $$ Hl1 Hl2
  subst Heq
  ihave #Hp_eq := saved_prop_agree _ _ _ _ _ $$ Hp1 Hp2
  ihave #Hc_eq := saved_prop_agree _ _ _ _ _ $$ Hc1 Hc2
  ihave Heq : iprop(▷ ((parked1 ≡ parked2) ∗ (cont1 ≡ cont2))) $$ []
  · inext
    isplitl []
    · iexact Hp_eq
    · iexact Hc_eq
  imod lc_fupd_elim_later $$ Hlc1 Heq with ⟨#Hp_eq', #Hc_eq'⟩
  icombine Hl1 Hl2 as Hlock
  imod ghost_var_update none _ _ $$ Hlock with Hlock
  imod saved_prop_update_halves iprop(True) _ _ _ $$ Hp1 Hp2 with ⟨Hp1, Hp2⟩
  imod saved_prop_update_halves iprop(True) _ _ _ $$ Hc1 Hc2 with ⟨Hc1, Hc2⟩
  icombine Hp1 Hp2 as Hparked
  icombine Hc1 Hc2 as Hcont
  imodintro
  iframe
  isplit
  · ipureintro; rfl
  · isplit
    · iexact Hp_eq'
    · iexact Hc_eq'

end lc_lemmas

/-- Unfold the channel model's `offerState` constants (`buffered`, `idle`, ...),
which `wp_auto` does not unfold when they are stored. -/
macro "chan_unfold_consts" : tactic => `(tactic|
  simp only [channel.buffered, channel.idle, channel.sndPending, channel.rcvPending,
    channel.sndCommit, channel.rcvDone, channel.closed])

end Perennial
