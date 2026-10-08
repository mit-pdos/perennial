/-
The logical state of a
channel (`chanstate.t`), the atomic-update style specifications for channel
operations (`sendAu`, `recvAu`, ...), and the channel invariant (`isChan`).

Notes:
* Ghost state. `chanstate.t V` and `option (OfferLock V)` are stored in
  `ghost_var`s and `V * bool → iProp` in a `saved_pred`. With
  the `allG` codes (see `Perennial/Ghost/All.lean`) the stored data must be
  `Pos.Countable`, so everything that mentions the ghost state assumes
  `[Pos.Countable V]` (the instances for `chanstate.t V` and `OfferLock V` are
  derived here).
* `1/2` is `(1 : Qp).half`.
* `isChan` and `ownChan` are sealed (`@[irreducible]` + `_unseal`).
-/
module

public import Perennial.Golang.Theory.Chan.AuSpec.ChanInit
public import Perennial.Golang.Theory.Lock
public import Perennial.Golang.Theory.Slice
public import Perennial.Golang.Defn.Chan

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.model

/-! The specification state for a channel. -/
namespace chanstate
inductive _root_.Perennial.ChanState (V : Type) : Type where
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

instance witness (V : Type) : Inhabited (ChanState V) := ⟨.Idle⟩

/-- Encoding into `Nat × List V` (for `Pos.Countable`). -/
def enc {V : Type} : ChanState V → Nat × List V
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

instance countable {V : Type} [Pos.Countable V] : Pos.Countable (ChanState V) :=
  .ofInjective (fun s => Pos.Countable.encode (enc s))
    (fun _ _ h => enc_inj (Pos.encode_inj h))

end chanstate

/-- The state machine representation matching the model implementation.
This is slightly different from the mathematical representation in that we
don't go to the `SndWait` state logically until an offer is about to be
accepted. -/
inductive ChanPhysState (V : Type) : Type where
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
inductive OfferLock (V : Type) : Type where
  /-- Sender has made an offer -/
  | Snd (v : V)
  /-- Receiver has made an offer -/
  | Rcv

instance OfferLock.countable {V : Type} [Pos.Countable V] : Pos.Countable (OfferLock V) :=
  .ofInjective
    (fun | .Snd v => Pos.Countable.encode (some v) | .Rcv => Pos.Countable.encode (none : Option V))
    (by
      intro a b h
      cases a <;> cases b <;> simp_all [Pos.encode_eq_iff])

/-- Ghost names for tracking various aspects of channel state in the logic. -/
structure ChanNames where
  /-- Main channel state -/
  stateName : GName
  /-- Offer protocol lock -/
  offerLockName : GName
  /-- The saved prop that we can leave with the channel to support select -/
  offerParkedPropName : GName
  /-- The saved continuation for receive, which is a predicate on `v, ok` -/
  offerParkedPredName : GName
  /-- The continuation for send -/
  offerContinuationName : GName
  /-- The channel capacity -/
  chanCap : w64

/-- Validity of a logical state for a channel of capacity `cap`. -/
def ChanCapValid {V : Type} (s : ChanState V) (cap : Int) : Prop :=
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable (γ : ChanNames) (V : Type) [Pos.Countable V]

def chanstate (q : Qp) (s : ChanState V) : IProp GF :=
  ghostVar γ.stateName q s

def ownChanDef (s : ChanState V) : IProp GF :=
  iprop("Hchanrepfrag" ∷ chanstate γ V (1 : Qp).half s ∗
    "%Hcapvalid" ∷ ⌜ChanCapValid s (sint.Z γ.chanCap)⌝)
/-- Represents ownership of a channel with its logical state. -/
@[irreducible] def ownChan (s : ChanState V) : IProp GF := ownChanDef γ V s
theorem ownChan_unseal : @ownChan = @ownChanDef := by funext; with_unfolding_all rfl

variable [ZeroVal V]

/-- Inner atomic update for receive completion (second phase of handshake). -/
def recvNestedAu (Φ : V → Bool → IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : ChanState V, "Hocinner" ∷ ownChan γ V s ∗
    "Hcontinner" ∷
    (match s with
      -- Case: Sender has committed, complete the exchange
      | .SndCommit v => iprop(ownChan γ V .Idle ={∅,⊤}=∗ Φ v true)
      -- Case: Channel is closed with no messages
      | .Closed [] => iprop(ownChan γ V s ={∅,⊤}=∗ Φ (zero_val V) false)
      | _ => iprop(True)))

/-- Slow path receive: may need to block and wait. -/
def recvAu (Φ : V → Bool → IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : ChanState V, "Hoc" ∷ ownChan γ V s ∗
    "Hcont" ∷
    (match s with
      -- Case: Sender is waiting, can complete immediately
      | .SndPending v => iprop(ownChan γ V .RcvCommit ={∅,⊤}=∗ Φ v true)
      -- Case: Channel is idle, need to wait for sender
      | .Idle => iprop(ownChan γ V .RcvPending ={∅,⊤}=∗ recvNestedAu γ V Φ)
      -- Case: Channel is closed
      | .Closed [] => iprop(ownChan γ V s ={∅,⊤}=∗ Φ (zero_val V) false)
      -- Case: Closed but still have values to drain
      | .Closed (v :: rest) => iprop(ownChan γ V (.Closed rest) ={∅,⊤}=∗ Φ v true)
      -- Case: Buffered channel with values in buffer
      | .Buffered (v :: rest) => iprop(ownChan γ V (.Buffered rest) ={∅,⊤}=∗ Φ v true)
      | _ => iprop(True)))

/-- The atomic update of `nonblockingRecvAu`. -/
def nonblockingRecvAuInner (Φ : V → Bool → IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : ChanState V, "Hoc" ∷ ownChan γ V s ∗
    "Hcont" ∷
    (match s with
      -- Case: Sender is waiting, can complete immediately
      | .SndPending v => iprop(ownChan γ V .RcvCommit ={∅,⊤}=∗ Φ v true)
      -- Case: Channel is closed
      | .Closed [] => iprop(ownChan γ V s ={∅,⊤}=∗ Φ (zero_val V) false)
      -- Case: Channel is closed but still has values to drain
      | .Closed (v :: rest) => iprop(ownChan γ V (.Closed rest) ={∅,⊤}=∗ Φ v true)
      -- Case: Buffered channel with values
      | .Buffered (v :: rest) => iprop(ownChan γ V (.Buffered rest) ={∅,⊤}=∗ Φ v true)
      | _ => iprop(True)))

/-- Fast path receive: immediate completion when possible. -/
def nonblockingRecvAu (Φ : V → Bool → IProp GF) (Φnotready : IProp GF) : IProp GF :=
  iprop(nonblockingRecvAuInner γ V Φ ∧ Φnotready)

/-- See `nonblockingSendAuAlt` documentation below. -/
def nonblockingRecvAuAlt (Φ : V → Bool → IProp GF) (Φnotready : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : ChanState V, "Hoc" ∷ ownChan γ V s ∗
    "Hcont" ∷
    (match s with
      | .SndPending v => iprop(ownChan γ V .RcvCommit ={∅,⊤}=∗ Φ v true)
      | .Closed [] => iprop(ownChan γ V s ={∅,⊤}=∗ Φ (zero_val V) false)
      | .Closed (v :: rest) => iprop(ownChan γ V (.Closed rest) ={∅,⊤}=∗ Φ v true)
      | .Buffered (v :: rest) => iprop(ownChan γ V (.Buffered rest) ={∅,⊤}=∗ Φ v true)
      | _ => iprop(ownChan γ V s ={∅,⊤}=∗ Φnotready)))

variable {V}

/-- Inner atomic update for send completion (second phase of handshake). -/
def sendNestedAu (Φ : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : ChanState V, "Hocinner" ∷ ownChan γ V s ∗
    "Hcontinner" ∷
    (match s with
      -- Case: Receiver has committed, complete the exchange
      | .RcvCommit => iprop(ownChan γ V .Idle ={∅,⊤}=∗ Φ)
      -- Case: Channel is closed, operation fails
      | .Closed _ => iprop(False)
      | _ => iprop(True)))

/-- Slow path send: may need to block and wait. -/
def sendAu (v : V) (Φ : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : ChanState V, "Hoc" ∷ ownChan γ V s ∗
    "Hcont" ∷
    (match s with
      -- Case: Receiver is waiting, can complete immediately
      | .RcvPending => iprop(ownChan γ V (.SndCommit v) ={∅,⊤}=∗ Φ)
      -- Case: Channel is idle, need to wait for receiver
      | .Idle => iprop(ownChan γ V (.SndPending v) ={∅,⊤}=∗ sendNestedAu (V := V) γ Φ)
      -- Case: Channel is closed, client must rule this out
      | .Closed _ => iprop(False)
      -- Case: Buffered channel. `ownChan` implies new buffer size is ≤ cap, so the
      -- whole update is equivalent to `True` if no space is available
      | .Buffered buff => iprop(ownChan γ V (.Buffered (buff ++ [v])) ={∅,⊤}=∗ Φ)
      | _ => iprop(True)))

/-- The atomic update of `nonblockingSendAu`. -/
def nonblockingSendAuInner (v : V) (Φ : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : ChanState V, "Hoc" ∷ ownChan γ V s ∗
    "Hcont" ∷
    (match s with
      -- Case: Receiver is waiting, can complete immediately
      | .RcvPending => iprop(ownChan γ V (.SndCommit v) ={∅,⊤}=∗ Φ)
      -- Case: Channel is closed, client must rule this out
      | .Closed _ => iprop(False)
      -- Case: Buffered channel
      | .Buffered buff => iprop(ownChan γ V (.Buffered (buff ++ [v])) ={∅,⊤}=∗ Φ)
      | _ => iprop(True)))

/-- Fast path send: immediate completion when possible. -/
def nonblockingSendAu (v : V) (Φ Φnotready : IProp GF) : IProp GF :=
  iprop(nonblockingSendAuInner γ v Φ ∧ Φnotready)

/-- Special case update that only works if the channel is known to be buffered.
This is only an illustrative example. Proofs and specs should always use
`sendAu`. -/
def bufferedSendAu (v : V) (Φ : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : ChanState V, "Hoc" ∷ ownChan γ V s ∗
    "Hcont" ∷
    (match s with
      | .Buffered buf => iprop(ownChan γ V (.Buffered (buf ++ [v])) ={∅,⊤}=∗ Φ)
      | .Closed _ => iprop(False)
      | _ => iprop(True)))

/-- This is an alternate specification for nonblocking chan send that allows for
proving a caller-chosen `Φnotready` in case the send does not occur. If no cases
are ready in the containing select statement, the `Φnotready`s will be passed as
a precondition to the default handler, allowing for reasoning about programs in
which it should be _impossible_ to reach the default.

This is not implied by nor does it imply `nonblockingSendAu`.
- `nonblockingSendAu -∗ nonblockingSendAuAlt`: the default spec does not
  provide `|={∅,⊤}=>` in the notready case, but it's necessary to somehow close
  all invariants in `nonblockingSendAuAlt`.
- `nonblockingSendAuAlt -∗ nonblockingSendAu`: under
  `nonblockingSendAuAlt`, the notready predicate is only known to be true if
  the channel is _actually_ not ready, whereas `nonblockingSendAu` requires
  proving it's always OK to skip a case.

The writer of this spec does not know a different au which is weaker than both
`nonblockingSendAu` and `nonblockingSendAuAlt` and which is provable with
`TrySend`. If such a thing exists, it may enable having a canonical spec for
nonblocking channel operations. To be worth it, it would also require having a
canonical version of the select spec, for which there are currently two (see
`Perennial/Golang/Theory/Chan.lean`). -/
def nonblockingSendAuAlt (v : V) (Φ Φnotready : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : ChanState V, "Hoc" ∷ ownChan γ V s ∗
    "Hcont" ∷
    (match s with
      | .RcvPending => iprop(ownChan γ V (.SndCommit v) ={∅,⊤}=∗ Φ)
      | .Closed _ => iprop(False)
      | .Buffered buff =>
          if (buff.length : Int) < sint.Z γ.chanCap then
            iprop(ownChan γ V (.Buffered (buff ++ [v])) ={∅,⊤}=∗ Φ)
          else
            iprop(ownChan γ V s ={∅,⊤}=∗ Φnotready)
      | _ => iprop(ownChan γ V s ={∅,⊤}=∗ Φnotready)))

variable (V)

def closeAu (Φ : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ ∃ s : ChanState V, "Hocinner" ∷ ownChan γ V s ∗
    "Hcontinner" ∷
    (match s with
      -- Case: Ready to close unbuffered
      | .Idle => iprop(ownChan γ V (.Closed []) ={∅,⊤}=∗ Φ)
      -- Case: Buffered, go to drain
      | .Buffered buff => iprop(ownChan γ V (.Closed buff) ={∅,⊤}=∗ Φ)
      -- Case: Channel is closed already, panic
      | .Closed _ => iprop(False)
      | _ => iprop(True)))

end au_defns

section defns
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics]
variable (ch : Loc) (γ : ChanNames) (V : Type) [Pos.Countable V]
variable [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- Maps physical channel states to their heap representations. Each state
corresponds to specific field values in the Go struct. -/
def chanPhys (s : ChanPhysState V) : IProp GF :=
  match s with
  | .Closed [] =>
      iprop(∃ (slice_val : GoSlice),
        "state" ∷ ch.[channel.Channel V, go!"state"] ↦ (W64 6) ∗
        "slice" ∷ slice_val ↦* ([] : List V) ∗
        "slice_cap" ∷ ownSliceCap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel V, go!"buffer"] ↦ slice_val)
  | .Closed drain =>
      iprop(∃ (slice_val : GoSlice),
        "state" ∷ ch.[channel.Channel V, go!"state"] ↦ (W64 6) ∗
        "slice" ∷ slice_val ↦* drain ∗
        "slice_cap" ∷ ownSliceCap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel V, go!"buffer"] ↦ slice_val)
  | .Buffered buff =>
      iprop(∃ (slice_val : GoSlice),
        "state" ∷ ch.[channel.Channel V, go!"state"] ↦ (W64 0) ∗
        "slice" ∷ slice_val ↦* buff ∗
        "slice_cap" ∷ ownSliceCap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel V, go!"buffer"] ↦ slice_val)
  | .Idle =>
      iprop(∃ (v0 : V) (slice_val : GoSlice),
        "state" ∷ ch.[channel.Channel V, go!"state"] ↦ (W64 1) ∗
        "v" ∷ ch.[channel.Channel V, go!"v"] ↦ v0 ∗
        "slice" ∷ slice_val ↦* ([] : List V) ∗
        "slice_cap" ∷ ownSliceCap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel V, go!"buffer"] ↦ slice_val)
  | .SndWait v =>
      iprop(∃ (slice_val : GoSlice),
        "state" ∷ ch.[channel.Channel V, go!"state"] ↦ (W64 2) ∗
        "v" ∷ ch.[channel.Channel V, go!"v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : List V) ∗
        "slice_cap" ∷ ownSliceCap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel V, go!"buffer"] ↦ slice_val)
  | .RcvWait =>
      iprop(∃ (v0 : V) (slice_val : GoSlice),
        "state" ∷ ch.[channel.Channel V, go!"state"] ↦ (W64 3) ∗
        "v" ∷ ch.[channel.Channel V, go!"v"] ↦ v0 ∗
        "slice" ∷ slice_val ↦* ([] : List V) ∗
        "slice_cap" ∷ ownSliceCap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel V, go!"buffer"] ↦ slice_val)
  | .SndDone v =>
      iprop(∃ (slice_val : GoSlice),
        "state" ∷ ch.[channel.Channel V, go!"state"] ↦ (W64 4) ∗
        "v" ∷ ch.[channel.Channel V, go!"v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : List V) ∗
        "slice_cap" ∷ ownSliceCap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel V, go!"buffer"] ↦ slice_val)
  | .RcvDone =>
      iprop(∃ (v0 : V) (slice_val : GoSlice),
        "state" ∷ ch.[channel.Channel V, go!"state"] ↦ (W64 5) ∗
        "v" ∷ ch.[channel.Channel V, go!"v"] ↦ v0 ∗
        "slice" ∷ slice_val ↦* ([] : List V) ∗
        "slice_cap" ∷ ownSliceCap V slice_val (DFrac.own 1) ∗
        "buffer" ∷ ch.[channel.Channel V, go!"buffer"] ↦ slice_val)

/-- Bundles together offer-related ghost state for atomic operations. -/
def savedOffer (q : Qp) (lock_val : Option (OfferLock V))
    (parked_prop continuation_prop : IProp GF) : IProp GF :=
  iprop(ghostVar γ.offerLockName q lock_val ∗
    savedPropOwn γ.offerParkedPropName (DFrac.own q) parked_prop ∗
    savedPropOwn γ.offerContinuationName (DFrac.own q) continuation_prop)

/-- Maps physical states to their logical representations with ghost state. This
is the key invariant that connects the physical implementation to the logical
specifications. -/
def chanLogical (s : ChanPhysState V) : IProp GF :=
  match s with
  | .Idle =>
      iprop(∃ (Φr0 : V → Bool → IProp GF),
        "Hoffer" ∷ savedOffer γ V 1 none iprop(True) iprop(True) ∗
        "Hpred" ∷ savedPredOwn γ.offerParkedPredName (DFrac.own 1) (Function.uncurry Φr0) ∗
        ownChan γ V .Idle)
  | .SndWait v =>
      iprop(∃ (P0 : IProp GF) (Φ0 : IProp GF) (Φr0 : V → Bool → IProp GF),
        "Hoffer" ∷ savedOffer γ V (1 : Qp).half (some (.Snd v)) P0 Φ0 ∗
        "HP" ∷ P0 ∗
        "Hpred" ∷ savedPredOwn γ.offerParkedPredName (DFrac.own 1) (Function.uncurry Φr0) ∗
        "Hau" ∷ (P0 -∗ sendAu γ v Φ0) ∗
        ownChan γ V .Idle)
  | .RcvWait =>
      iprop(∃ (P0 : IProp GF) (Φr0 : V → Bool → IProp GF),
        "Hoffer" ∷ savedOffer γ V (1 : Qp).half (some .Rcv) P0 iprop(True) ∗
        "HP" ∷ P0 ∗
        "Hpred" ∷ savedPredOwn γ.offerParkedPredName (DFrac.own (1 : Qp).half)
          (Function.uncurry Φr0) ∗
        "Hau" ∷ (P0 -∗ recvAu γ V Φr0) ∗
        ownChan γ V .Idle)
  | .SndDone v =>
      iprop(∃ (P0 : IProp GF) (Φr0 : V → Bool → IProp GF),
        "Hpred" ∷ savedPredOwn γ.offerParkedPredName (DFrac.own (1 : Qp).half)
          (Function.uncurry Φr0) ∗
        "Hoffer" ∷ savedOffer γ V (1 : Qp).half (some .Rcv) P0 iprop(True) ∗
        "Hau" ∷ recvNestedAu γ V Φr0 ∗
        ownChan γ V (.SndCommit v))
  | .RcvDone =>
      iprop(∃ (P0 : IProp GF) (Φ0 : IProp GF) (Φr0 : V → Bool → IProp GF) (v1 : V),
        "Hoffer" ∷ savedOffer γ V (1 : Qp).half (some (.Snd v1)) P0 Φ0 ∗
        "Hpred" ∷ savedPredOwn γ.offerParkedPredName (DFrac.own 1) (Function.uncurry Φr0) ∗
        "Hau" ∷ sendNestedAu (V := V) γ Φ0 ∗
        ownChan γ V .RcvCommit)
  | .Closed [] =>
      iprop(ownChan γ V (.Closed []) ∗
        "Hoffer" ∷ (⌜γ.chanCap = W64 0⌝ -∗ savedOffer γ V 1 none iprop(True) iprop(True)))
  | .Closed drain =>
      ownChan γ V (.Closed drain)
  | .Buffered buff =>
      ownChan γ V (.Buffered buff)

/-- The main invariant protected by the channel's mutex. This connects the
physical heap state with the logical state. -/
def chanInvInner : IProp GF :=
  iprop(∃ (s : ChanPhysState V),
    "phys" ∷ chanPhys ch V s ∗
    "offer" ∷ chanLogical γ V s)

theorem chanInvInner_intro (s : ChanPhysState V) :
    chanPhys ch V s ∗ chanLogical γ V s ⊢ chanInvInner (GF := GF) ch γ V := by
  unfold chanInvInner
  iintro ⟨H1, H2⟩
  iexists s
  iframe

def isChanDef : IProp GF :=
  iprop(∃ (mu_loc : Loc),
    "#cap" ∷ ch.[channel.Channel V, go!"cap"] ↦□ γ.chanCap ∗
    "#mu" ∷ ch.[channel.Channel V, go!"mu"] ↦□ mu_loc ∗
    "#lock" ∷ isLock mu_loc (chanInvInner ch γ V) ∗
    "%Hnotnull" ∷ ⌜ch ≠ chan.nil⌝ ∗
    "%Hcap" ∷ ⌜0 ≤ sint.Z γ.chanCap⌝)
/-- The public predicate that clients use to interact with channels. This is
persistent and provides access to the channel's capabilities. -/
@[irreducible] def isChan : IProp GF := isChanDef ch γ V
theorem isChan_unseal : @isChan = @isChanDef := by funext; with_unfolding_all rfl

end defns

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable (γ : ChanNames) (V : Type) [Pos.Countable V]

theorem blocking_rcv_implies_nonblocking [ZeroVal V] (Φ : V → Bool → IProp GF) :
    ⊢ recvAu γ V Φ -∗ nonblockingRecvAu γ V Φ iprop(True) := by
  iintro Hau
  unfold nonblockingRecvAu nonblockingRecvAuInner
  isplit
  · unfold recvAu
    imod Hau with ⟨%s, Hoc, Hcont⟩
    imodintro
    inext
    iexists s
    iframe Hoc
    rcases s with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩) <;> first | iexact Hcont | itrivial
  · itrivial

theorem blocking_send_implies_nonblocking (Φ : IProp GF) (v : V) :
    ⊢ sendAu γ v Φ -∗ nonblockingSendAu γ v Φ iprop(True) := by
  iintro Hchan
  unfold nonblockingSendAu nonblockingSendAuInner
  isplit
  · unfold sendAu
    imod Hchan with ⟨%s, Hoc, Hcont⟩
    imodintro
    inext
    iexists s
    iframe Hoc
    rcases s with _ | _ | _ | _ | _ | _ | _ <;> first | iexact Hcont | itrivial
  · itrivial

/-! Monotonicity of the atomic updates in their postconditions. -/

theorem sendNestedAu_wand (Φ1 Φ2 : IProp GF) :
    ⊢ sendNestedAu (V := V) γ Φ1 -∗ (Φ1 -∗ Φ2) -∗ sendNestedAu (V := V) γ Φ2 := by
  unfold sendNestedAu
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

theorem sendAu_wand (v : V) (Φ1 Φ2 : IProp GF) :
    ⊢ sendAu γ v Φ1 -∗ (Φ1 -∗ Φ2) -∗ sendAu γ v Φ2 := by
  unfold sendAu
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
    iapply sendNestedAu_wand $$ H Hw
  all_goals first
    | (iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H)
    | iexact Hcont
    | itrivial

theorem closeAu_wand (Φ1 Φ2 : IProp GF) :
    ⊢ closeAu γ V Φ1 -∗ (Φ1 -∗ Φ2) -∗ closeAu γ V Φ2 := by
  unfold closeAu
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

theorem recvNestedAu_wand [ZeroVal V] (Φ1 Φ2 : V → Bool → IProp GF) :
    ⊢ recvNestedAu γ V Φ1 -∗ (∀ v ok, Φ1 v ok -∗ Φ2 v ok) -∗ recvNestedAu γ V Φ2 := by
  unfold recvNestedAu
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

theorem recvAu_wand [ZeroVal V] (Φ1 Φ2 : V → Bool → IProp GF) :
    ⊢ recvAu γ V Φ1 -∗ (∀ v ok, Φ1 v ok -∗ Φ2 v ok) -∗ recvAu γ V Φ2 := by
  unfold recvAu
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
    iapply recvNestedAu_wand $$ H Hw
  all_goals first
    | (iintro H; imod Hcont $$ H with H; imodintro; iapply Hw $$ H)
    | iexact Hcont
    | itrivial

theorem nonblockingSendAuInner_wand (v : V) (Φ1 Φ2 : IProp GF) :
    ⊢ nonblockingSendAuInner γ v Φ1 -∗ (Φ1 -∗ Φ2) -∗ nonblockingSendAuInner γ v Φ2 := by
  unfold nonblockingSendAuInner
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

theorem nonblockingRecvAuInner_wand [ZeroVal V] (Φ1 Φ2 : V → Bool → IProp GF) :
    ⊢ nonblockingRecvAuInner γ V Φ1 -∗ (∀ v ok, Φ1 v ok -∗ Φ2 v ok) -∗
      nonblockingRecvAuInner γ V Φ2 := by
  unfold nonblockingRecvAuInner
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

theorem nonblockingSendAuAlt_wand (v : V) (Φ1 Φ2 N1 N2 : IProp GF) :
    ⊢ nonblockingSendAuAlt γ v Φ1 N1 -∗ ((Φ1 -∗ Φ2) ∧ (N1 -∗ N2)) -∗
      nonblockingSendAuAlt γ v Φ2 N2 := by
  unfold nonblockingSendAuAlt
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

theorem nonblockingRecvAuAlt_wand [ZeroVal V] (Φ1 Φ2 : V → Bool → IProp GF) (N1 N2 : IProp GF) :
    ⊢ nonblockingRecvAuAlt γ V Φ1 N1 -∗ ((∀ v ok, Φ1 v ok -∗ Φ2 v ok) ∧ (N1 -∗ N2)) -∗
      nonblockingRecvAuAlt γ V Φ2 N2 := by
  unfold nonblockingRecvAuAlt
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics]
variable (ch : Loc) (γ : ChanNames) (V : Type) [Pos.Countable V]

theorem ghostVar_halves {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    ghostVar (GF := GF) γ 1 a ⊢ ghostVar γ (1 : Qp).half a ∗ ghostVar γ (1 : Qp).half a := by
  have h := ghostVar_split (GF := GF) γ a (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact wand_entails h

theorem saved_prop_halves (γ : GName) (P : IProp GF) :
    savedPropOwn γ (DFrac.own 1) P ⊢
      savedPropOwn γ (DFrac.own (1 : Qp).half) P ∗ savedPropOwn γ (DFrac.own (1 : Qp).half) P := by
  have h := (saved_prop_fractional (GF := GF) γ P).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.1

theorem saved_pred_halves {A : Type} [Pos.Countable A] (γ : GName) (Φ : A → IProp GF) :
    savedPredOwn γ (DFrac.own 1) Φ ⊢
      savedPredOwn γ (DFrac.own (1 : Qp).half) Φ ∗ savedPredOwn γ (DFrac.own (1 : Qp).half) Φ := by
  have h := (saved_pred_fractional (GF := GF) γ Φ).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.1

theorem saved_pred_combine_halves {A : Type} [Pos.Countable A] (γ : GName) (Φ Ψ : A → IProp GF) :
    savedPredOwn γ (DFrac.own (1 : Qp).half) Φ ∗ savedPredOwn γ (DFrac.own (1 : Qp).half) Ψ ⊢
      savedPredOwn γ (DFrac.own 1) Φ := by
  have h := (saved_pred_combine_as (GF := GF) γ (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
    Φ Ψ).combine_sep_as
  rw [DFrac.op_own, Qp.half_add_half] at h
  exact h

/-- `saved_pred_agree` without consuming the saved predicates. -/
theorem saved_pred_agree_keep {A : Type} [Pos.Countable A] (γ : GName) (dq1 dq2 : DFrac)
    (Φ Ψ : A → IProp GF) (x : A) :
    savedPredOwn γ dq1 Φ ∗ savedPredOwn γ dq2 Ψ ⊢
      (savedPredOwn γ dq1 Φ ∗ savedPredOwn γ dq2 Ψ) ∗ ▷ (Φ x ≡ Ψ x) := by
  apply persistent_entails_left
  iintro ⟨H1, H2⟩
  iapply saved_pred_agree γ dq1 dq2 Φ Ψ x $$ H1 H2

theorem offer_idle_to_send (parked_prop cont : IProp GF) (v : V) :
    ⊢ savedOffer γ V 1 none iprop(True) iprop(True) ==∗
      savedOffer γ V (1 : Qp).half (some (.Snd v)) parked_prop cont ∗
      savedOffer γ V (1 : Qp).half (some (.Snd v)) parked_prop cont := by
  unfold savedOffer
  iintro ⟨Hlock, Hoffer, Hcont⟩
  imod ghostVar_update (some (OfferLock.Snd v)) _ _ $$ Hlock with Hlock
  icases ghostVar_halves _ _ $$ Hlock with ⟨Hlock1, Hlock2⟩
  imod saved_prop_update cont _ _ $$ Hcont with Hcont
  icases saved_prop_halves _ _ $$ Hcont with ⟨Hcont1, Hcont2⟩
  imod saved_prop_update parked_prop _ _ $$ Hoffer with Hoffer
  icases saved_prop_halves _ _ $$ Hoffer with ⟨Hoffer1, Hoffer2⟩
  imodintro
  iframe

theorem offer_halves_to_idle (x y : OfferLock V) (parked_prop cont : IProp GF) :
    ⊢ savedOffer γ V (1 : Qp).half (some x) parked_prop cont -∗
      savedOffer γ V (1 : Qp).half (some y) parked_prop cont ==∗
      savedOffer γ V 1 none iprop(True) iprop(True) := by
  unfold savedOffer
  iintro ⟨Hlock, Hoffer, Hcont⟩ ⟨Hlock2, Hoffer2, Hcont2⟩
  icombine Hlock Hlock2 gives %Heq
  obtain ⟨_, Heq⟩ := Heq
  cases Heq
  icombine Hlock Hlock2 as Hlock
  icombine Hoffer Hoffer2 as Hoffer
  icombine Hcont Hcont2 as Hcont
  imod ghostVar_update none _ _ $$ Hlock with Hlock
  imod saved_prop_update iprop(True) _ _ $$ Hoffer with Hoffer
  imod saved_prop_update iprop(True) _ _ $$ Hcont with Hcont
  imodintro
  iframe

theorem offer_idle_to_recv (parked_prop cont : IProp GF) :
    ⊢ savedOffer γ V 1 none iprop(True) iprop(True) ==∗
      savedOffer γ V (1 : Qp).half (some .Rcv) parked_prop cont ∗
      savedOffer γ V (1 : Qp).half (some .Rcv) parked_prop cont := by
  unfold savedOffer
  iintro ⟨Hlock, Hoffer, Hcont⟩
  imod ghostVar_update (some (OfferLock.Rcv (V := V))) _ _ $$ Hlock with Hlock
  icases ghostVar_halves _ _ $$ Hlock with ⟨Hlock1, Hlock2⟩
  imod saved_prop_update cont _ _ $$ Hcont with Hcont
  icases saved_prop_halves _ _ $$ Hcont with ⟨Hcont1, Hcont2⟩
  imod saved_prop_update parked_prop _ _ $$ Hoffer with Hoffer
  icases saved_prop_halves _ _ $$ Hoffer with ⟨Hoffer1, Hoffer2⟩
  imodintro
  iframe

theorem offer_reset (parked_prop cont : IProp GF) (state : Option (OfferLock V)) :
    ⊢ savedOffer γ V 1 state parked_prop cont ==∗
      savedOffer γ V 1 none iprop(True) iprop(True) := by
  unfold savedOffer
  iintro ⟨Hlock, Hoffer, Hcont⟩
  imod ghostVar_update none _ _ $$ Hlock with Hlock
  imod saved_prop_update iprop(True) _ _ $$ Hcont with Hcont
  imod saved_prop_update iprop(True) _ _ $$ Hoffer with Hoffer
  imodintro
  iframe

theorem savedOffer_agree (q1 q2 : Qp) (lock1 : Option (OfferLock V)) (parked1 cont1 : IProp GF)
    (lock2 : Option (OfferLock V)) (parked2 cont2 : IProp GF) :
    savedOffer γ V q1 lock1 parked1 cont1 ∗ savedOffer γ V q2 lock2 parked2 cont2 ⊢
      ⌜lock1 = lock2⌝ ∗ ▷ (parked1 ≡ parked2) ∗ ▷ (cont1 ≡ cont2) := by
  unfold savedOffer
  iintro ⟨⟨Hl1, Hp1, Hc1⟩, ⟨Hl2, Hp2, Hc2⟩⟩
  ihave %Heq := ghostVar_agree _ _ _ _ _ $$ Hl1 Hl2
  ihave Hp_eq := saved_prop_agree _ _ _ _ _ $$ Hp1 Hp2
  ihave Hc_eq := saved_prop_agree _ _ _ _ _ $$ Hc1 Hc2
  iframe
  ipureintro
  exact Heq

theorem savedOffer_fractional_invalid (q1 q2 : Qp) (lock1 : Option (OfferLock V))
    (parked1 cont1 : IProp GF) (lock2 : Option (OfferLock V)) (parked2 cont2 : IProp GF)
    (Hq : 1 < (q1 + q2 : Qp).val) :
    ⊢ savedOffer γ V q1 lock1 parked1 cont1 -∗ savedOffer γ V q2 lock2 parked2 cont2 -∗ False := by
  unfold savedOffer
  iintro ⟨Hlock1, _, _⟩ ⟨Hlock2, _, _⟩
  ihave %Hvalid := ghostVar_valid_2 _ _ _ _ _ $$ Hlock1 Hlock2
  exfalso
  have h1 := Hvalid.1
  have : (q1 + q2 : Qp).val ≤ 1 := h1
  grind

theorem savedOffer_half_full_invalid (lock1 : Option (OfferLock V)) (parked1 cont1 : IProp GF)
    (lock2 : Option (OfferLock V)) (parked2 cont2 : IProp GF) :
    ⊢ savedOffer γ V (1 : Qp).half lock1 parked1 cont1 -∗
      savedOffer γ V 1 lock2 parked2 cont2 -∗ False := by
  iapply savedOffer_fractional_invalid
  show (1 : Rat) < (1 : Rat) / 2 + 1
  grind

theorem chanstate_update (s s' : ChanState V) :
    ⊢ chanstate (GF := GF) γ V 1 s ==∗ chanstate γ V 1 s' := by
  unfold chanstate
  exact ghostVar_update _ _ _

theorem chanstate_agree (q1 q2 : Qp) (s s' : ChanState V) :
    ⊢ chanstate (GF := GF) γ V q1 s -∗ chanstate γ V q2 s' -∗ ⌜s = s'⌝ := by
  unfold chanstate
  exact ghostVar_agree _ _ _ _ _

theorem chanstate_halves_update (s1 s2 s' : ChanState V) :
    ⊢ chanstate (GF := GF) γ V (1 : Qp).half s1 -∗ chanstate γ V (1 : Qp).half s2 ==∗
      chanstate γ V (1 : Qp).half s' ∗ chanstate γ V (1 : Qp).half s' := by
  unfold chanstate
  exact ghostVar_update_halves _ _ _ _

-- FIXME: iCombine instances.
theorem ownChan_agree (s s' : ChanState V) :
    ⊢ ownChan (GF := GF) γ V s -∗ ownChan γ V s' -∗ ⌜s = s'⌝ := by
  rw [ownChan_unseal]; unfold ownChanDef
  iintro ⟨H1, _⟩ ⟨H2, _⟩
  iapply chanstate_agree $$ H1 H2

/-- Needs `ChanCapValid s'' cap` as precondition. -/
theorem ownChan_halves_update (s'' s s' : ChanState V)
    (Hvalid : ChanCapValid s'' (sint.Z γ.chanCap)) :
    ⊢ ownChan (GF := GF) γ V s -∗ ownChan γ V s' ==∗ ownChan γ V s'' ∗ ownChan γ V s'' := by
  rw [ownChan_unseal]; unfold ownChanDef
  iintro ⟨Hv1, _⟩ ⟨Hv2, _⟩
  imod chanstate_halves_update γ V s s' s'' $$ Hv1 Hv2 with ⟨H1, H2⟩
  imodintro
  iframe
  isplit <;> ipureintro <;> exact Hvalid

theorem ownChan_cap_valid (s : ChanState V) :
    ⊢ ownChan (GF := GF) γ V s -∗ ⌜ChanCapValid s (sint.Z γ.chanCap)⌝ := by
  rw [ownChan_unseal]; unfold ownChanDef
  iintro ⟨_, %Hcapvalid⟩
  ipureintro
  exact Hcapvalid

/-- Build `ownChan` from the ghost-state half. -/
theorem ownChan_intro (s : ChanState V) (Hvalid : ChanCapValid s (sint.Z γ.chanCap)) :
    ⊢ chanstate (GF := GF) γ V (1 : Qp).half s -∗ ownChan γ V s := by
  rw [ownChan_unseal]; unfold ownChanDef
  iintro H
  iframe
  ipureintro
  exact Hvalid

theorem ownChan_buffer_size (buf : List V) :
    ⊢ ownChan (GF := GF) γ V (.Buffered buf) -∗ ⌜(buf.length : Int) ≤ sint.Z γ.chanCap⌝ := by
  rw [ownChan_unseal]; unfold ownChanDef
  iintro ⟨_, %Hcapvalid⟩
  ipureintro
  exact Hcapvalid.1

theorem ownChan_drain_size (drain : List V) :
    ⊢ ownChan (GF := GF) γ V (.Closed drain) -∗ ⌜(drain.length : Int) ≤ sint.Z γ.chanCap⌝ := by
  rw [ownChan_unseal]; unfold ownChanDef
  iintro ⟨_, %Hcapvalid⟩
  ipureintro
  cases drain with
  | nil => simpa [ChanCapValid] using Hcapvalid
  | cons _ _ => exact Hcapvalid.1

variable [ZeroVal V] [TypedPointsto (GF := GF) V]

instance isChan_pers : Persistent (isChan (GF := GF) ch γ V) := by
  rw [isChan_unseal]; unfold isChanDef; infer_instance

instance ownChan_timeless (s : ChanState V) : Timeless (ownChan (GF := GF) γ V s) := by
  rw [ownChan_unseal]; unfold ownChanDef chanstate; infer_instance

theorem isChan_not_null : ⊢ isChan (GF := GF) ch γ V -∗ ⌜ch ≠ null⌝ := by
  rw [isChan_unseal]; unfold isChanDef
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

theorem val_bool_eq [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]
    [go.PreSemantics] (b1 b2 : Bool) : ((#b1 : val) = #b2) = (b1 = b2) := by
  rw [go.intoVal_unfold Bool]
  simp

section lc_lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable (γ : ChanNames) (V : Type) [Pos.Countable V]

theorem savedOffer_lc_agree (lock1 : Option (OfferLock V)) (parked1 cont1 : IProp GF)
    (lock2 : Option (OfferLock V)) (parked2 cont2 : IProp GF) :
    ⊢ £ 1 -∗ savedOffer γ V (1 : Qp).half lock1 parked1 cont1 -∗
      savedOffer γ V (1 : Qp).half lock2 parked2 cont2 -∗
      |={⊤}=> ⌜lock1 = lock2⌝ ∗ (parked1 ≡ parked2) ∗ (cont1 ≡ cont2) ∗
        savedOffer γ V 1 none iprop(True) iprop(True) := by
  unfold savedOffer
  iintro Hlc1 ⟨Hl1, Hp1, Hc1⟩ ⟨Hl2, Hp2, Hc2⟩
  ihave %Heq := ghostVar_agree _ _ _ _ _ $$ Hl1 Hl2
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
  imod ghostVar_update none _ _ $$ Hlock with Hlock
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
