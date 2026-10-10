/-
FFI module for distributed Perennial (Grove) [Trusted definitions!].

Consists only of a network, per-node file storage, and clocks.

* No crash semantics (`ffi_crash_step`).
* `ffi_step` is a relation (see `Perennial/GooseLang/Lang.lean`): either the
  operation stutters (state unchanged, `e' = ExternalOp op v`) or it takes an
  `IsGroveFfiStep`.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

/-! ## The Grove extension to GooseLang: primitive operations -/

inductive GroveOp where
  -- Network ops
  | ListenOp | ConnectOp | AcceptOp | SendOp | RecvOp
  -- File ops
  | FileReadOp | FileWriteOp | FileAppendOp
  -- Time ops
  | GetTscOp
  | GetTimeRangeOp
deriving DecidableEq, Inhabited

/-- `endpoint` corresponds to a host-IP-pair -/
abbrev Endpoint := w64

inductive GroveVal where
  /-- Corresponds to a 2-tuple. -/
  | ListenSocketV (c : Endpoint)
  /-- Corresponds to a 4-tuple. `c_l` is the local part, `c_r` the remote part. -/
  | ConnectionSocketV (c_l : Endpoint) (c_r : Endpoint)
  /-- A bad (error'd) connection -/
  | BadSocketV
deriving DecidableEq

export GroveVal (ListenSocketV ConnectionSocketV BadSocketV)

instance : Pos.Countable GroveOp where
  encode o := Pos.Countable.encode (match o with
      | .ListenOp => (0 : Nat) | .ConnectOp => 1 | .AcceptOp => 2 | .SendOp => 3 | .RecvOp => 4
      | .FileReadOp => 5 | .FileWriteOp => 6 | .FileAppendOp => 7 | .GetTscOp => 8
      | .GetTimeRangeOp => 9)
  decode p := match (Pos.Countable.decode p : Option Nat) with
    | some 0 => some .ListenOp | some 1 => some .ConnectOp | some 2 => some .AcceptOp
    | some 3 => some .SendOp | some 4 => some .RecvOp | some 5 => some .FileReadOp
    | some 6 => some .FileWriteOp | some 7 => some .FileAppendOp | some 8 => some .GetTscOp
    | some 9 => some .GetTimeRangeOp | _ => none
  decode_encode o := by cases o <;> simp [Pos.Countable.decode_encode]

instance : Pos.Countable GroveVal where
  encode v := Pos.Countable.encode (match v with
      | .ListenSocketV c => [c.toNat]
      | .ConnectionSocketV c_l c_r => [c_l.toNat, c_r.toNat]
      | .BadSocketV => [])
  decode p := match (Pos.Countable.decode p : Option (List Nat)) with
    | some [c] => some (.ListenSocketV (BitVec.ofNat 64 c))
    | some [c_l, c_r] => some (.ConnectionSocketV (BitVec.ofNat 64 c_l) (BitVec.ofNat 64 c_r))
    | some [] => some .BadSocketV
    | _ => none
  decode_encode v := by cases v <;> simp [Pos.Countable.decode_encode]

@[reducible] def grove_op : FfiSyntax where
  ffi_opcode := GroveOp
  ffi_val := GroveVal

structure message where
  Message ::
  msgSender : Endpoint
  msgData : List w8
deriving DecidableEq

export message (Message)

/-- The global network state: a map from endpoint names to the set of messages
sent to those endpoints. -/
structure GroveGlobalState where
  groveNet : GMap Endpoint (GSet message)
  groveGlobalTime : w64

instance groveGlobalState_inhabited : Inhabited GroveGlobalState :=
  ⟨{ groveNet := ∅, groveGlobalTime := 0 }⟩

/-- The per-node state -/
structure GroveNodeState where
  groveNodeTsc : w64
  groveNodeFiles : GMap byte_string (List w8)

instance groveNodeState_inhabited : Inhabited GroveNodeState :=
  ⟨{ groveNodeTsc := 0, groveNodeFiles := ∅ }⟩

@[reducible] def grove_model : FfiModel where
  ffi_state := GroveNodeState
  ffi_global_state := GroveGlobalState

section grove
/- these are local instances on purpose, so that importing this files doesn't
suddenly cause all FFI parameters to be inferred as the grove model -/
attribute [local instance] grove_op grove_model
variable [GoGlobalContext]

def IsFreshChan (fg : GroveGlobalState) (c : Option Endpoint) : Prop :=
  match c with
  | none => True -- failure (to allocate a channel) is always an option
  | some c => fg.groveNet !! c = none

theorem gen_isFreshChan (σg : GroveGlobalState) : IsFreshChan σg none := trivial

def IsGroveFfiStep (op : GroveOp) (v : val) (e' : Expr)
    (σ σ' : GroveNodeState) (g g' : GroveGlobalState) : Prop :=
  match op with
  | .ListenOp =>
      σ = σ' ∧ g = g' ∧ (∀ c : Endpoint, v = #c → e' = Val (ExtV (ListenSocketV c)))
  | .ConnectOp =>
      ∀ c_r : Endpoint, v = #c_r →
        σ = σ' ∧
        ∃ c_l, IsFreshChan g c_l ∧
          match c_l with
          | none => g = g' ∧ e' = Val (PairV (#true) (ExtV BadSocketV))
          | some c_l => g' = { g with groveNet := <[c_l := ∅]> g.groveNet } ∧
              e' = Val (PairV (#false) (ExtV (ConnectionSocketV c_l c_r)))
  | .AcceptOp =>
      σ = σ' ∧ g = g' ∧ (∀ c_l, v = ExtV (ListenSocketV c_l) →
        ∃ c_r, g = g' ∧ e' = Val (ExtV (ConnectionSocketV c_l c_r)))
  | .SendOp =>
      σ = σ' ∧
      (∀ (data : List w8) c_l c_r,
        v = PairV (ExtV (ConnectionSocketV c_l c_r)) (#data) →
        match g.groveNet !! c_r with
        | some ms => ∃ b : Bool,
            g' = { g with groveNet := <[c_r := ms ∪ {[Message c_l data]}]> g.groveNet } ∧
            e' = Val (#b)
        | none => e' = Panic "invalid")
  | .RecvOp =>
      σ = σ' ∧ g = g' ∧
      (∀ c_l c_r, v = ExtV (ConnectionSocketV c_l c_r) →
        ∃ err : Bool,
          match g.groveNet !! c_l with
          | some ms =>
              if err then e' = Val (PairV (#true) (#([] : List w8)))
              else ∃ d, Message c_r d ∈ ms ∧ e' = Val (PairV (#false) (#d))
          | none => e' = Panic "invalid")
  | .FileReadOp =>
      σ = σ' ∧ g = g' ∧
      (∀ name : GoString, v = #name →
        match σ.groveNodeFiles !! name with
        | some data => e' = Val (#data)
        | none => e' = Panic "invalid")
  | .FileWriteOp =>
      g = g' ∧
      (∀ (name : GoString) (data : List w8), v = PairV (#name) (#data) →
        e' = Val (#()) ∧ σ' = { σ with groveNodeFiles := <[name := data]> σ.groveNodeFiles })
  | .FileAppendOp =>
      g = g' ∧
      (∀ (name : GoString) (data : List w8), v = PairV (#name) (#data) →
        match σ.groveNodeFiles !! name with
        | some old =>
            σ' = { σ with groveNodeFiles := <[name := old ++ data]> σ.groveNodeFiles } ∧
            e' = Val (#())
        | none => e' = Panic "invalid")
  | .GetTscOp =>
      g = g' ∧
      ∃ new_time : w64,
        σ.groveNodeTsc.toNat ≤ new_time.toNat ∧
        σ' = { σ with groveNodeTsc := new_time } ∧ e' = Val (#new_time)
  | .GetTimeRangeOp =>
      σ = σ' ∧
      ∃ new_time low high : w64,
        g.groveGlobalTime.toNat ≤ new_time.toNat ∧
        low.toNat ≤ new_time.toNat ∧ new_time.toNat ≤ high.toNat ∧
        g' = { g with groveGlobalTime := new_time } ∧
        e' = Val (PairV (#low) (#high))

/-- The Grove FFI step relation: the operation either stutters or takes an
`IsGroveFfiStep`; only the FFI parts of the state change. -/
def GroveFfiStep (op : GroveOp) (v : val) (σg : CfgState) (e' : Expr) (σg' : CfgState) :
    Prop :=
  ∃ s' w', σg' = ({ σg.1 with world := s' }, { σg.2 with globalWorld := w' }) ∧
    ((s' = σg.1.world ∧ w' = σg.2.globalWorld ∧ e' = ExternalOp op (Val v)) ∨
      IsGroveFfiStep op v e' σg.1.world s' σg.2.globalWorld w')

@[reducible] def grove_semantics : FfiSemantics grove_op grove_model where
  ffi_step := GroveFfiStep
  ffi_step_threads h := by obtain ⟨_, _, rfl, _⟩ := h; rfl

end grove

end Perennial
