/-
FFI module for distributed Perennial (Grove). Port of
`src/goose_lang/ffi/grove_ffi/impl.v` [Trusted definitions!].

Consists only of a network, per-node file storage, and clocks.

Differences from the Rocq version:
* No crash semantics (`ffi_crash_step`).
* `ffi_step` is a relation (see `Perennial/GooseLang/Lang.lean`); the Rocq
  `transition` is unfolded into it: either the operation stutters (state
  unchanged, `e' = ExternalOp op v`) or it takes an `is_grove_ffi_step`.
-/
import Perennial.GooseLang.Lang

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
abbrev endpoint := w64

inductive GroveVal where
  /-- Corresponds to a 2-tuple. -/
  | ListenSocketV (c : endpoint)
  /-- Corresponds to a 4-tuple. `c_l` is the local part, `c_r` the remote part. -/
  | ConnectionSocketV (c_l : endpoint) (c_r : endpoint)
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

@[reducible] def grove_op : ffi_syntax where
  ffi_opcode := GroveOp
  ffi_val := GroveVal

structure message where
  /-- Rocq constructor `Message`. -/
  Message ::
  msg_sender : endpoint
  msg_data : List w8
deriving DecidableEq

export message (Message)

/-- The global network state: a map from endpoint names to the set of messages
sent to those endpoints. -/
structure grove_global_state where
  grove_net : gmap endpoint (gset message)
  grove_global_time : w64

instance grove_global_state_inhabited : Inhabited grove_global_state :=
  ⟨{ grove_net := ∅, grove_global_time := 0 }⟩

/-- The per-node state -/
structure grove_node_state where
  grove_node_tsc : w64
  grove_node_files : gmap byte_string (List w8)

instance grove_node_state_inhabited : Inhabited grove_node_state :=
  ⟨{ grove_node_tsc := 0, grove_node_files := ∅ }⟩

@[reducible] def grove_model : ffi_model where
  ffi_state := grove_node_state
  ffi_global_state := grove_global_state

section grove
/- these are local instances on purpose, so that importing this files doesn't
suddenly cause all FFI parameters to be inferred as the grove model -/
attribute [local instance] grove_op grove_model
variable [GoGlobalContext]

def isFreshChan (fg : grove_global_state) (c : Option endpoint) : Prop :=
  match c with
  | none => True -- failure (to allocate a channel) is always an option
  | some c => fg.grove_net !! c = none

theorem gen_isFreshChan (σg : grove_global_state) : isFreshChan σg none := trivial

def is_grove_ffi_step (op : GroveOp) (v : val) (e' : expr)
    (σ σ' : grove_node_state) (g g' : grove_global_state) : Prop :=
  match op with
  | .ListenOp =>
      σ = σ' ∧ g = g' ∧ (∀ c : endpoint, v = #c → e' = Val (ExtV (ListenSocketV c)))
  | .ConnectOp =>
      ∀ c_r : endpoint, v = #c_r →
        σ = σ' ∧
        ∃ c_l, isFreshChan g c_l ∧
          match c_l with
          | none => g = g' ∧ e' = Val (PairV (#true) (ExtV BadSocketV))
          | some c_l => g' = { g with grove_net := <[c_l := ∅]> g.grove_net } ∧
              e' = Val (PairV (#false) (ExtV (ConnectionSocketV c_l c_r)))
  | .AcceptOp =>
      σ = σ' ∧ g = g' ∧ (∀ c_l, v = ExtV (ListenSocketV c_l) →
        ∃ c_r, g = g' ∧ e' = Val (ExtV (ConnectionSocketV c_l c_r)))
  | .SendOp =>
      σ = σ' ∧
      (∀ (data : List w8) c_l c_r,
        v = PairV (ExtV (ConnectionSocketV c_l c_r)) (#data) →
        match g.grove_net !! c_r with
        | some ms => ∃ b : Bool,
            g' = { g with grove_net := <[c_r := ms ∪ {[Message c_l data]}]> g.grove_net } ∧
            e' = Val (#b)
        | none => e' = Panic "invalid")
  | .RecvOp =>
      σ = σ' ∧ g = g' ∧
      (∀ c_l c_r, v = ExtV (ConnectionSocketV c_l c_r) →
        ∃ err : Bool,
          match g.grove_net !! c_l with
          | some ms =>
              if err then e' = Val (PairV (#true) (#([] : List w8)))
              else ∃ d, Message c_r d ∈ ms ∧ e' = Val (PairV (#false) (#d))
          | none => e' = Panic "invalid")
  | .FileReadOp =>
      σ = σ' ∧ g = g' ∧
      (∀ name : go_string, v = #name →
        match σ.grove_node_files !! name with
        | some data => e' = Val (#data)
        | none => e' = Panic "invalid")
  | .FileWriteOp =>
      g = g' ∧
      (∀ (name : go_string) (data : List w8), v = PairV (#name) (#data) →
        e' = Val (#()) ∧ σ' = { σ with grove_node_files := <[name := data]> σ.grove_node_files })
  | .FileAppendOp =>
      g = g' ∧
      (∀ (name : go_string) (data : List w8), v = PairV (#name) (#data) →
        match σ.grove_node_files !! name with
        | some old =>
            σ' = { σ with grove_node_files := <[name := old ++ data]> σ.grove_node_files } ∧
            e' = Val (#())
        | none => e' = Panic "invalid")
  | .GetTscOp =>
      g = g' ∧
      ∃ new_time : w64,
        σ.grove_node_tsc.toNat ≤ new_time.toNat ∧
        σ' = { σ with grove_node_tsc := new_time } ∧ e' = Val (#new_time)
  | .GetTimeRangeOp =>
      σ = σ' ∧
      ∃ new_time low high : w64,
        g.grove_global_time.toNat ≤ new_time.toNat ∧
        low.toNat ≤ new_time.toNat ∧ new_time.toNat ≤ high.toNat ∧
        g' = { g with grove_global_time := new_time } ∧
        e' = Val (PairV (#low) (#high))

/-- Rocq `ffi_step` (as a relation): the operation either stutters or takes an
`is_grove_ffi_step`; only the FFI parts of the state change. -/
def grove_ffi_step (op : GroveOp) (v : val) (σg : cfg_state) (e' : expr) (σg' : cfg_state) :
    Prop :=
  ∃ s' w', σg' = ({ σg.1 with world := s' }, { σg.2 with global_world := w' }) ∧
    ((s' = σg.1.world ∧ w' = σg.2.global_world ∧ e' = ExternalOp op (Val v)) ∨
      is_grove_ffi_step op v e' σg.1.world s' σg.2.global_world w')

@[reducible] def grove_semantics : ffi_semantics grove_op grove_model where
  ffi_step := grove_ffi_step

end grove

end Perennial
