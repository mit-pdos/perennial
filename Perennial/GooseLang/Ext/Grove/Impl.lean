/-
The Grove extension of GooseLang, for distributed Perennial [Trusted definitions!].

Consists only of a network, per-node file storage, and clocks.

* Crashes (`ExtSemantics.crash`): a node's state may be anything afterwards
  (`grove_ffi` does not make its writes durable).
* Initial states (`ExtSemantics.initLocal`/`initGlobal`): any (the default): the
  network may hold any messages, any endpoints may be free or listened on, and a node
  may hold any files, clocks and so on.
* The step (`GroveStep`, the `ExtSemantics` of `groveExt`) is a relation:
  either one of Grove's operations (`groveOps`) stutters (state unchanged,
  `e' = ExternalOp groveExt.name op v`) or it
  takes an `IsGroveStep`. It does not change the heap.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

/-! ## The Grove extension to GooseLang: primitive operations -/

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

structure message where
  Message ::
  msgSender : Endpoint
  msgData : List w8
deriving DecidableEq

export message (Message)

/-- The global state: a map from endpoint names to the set of messages sent to
those endpoints, whether each endpoint is being listened on (`Listen` is stuck on an
endpoint not in `groveListen`), and the global time. -/
structure GroveGlobalState where
  groveNet : GMap Endpoint (GSet message)
  groveListen : GMap Endpoint Bool
  groveGlobalTime : w64

instance groveGlobalState_inhabited : Inhabited GroveGlobalState :=
  ⟨{ groveNet := ∅, groveListen := ∅, groveGlobalTime := 0 }⟩

/-- The per-node state -/
structure GroveNodeState where
  groveNodeTsc : w64
  groveNodeFiles : GMap byte_string (List w8)

instance groveNodeState_inhabited : Inhabited GroveNodeState :=
  ⟨{ groveNodeTsc := 0, groveNodeFiles := ∅ }⟩

/-- The Grove extension: network, files and clocks. -/
@[reducible] def groveExt : GooseExt where
  name := "github.com/mit-pdos/gokv/grove_ffi"
  Val := GroveVal
  LocalState := GroveNodeState
  GlobalState := GroveGlobalState

section grove
variable [GooseExts] [GoGlobalContext]

/-- A Grove value (a socket). -/
abbrev groveV (v : GroveVal) : val := ExtV (extVal groveExt v)

/-- An endpoint `Listen` and `Connect` accept: the bits above the port are 0
(`grove_ffi.AddressToStr` ignores them), the IP is not `0.0.0.0` (the wildcard address)
and the port is not 0 (with which `net.Listen` picks a port). -/
def ValidEndpoint (a : Endpoint) : Prop :=
  a >>> 48 = 0 ∧ a &&& 0xffffffff ≠ 0 ∧ (a >>> 32) &&& 0xffff ≠ 0

instance (a : Endpoint) : Decidable (ValidEndpoint a) := by
  unfold ValidEndpoint; infer_instance

/-- An endpoint `Listen` accepts: a valid endpoint whose port is at least 1024 (binding a lower
port needs privilege). -/
def ListenEndpoint (a : Endpoint) : Prop :=
  ValidEndpoint a ∧ 1024 ≤ (a >>> 32) &&& 0xffff

instance (a : Endpoint) : Decidable (ListenEndpoint a) := by
  unfold ListenEndpoint; infer_instance

/-- A file name `FileRead`, `FileWrite` and `FileAppend` accept: non-empty, with no `/` (47)
and no NUL byte, not `.` (46) or `..`, and at most 244 bytes (`FileWrite`'s temporary file is
named by the name, `_` and up to 10 digits, at most 255 bytes, Linux's `NAME_MAX`). -/
def ValidFileName (name : GoString) : Prop :=
  name ≠ [] ∧ (47 : w8) ∉ name ∧ (0 : w8) ∉ name ∧ name ≠ [(46 : w8)] ∧
    name ≠ [(46 : w8), 46] ∧ name.length ≤ 244

instance (name : GoString) : Decidable (ValidFileName name) := by
  unfold ValidFileName; infer_instance

/-- A local endpoint `Connect` may pick: none (it fails), or one that is neither a channel nor
an endpoint `Listen` may be called on. -/
def IsFreshChan (fg : GroveGlobalState) (c : Option Endpoint) : Prop :=
  match c with
  | none => True -- failure (to allocate a channel) is always an option
  | some c => fg.groveNet !! c = none ∧ fg.groveListen !! c = none

theorem gen_isFreshChan (σg : GroveGlobalState) : IsFreshChan σg none := trivial

def IsGroveStep (op : String) (v : val) (e' : Expr)
    (σ σ' : GroveNodeState) (g g' : GroveGlobalState) : Prop :=
  match op with
  | "Listen" =>
      σ = σ' ∧
      (∀ c : Endpoint, v = #c →
        if ListenEndpoint c ∧ g.groveListen !! c = some false then
          g' = { g with groveListen := <[c := true]> g.groveListen } ∧
            e' = Val (groveV (ListenSocketV c))
        else e' = Panic "invalid")
  | "Connect" =>
      ∀ c_r : Endpoint, v = #c_r →
        if ValidEndpoint c_r then
          σ = σ' ∧
          ∃ c_l, IsFreshChan g c_l ∧
            match c_l with
            | none => g = g' ∧ e' = Val (PairV (#true) (groveV BadSocketV))
            | some c_l => g' = { g with groveNet := <[c_l := ∅]> g.groveNet } ∧
                e' = Val (PairV (#false) (groveV (ConnectionSocketV c_l c_r)))
        else e' = Panic "invalid"
  | "Accept" =>
      σ = σ' ∧ g = g' ∧ (∀ c_l, v = groveV (ListenSocketV c_l) →
        ∃ c_r, g = g' ∧ e' = Val (groveV (ConnectionSocketV c_l c_r)))
  | "Send" =>
      σ = σ' ∧
      (∀ (data : List w8) c_l c_r,
        v = PairV (groveV (ConnectionSocketV c_l c_r)) (#data) →
        match g.groveNet !! c_r with
        | some ms => ∃ b : Bool,
            g' = { g with groveNet := <[c_r := ms ∪ {[Message c_l data]}]> g.groveNet } ∧
            e' = Val (#b)
        | none => e' = Panic "invalid")
  | "Receive" =>
      σ = σ' ∧ g = g' ∧
      (∀ c_l c_r, v = groveV (ConnectionSocketV c_l c_r) →
        ∃ err : Bool,
          match g.groveNet !! c_l with
          | some ms =>
              if err then e' = Val (PairV (#true) (#([] : List w8)))
              else ∃ d, Message c_r d ∈ ms ∧ e' = Val (PairV (#false) (#d))
          | none => e' = Panic "invalid")
  | "FileRead" =>
      σ = σ' ∧ g = g' ∧
      (∀ name : GoString, v = #name →
        if ValidFileName name then
          match σ.groveNodeFiles !! name with
          | some data => e' = Val (#data)
          | none => e' = Panic "invalid"
        else e' = Panic "invalid")
  | "FileWrite" =>
      g = g' ∧
      (∀ (name : GoString) (data : List w8), v = PairV (#name) (#data) →
        if ValidFileName name then
          e' = Val (#()) ∧ σ' = { σ with groveNodeFiles := <[name := data]> σ.groveNodeFiles }
        else e' = Panic "invalid")
  | "FileAppend" =>
      g = g' ∧
      (∀ (name : GoString) (data : List w8), v = PairV (#name) (#data) →
        if ValidFileName name then
          match σ.groveNodeFiles !! name with
          | some old =>
              σ' = { σ with groveNodeFiles := <[name := old ++ data]> σ.groveNodeFiles } ∧
              e' = Val (#())
          | none => e' = Panic "invalid"
        else e' = Panic "invalid")
  | "GetTSC" =>
      g = g' ∧
      ∃ new_time : w64,
        σ.groveNodeTsc.toNat ≤ new_time.toNat ∧
        σ' = { σ with groveNodeTsc := new_time } ∧ e' = Val (#new_time)
  | "GetTimeRange" =>
      σ = σ' ∧
      ∃ new_time low high : w64,
        g.groveGlobalTime.toNat ≤ new_time.toNat ∧
        low.toNat ≤ new_time.toNat ∧ new_time.toNat ≤ high.toNat ∧
        g' = { g with groveGlobalTime := new_time } ∧
        e' = Val (PairV (#low) (#high))
  | _ => False

/-- The names of Grove's operations (`IsGroveStep`'s cases). -/
def groveOps : List String :=
  ["Listen", "Connect", "Accept", "Send", "Receive", "FileRead", "FileWrite", "FileAppend",
    "GetTSC", "GetTimeRange"]

/-- The Grove step relation: one of Grove's operations either stutters or takes an
`IsGroveStep`; the heap does not change. Any other operation name has no step (it does not
stutter: a model calling an operation Grove does not have is stuck, not looping). -/
def GroveStep (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (σ : GroveNodeState)
    (g : GroveGlobalState) (e' : Expr) (h' : GMap Loc (NonAtomic val)) (σ' : GroveNodeState)
    (g' : GroveGlobalState) : Prop :=
  h' = h ∧ ((op ∈ groveOps ∧ σ' = σ ∧ g' = g ∧ e' = ExternalOp groveExt.name op (Val v)) ∨
    IsGroveStep op v e' σ σ' g g')

end grove

/-- On a crash, the node's state may be anything: `grove_ffi.FileWrite` renames
its temporary file over the file without syncing the directory, so a crash may
undo a write that returned, and `FileAppend` ignores the result of its write,
so a crash may leave part of it; the TSC restarts. (Nothing proves crash
safety for Grove yet: there is no `ExtCrashInterp` for it.) -/
instance grove_semantics : ExtSemantics groveExt where
  step := GroveStep
  crash _ _ := True


end Perennial
