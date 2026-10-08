/-
A pure model of
etcd's KV/lease semantics as computations (`ecomp`) over effects (`etcdE`).

Notes:
* Everything lives in `namespace go_etcd_io.etcd.client.v3_proof`, to avoid
  clashing with generic names such as `Error` or `interp`.
* `ecomp E` and `relation.t S` are Lean `Monad` instances, so `do` notation
  works; `exnT M R` is `M ∘ (R ⊕ ·)`.
* Since effects quantify over types, `etcdE : Type → Type 1` and
  `ecomp E R : Type 1`.
* `relation.t` (state transitions) is not in `Perennial/Std`; the (only) part
  needed here is defined locally.
* `do` is a Lean keyword, so it is `«do»`.
* The `Settable` instances are dropped: Lean has record-update syntax.
* `RangeRequest.default`/`PutRequest.default` use the zero values directly
  rather than `zero_val` (so they do not need `FfiSyntax`).
* `StronglySorted` is `List.Pairwise`, `Permutation` is `List.Perm`, stdpp
  `filter` is `List.filter`, `default d o` is `o.getD d`.
* `DeleteRange` and `Txn` are `opaque` constants (uninterpreted, no axiom or
  `sorry`).
-/
import Perennial.Proof.ProofPrelude
import Perennial.Golang.Defn.String

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace go_etcd_io.etcd.client.v3_proof

universe u v

inductive Ecomp (E : Type → Type u) (R : Type) : Type (max 1 u) where
  | Pure (r : R) : Ecomp E R
  | Effect {A : Type} (e : E A) (k : A → Ecomp E R) : Ecomp E R
  /- Having a separate [Bind] permits binding at pure computation steps,
     whereas binding only in [Effect] results in a shallower (and thus easier
     to reason about) embedding. -/

def Handler (E : Type → Type u) (M : Type → Type v) := ∀ A, E A → M A

def interp {M : Type → Type v} {E : Type → Type u} {R : Type} [Pure M] [Bind M]
    (handler : Handler E M) : Ecomp E R → M R
  | .Pure r => pure r
  | .Effect e k => handler _ e >>= fun v => interp handler (k v)

def ecompBind {E : Type → Type u} (A B : Type) (kx : A → Ecomp E B) : Ecomp E A → Ecomp E B
  | .Pure r => kx r
  | .Effect e k => .Effect e (fun c => ecompBind _ _ kx (k c))

instance ecomp_Monad (E : Type → Type u) : Monad (Ecomp E) where
  pure := Ecomp.Pure
  bind x kx := ecompBind _ _ kx x

instance ecomp_Inhabited (E : Type → Type u) (R : Type) [Inhabited R] : Inhabited (Ecomp E R) :=
  ⟨.Pure default⟩

@[simp] theorem ecompBind_Pure {E : Type → Type u} {A B : Type} (a : A) (kx : A → Ecomp E B) :
    (Ecomp.Pure a >>= kx) = kx a := rfl

@[simp] theorem ecompBind_Effect {E : Type → Type u} {A B C : Type} (e : E C) (k : C → Ecomp E A)
    (kx : A → Ecomp E B) :
    (Ecomp.Effect e k >>= kx) = Ecomp.Effect e (fun c => k c >>= kx) := rfl

@[simp] theorem ecomp_pure_eq {E : Type → Type u} {A : Type} (a : A) :
    (pure a : Ecomp E A) = Ecomp.Pure a := rfl

/-! ### Relations (state transitions) -/

/-- `relation.t Σ A`: a transition from a state to a new state, returning an `A`. -/
def Relation (S : Type) (A : Type) : Type := S → S → A → Prop

/-- Establish monadicity of relation.t. -/
instance relation_Monad (S : Type) : Monad (Relation S) where
  pure a := fun σ σ' a' => a = a' ∧ σ' = σ
  bind ma kmb := fun σ σ' b => ∃ a σmiddle, ma σ σmiddle a ∧ kmb a σmiddle σ' b

theorem relation_pure_def {S A : Type} (a : A) (σ σ' : S) (a' : A) :
    (pure a : Relation S A) σ σ' a' = (a = a' ∧ σ' = σ) := rfl

theorem relation_bind_def {S A B : Type} (ma : Relation S A) (kmb : A → Relation S B)
    (σ σ' : S) (b : B) :
    (ma >>= kmb) σ σ' b = ∃ a σmiddle, ma σ σmiddle a ∧ kmb a σmiddle σ' b := rfl

/-! ### The etcd state -/

-- https://etcd.io/docs/v3.6/learning/api/
structure KeyValue where
  mk ::
  key : List w8
  create_revision : w64
  mod_revision : w64
  version : w64
  value : List w8
  lease : w64

structure EtcdState where
  mk ::
  revision : w64
  compact_revision : w64
  key_values : GMap w64 (GMap (List w8) KeyValue)
  /- XXX: Though the docs don't explain or guarantee this, this tracks lease
     IDs that have been given out previously to avoid reusing LeaseIDs. If
     reuse were allowed, it's possible that a lease expires & its keys are
     deleted, then another client creates a lease with the same ID and
     attaches the same keys, after which the first expired client would
     incorrectly see its keys still attached with its leaseid. -/
  used_lease_ids : GSet w64
  /-- If an ID is used but not in here, then it has been expired. -/
  lease_expiration : GMap w64 w64

/-- Effects for etcd specification. -/
inductive EtcdE : Type → Type 1 where
  | SuchThat {A : Type} (pred : A → Prop) : EtcdE A
  | GetState : EtcdE EtcdState
  | SetState (σ' : EtcdState) : EtcdE Unit
  | GetTime : EtcdE w64
  | Assume (b : Prop) : EtcdE Unit
  | Assert (b : Prop) : EtcdE Unit

/-! Monads can't be composed in general. `exnT M R` is `M ∘ (R ⊕ ·)`. -/

def ExnT (M : Type → Type v) (R : Type) (A : Type) : Type v := M (R ⊕ A)

instance exception_compose_Monad {M : Type → Type v} [Monad M] (R : Type) : Monad (ExnT M R) where
  pure a := (pure (Sum.inr a) : M (R ⊕ _))
  bind a kmb := (bind (m := M) a (fun ea => match ea with
    | .inl r => pure (Sum.inl r)
    | .inr a => kmb a) : M (R ⊕ _))

inductive WithExceptionE (R : Type) (E : Type → Type u) (A : Type) : Type u where
  | Throw (r : R)
  | Ok (e : E A)

def handleExceptionE {R : Type} {E : Type → Type u} :
    Handler (WithExceptionE R E) (ExnT (Ecomp E) R) :=
  fun _A e =>
    match e with
    | .Throw r => Ecomp.Pure (Sum.inl r)
    | .Ok e => Ecomp.Effect e (fun x => Ecomp.Pure (Sum.inr x))

/-- Handle etcd effects with the `relation.t EtcdState.t` monad. -/
def HandleEtcdE (t : w64) : Handler EtcdE (Relation EtcdState) :=
  fun _A e =>
    match e with
    | .SuchThat pred => fun σ σ' a => pred a ∧ σ' = σ
    | .GetState => fun σ σ' ret => σ' = σ ∧ ret = σ
    | .SetState σnew => fun _σ σ' _ret => σ' = σnew
    | .GetTime => fun σ σ' tret => tret = t ∧ σ' = σ
    | .Assume P => fun σ σ' _tret => P ∧ σ = σ'
    | .Assert P => fun σ σ' _tret => (P → σ = σ')
    /- FIXME: the [Assert] case is a bit sketchy, and probably
       wrong in some way; it implies that after an assert statement, there *is*
       some next state, but nothing about that state is known unless `P` is
       true. -/

def «do» {E : Type → Type u} {R : Type} (e : E R) : Ecomp E R := .Effect e Ecomp.Pure

/-- This covers all transitions of the etcd state that are not tied to a client
API call, e.g. lease expiration happens "in the background". This will be called
as a prelude by all the client-facing operations, since it is sound to delay
running spontaneous transitions until they would actually affect the client.
This relies on `SpontaneousTransition` being monotonic: if a transition can
happen at time `t`, then for any `t' > t` it must be possible at `t'` as well.
The following lemma confirms this. -/
def SingleSpontaneousTransition : Ecomp EtcdE Unit := do
  -- expire some lease
  -- XXX: this is a "partial" transition: it is not always possible to expire a lease.
  let time ← «do» EtcdE.GetTime
  let σ ← «do» EtcdE.GetState
  let lease_id ← «do» (EtcdE.SuchThat (fun l => ∃ exp, σ.lease_expiration !! l = some exp ∧
                                       uint.nat time > uint.nat exp))
  -- FIXME: delete attached keys
  «do» (EtcdE.SetState { σ with lease_expiration := GMap.delete lease_id σ.lease_expiration })

theorem SingleSpontaneousTransition_monotonic (time time' : w64) (σ σ' : EtcdState) :
    uint.nat time < uint.nat time' →
    interp (HandleEtcdE time) SingleSpontaneousTransition σ σ' () →
    interp (HandleEtcdE time') SingleSpontaneousTransition σ σ' () := by
  intro Htime Hstep
  simp only [SingleSpontaneousTransition, «do», ecompBind_Effect, ecompBind_Pure, interp,
    HandleEtcdE] at Hstep ⊢
  obtain ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, l, _, ⟨⟨exp, Hexp, Hlt⟩, rfl⟩, _, _, rfl, Hret⟩ :=
    Hstep
  exact ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, l, _, ⟨⟨exp, Hexp, by omega⟩, rfl⟩, _, _, rfl, Hret⟩

/-- This does a non-deterministic number of spontaneous transitions. -/
def SpontaneousTransition : Ecomp EtcdE Unit := do
  let num_steps ← «do» (EtcdE.SuchThat (fun (_ : Nat) => True))
  Nat.repeat (fun p => do SingleSpontaneousTransition; p) num_steps (pure ())

structure LeaseGrantRequest where
  mk ::
  TTL : w64
  ID : w64

structure LeaseGrantResponse where
  mk ::
  TTL : w64
  ID : w64

def LeaseGrant (req : LeaseGrantRequest) : Ecomp EtcdE LeaseGrantResponse := do
  -- FIXME: add this back
  -- SpontaneousTransition
  -- req.TTL is advisory, so it is ignored.
  let ttl ← «do» (EtcdE.SuchThat (fun (ttl : w64) => uint.nat ttl > 0))
  let σ ← «do» EtcdE.GetState
  let lease_id ← (if req.ID = W64 0 then
                    «do» (EtcdE.SuchThat (fun lease_id => lease_id ∉ σ.used_lease_ids))
                  else do
                    «do» (EtcdE.Assert (req.ID ∉ σ.used_lease_ids))
                    pure req.ID)
  let time ← «do» EtcdE.GetTime
  let σ := { σ with used_lease_ids := {[lease_id]} ∪ σ.used_lease_ids }
  let σ := { σ with lease_expiration := <[lease_id := time + ttl]> σ.lease_expiration }
  «do» (EtcdE.SetState σ)
  pure (LeaseGrantResponse.mk lease_id ttl)

structure LeaseKeepAliveRequest where
  mk ::
  ID : w64

structure LeaseKeepAliveResponse where
  mk ::
  TTL : w64
  ID : w64

/-- If the lease is expired, returns TTL=0. The precise semantics of lease
renewal are not settled. -/
def LeaseKeepAlive (req : LeaseKeepAliveRequest) : Ecomp EtcdE LeaseKeepAliveResponse := do
  SpontaneousTransition
  let σ ← «do» EtcdE.GetState
  /- This is conservative. lessor.go looks like it avoids renewing a lease if
     its expiration is in the past, but it's actually possible for it to still
     renew something that would have been considered expired here because of
     leader change, which sets expiry to "forever" before restarting it upon
     promotion. -/
  match σ.lease_expiration !! req.ID with
  | none => pure (LeaseKeepAliveResponse.mk (W64 0) req.ID)
  | some expiration => do
      let ttl ← «do» (EtcdE.SuchThat (fun (_ : w64) => True))
      let time ← «do» EtcdE.GetTime
      let new_expiration_lower := time + ttl
      let new_expiration := if sint.Z new_expiration_lower < sint.Z expiration then
                              expiration
                            else
                              new_expiration_lower
      «do» (EtcdE.SetState { σ with lease_expiration :=
        <[req.ID := new_expiration]> σ.lease_expiration })
      pure (LeaseKeepAliveResponse.mk ttl req.ID)

namespace RangeRequest
-- sort order
def NONE : w32 := W32 0
def ASCEND : w32 := W32 1
def DESCEND : w32 := W32 2

-- sort target
def KEY : w32 := W32 0
def VERSION : w32 := W32 1
def MOD : w32 := W32 2
def VALUE : w32 := W32 3

structure _root_.Perennial.go_etcd_io.etcd.client.v3_proof.RangeRequest where
  mk ::
  key : List w8
  range_end : List w8
  limit : w64
  revision : w64
  sort_order : w32
  sort_target : w32
  serializable : Bool
  keys_only : Bool
  count_only : Bool
  min_mod_revision : w64
  max_mod_revision : w64
  min_create_revision : w64
  max_create_revision : w64

def default : RangeRequest :=
  mk [] [] (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0) (W64 0)
end RangeRequest

structure RangeResponse where
  mk ::
  kvs : List KeyValue
  more : Bool
  count : w64

inductive Error where
  | Bad (msg : GoString)

/-
txn.go:152 which calls kvstore_txn.go:72

XXX: The etcd documentation states that if the sort_order is None, there will
be "no sorting". In fact, the implementation seems to *always* return sorted
results, as of https://github.com/etcd-io/etcd/issues/6671

Nonetheless, this model is conservative and does not guarantee sortedness if
sort_order == None.
-/

def RelationPullback {A B : Type} (f : A → B) (R : B → B → Prop) : A → A → Prop :=
  fun a1 a2 => R (f a1) (f a2)

open WithExceptionE (Throw Ok) in
def Range (req : RangeRequest) : Ecomp EtcdE (Error ⊕ RangeResponse) :=
show ExnT (Ecomp EtcdE) Error RangeResponse from
interp handleExceptionE (show Ecomp (WithExceptionE Error EtcdE) RangeResponse from do
  «do» (Ok (EtcdE.Assert (req.serializable = false)))
  let σ ← «do» (Ok EtcdE.GetState)
  let current_revision := σ.revision
  (if sint.Z req.revision > sint.Z current_revision then
     «do» (Throw (Error.Bad go!"Future revision"))
   else pure ())
  let rev := (if sint.Z req.revision < 0 then current_revision else req.revision)
  let kv_map := (σ.key_values !! rev).getD ∅
  let kvs ← «do» (Ok (EtcdE.SuchThat (fun (kvs : List KeyValue) =>
                  match req.range_end with
                  | [] => -- just the one key
                      (∀ kv, kv ∈ kvs ↔ kv_map !! req.key = some kv)
                  | _ =>
                      if req.range_end = [W8 0] then
                        (∀ kv, kv ∈ kvs ↔
                               (go.GoStringLe req.key kv.key ∧
                                kv_map !! kv.key = some kv))
                      else
                        (∀ kv, kv ∈ kvs ↔
                               (go.GoStringLe req.key kv.key ∧
                                go.GoStringLt kv.key req.range_end ∧
                                kv_map !! kv.key = some kv)))))
  let kvs :=
    (if req.max_mod_revision ≠ W64 0 then
       kvs.filter (fun kv => decide (sint.Z kv.mod_revision ≤ sint.Z req.max_mod_revision))
     else kvs)
  let kvs :=
    (if req.min_mod_revision ≠ W64 0 then
       kvs.filter (fun kv => decide (sint.Z req.min_mod_revision ≤ sint.Z kv.mod_revision))
     else kvs)
  let kvs :=
    (if req.max_create_revision ≠ W64 0 then
       kvs.filter (fun kv => decide (sint.Z kv.create_revision ≤ sint.Z req.max_create_revision))
     else kvs)
  let kvs :=
    (if req.min_create_revision ≠ W64 0 then
       kvs.filter (fun kv => decide (sint.Z req.min_create_revision ≤ sint.Z kv.create_revision))
     else kvs)
  -- for sorting in ascending order; descending means flipping the order of the list.
  let sort_relation ← (show Ecomp _ (KeyValue → KeyValue → Prop) from
    match uint.Z req.sort_target with
    | 0 => pure (RelationPullback KeyValue.key go.GoStringLt) -- KEY
    | 1 => pure (RelationPullback (sint.Z ∘ KeyValue.version) (· < ·)) -- VERSION
    | 2 => pure (RelationPullback (sint.Z ∘ KeyValue.create_revision) (· < ·)) -- CREATE
    | 3 => pure (RelationPullback (sint.Z ∘ KeyValue.mod_revision) (· < ·)) -- MOD
    | 4 => pure (RelationPullback KeyValue.value go.GoStringLt) -- VALUE
    | _ => do «do» (Ok (EtcdE.Assert False)); «do» (Throw (Error.Bad go!"unreachable")))
  let kvs_sorted ← «do» (Ok (EtcdE.SuchThat (fun kvs_sorted =>
                     List.Pairwise sort_relation kvs_sorted ∧ List.Perm kvs kvs_sorted)))
  let kvs ← (show Ecomp _ (List KeyValue) from
    match uint.Z req.sort_order with
    | 0 => pure kvs -- NONE; XXX: the etcd implementation seems to sort even in this case.
    | 1 => pure kvs_sorted -- ASCEND
    | 2 => pure kvs_sorted.reverse -- DESCEND
    | _ => do «do» (Ok (EtcdE.Assert False)); «do» (Throw (Error.Bad go!"unreachable")))
  if req.count_only then
    pure (RangeResponse.mk [] false (W64 kvs.length))
  else do
    let kvs_limited ← (show Ecomp _ (List KeyValue) from
      if sint.Z req.limit = 0 then
        pure kvs
      else if sint.Z req.limit > 0 then
        pure (kvs.take (sint.Z req.limit).toNat)
      else do
        «do» (Ok (EtcdE.Assert False)); «do» (Throw (Error.Bad go!"unreachable")))
    pure (RangeResponse.mk kvs_limited (decide (kvs_limited.length < kvs.length))
      (W64 kvs.length))
  -- XXX: keys_only is not currently handled.
  )

namespace PutRequest
structure _root_.Perennial.go_etcd_io.etcd.client.v3_proof.PutRequest where
  mk ::
  key : List w8
  value : List w8
  lease : w64
  prev_kv : Bool
  ignore_value : Bool
  ignore_lease : Bool

def default : PutRequest := mk [] [] (W64 0) false false false
end PutRequest

structure PutResponse where
  mk ::
  -- TODO: add response header
  -- header : ResponseHeader.t;
  prev_kv : Option KeyValue

open WithExceptionE (Throw Ok) in
/-- server/etcdserver/txn.go:58, then server/storage/mvcc/kvstore_txn.go:196 -/
def Put (req : PutRequest) : Ecomp EtcdE (Error ⊕ PutResponse) :=
show ExnT (Ecomp EtcdE) Error PutResponse from
interp handleExceptionE (show Ecomp (WithExceptionE Error EtcdE) PutResponse from do
  let σ ← «do» (Ok EtcdE.GetState)
  let kvs := (σ.key_values !! σ.revision).getD ∅
  -- NOTE: could use [Range] here.
  let prev_kv := kvs !! req.key

  -- compute value and lease, possibly throwing an error.
  let value ← (if req.ignore_value then
                 (prev_kv.map (Ecomp.Pure ∘ KeyValue.value)).getD
                   («do» (Throw (Error.Bad go!"Key not found")))
               else pure req.value)
  let lease ← (if req.ignore_lease then
                 (prev_kv.map (Ecomp.Pure ∘ KeyValue.lease)).getD
                   («do» (Throw (Error.Bad go!"Key not found")))
               else pure req.lease)

  let ret_prev_kv := (if req.prev_kv then prev_kv else none)
  let prev_ver := (prev_kv.map KeyValue.version).getD (W64 0)
  let ver := prev_ver + W64 1 -- should this handle overflow?
  let mod_revision := σ.revision + W64 1
  let create_revision := (prev_kv.map KeyValue.create_revision).getD mod_revision
  let new_kv := KeyValue.mk req.key create_revision mod_revision ver value lease
  let σ := { σ with key_values := <[mod_revision := <[req.key := new_kv]> kvs]> σ.key_values }
  let σ := { σ with revision := mod_revision }
  /- updating [key_values] handles attaching/detaching leases, since the map
     itself defines the association from LeaseID to Key. -/
  «do» (Ok (EtcdE.SetState σ))
  pure (PutResponse.mk ret_prev_kv))

structure DeleteRangeRequest where
  mk ::
  key : List w8
  range_end : List w8
  prev_kv : Bool

structure DeleteRangeResponse where
  mk ::
  prev_kvs : List KeyValue
deriving Inhabited

/-- Uninterpreted. -/
opaque DeleteRange (req : DeleteRangeRequest) : Ecomp EtcdE DeleteRangeResponse

namespace Compare

-- FIXME: the etcd documentation is out-of-date for this.
inductive TargetUnion where
  | Version (version : w64)
  | CreateRevision (create_revision : w64)
  | ModRevision (mod_revision : w64)
  | Value (value : List w8)
  | Lease (lease : w64)

structure _root_.Perennial.go_etcd_io.etcd.client.v3_proof.Compare where
  mk ::
  result : w32 -- CompareResult
  target : w32 -- CompareTarget
  key : List w8
  target_union : TargetUnion
  range_end : List w8
end Compare

inductive RequestOp where
  | Range (request_range : RangeRequest)
  | Put (request_put : PutRequest)
  | DeleteRange (request_delete_range : DeleteRangeRequest)
  -- | Txn (request_txn : TxnRequest.t)
  -- This does not support Txn as a RequestOp.

inductive ResponseOp where
  | Range (response_range : RangeResponse)
  | Put (response_put : PutResponse)
  | DeleteRange (response_delete_range : DeleteRangeResponse)
  -- | Txn (response_txn : TxnResponse.t)
  -- This does not support Txn as a ResponseOp.

-- FIXME: etcd documentation out of date.
structure TxnRequest where
  mk ::
  compare : List Compare
  success : List RequestOp
  failure : List RequestOp

structure TxnResponse where
  mk ::
  succeeded : Bool
  responses : List ResponseOp
deriving Inhabited

/- Q: What is the meaning of this from rpc.proto:
  // It is not allowed to modify the same key several times within one txn.
  In particular, does Txn return an error if the ops try to modify the same key
  multiple times? Or does the Txn coalesce that into one modification? -/
/-- Uninterpreted. -/
opaque Txn (req : TxnRequest) : Ecomp EtcdE TxnResponse

end go_etcd_io.etcd.client.v3_proof

end Perennial
