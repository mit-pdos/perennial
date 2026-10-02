/-
Port of `new/proof/go_etcd_io/etcd/client/v3_proof/model.v`: a pure model of
etcd's KV/lease semantics as computations (`ecomp`) over effects (`etcdE`).

Differences from Rocq:
* Everything lives in `namespace go_etcd_io.etcd.client.v3_proof` (Rocq: global
  scope), to avoid clashing with generic names such as `Error` or `interp`.
* Rocq's `MRet`/`MBind` instances become Lean `Monad` instances, so `do`
  notation works. `ecomp E` and `relation.t S` are monads; Rocq's
  `M ∘ (sum R)` is `exnT M R`.
* Since effects quantify over types, `etcdE : Type → Type 1` and
  `ecomp E R : Type 1` (Rocq uses universe polymorphism implicitly).
* `relation.t` (Rocq `Perennial.Helpers.Transitions`) is not ported to
  `Perennial/Std`; the (only) part needed here is defined locally.
* `do` is a Lean keyword, so it is `«do»`.
* The `Settable` instances are dropped: Lean has record-update syntax.
* `RangeRequest.default`/`PutRequest.default` use the zero values directly
  rather than `zero_val` (so they do not need `ffi_syntax`).
* `StronglySorted` is `List.Pairwise`, `Permutation` is `List.Perm`, stdpp
  `filter` is `List.filter`, `default d o` is `o.getD d`.
* `DeleteRange` and `Txn` are `Admitted` definitions in Rocq; here they are
  `opaque` constants (uninterpreted, no axiom or `sorry`).
-/
import Perennial.Proof.ProofPrelude
import Perennial.Golang.Defn.String

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace go_etcd_io.etcd.client.v3_proof

universe u v

inductive ecomp (E : Type → Type u) (R : Type) : Type (max 1 u) where
  | Pure (r : R) : ecomp E R
  | Effect {A : Type} (e : E A) (k : A → ecomp E R) : ecomp E R
  /- Having a separate [Bind] permits binding at pure computation steps,
     whereas binding only in [Effect] results in a shallower (and thus easier
     to reason about) embedding. -/

def Handler (E : Type → Type u) (M : Type → Type v) := ∀ A, E A → M A

def interp {M : Type → Type v} {E : Type → Type u} {R : Type} [Pure M] [Bind M]
    (handler : Handler E M) : ecomp E R → M R
  | .Pure r => pure r
  | .Effect e k => handler _ e >>= fun v => interp handler (k v)

def ecomp_bind {E : Type → Type u} (A B : Type) (kx : A → ecomp E B) : ecomp E A → ecomp E B
  | .Pure r => kx r
  | .Effect e k => .Effect e (fun c => ecomp_bind _ _ kx (k c))

instance ecomp_Monad (E : Type → Type u) : Monad (ecomp E) where
  pure := ecomp.Pure
  bind x kx := ecomp_bind _ _ kx x

instance ecomp_Inhabited (E : Type → Type u) (R : Type) [Inhabited R] : Inhabited (ecomp E R) :=
  ⟨.Pure default⟩

@[simp] theorem ecomp_bind_Pure {E : Type → Type u} {A B : Type} (a : A) (kx : A → ecomp E B) :
    (ecomp.Pure a >>= kx) = kx a := rfl

@[simp] theorem ecomp_bind_Effect {E : Type → Type u} {A B C : Type} (e : E C) (k : C → ecomp E A)
    (kx : A → ecomp E B) :
    (ecomp.Effect e k >>= kx) = ecomp.Effect e (fun c => k c >>= kx) := rfl

@[simp] theorem ecomp_pure_eq {E : Type → Type u} {A : Type} (a : A) :
    (pure a : ecomp E A) = ecomp.Pure a := rfl

/-! ### Relations (Rocq `Perennial.Helpers.Transitions`) -/

/-- `relation.t Σ A`: a transition from a state to a new state, returning an `A`. -/
def relation.t (S : Type) (A : Type) : Type := S → S → A → Prop

/-- Establish monadicity of relation.t. Rocq `relation_mret`/`relation_mbind`. -/
instance relation_Monad (S : Type) : Monad (relation.t S) where
  pure a := fun σ σ' a' => a = a' ∧ σ' = σ
  bind ma kmb := fun σ σ' b => ∃ a σmiddle, ma σ σmiddle a ∧ kmb a σmiddle σ' b

theorem relation_pure_def {S A : Type} (a : A) (σ σ' : S) (a' : A) :
    (pure a : relation.t S A) σ σ' a' = (a = a' ∧ σ' = σ) := rfl

theorem relation_bind_def {S A B : Type} (ma : relation.t S A) (kmb : A → relation.t S B)
    (σ σ' : S) (b : B) :
    (ma >>= kmb) σ σ' b = ∃ a σmiddle, ma σ σmiddle a ∧ kmb a σmiddle σ' b := rfl

/-! ### The etcd state -/

-- https://etcd.io/docs/v3.6/learning/api/
namespace KeyValue
structure t where
  mk ::
  key : List w8
  create_revision : w64
  mod_revision : w64
  version : w64
  value : List w8
  lease : w64
end KeyValue

namespace EtcdState
structure t where
  mk ::
  revision : w64
  compact_revision : w64
  key_values : gmap w64 (gmap (List w8) KeyValue.t)
  /- XXX: Though the docs don't explain or guarantee this, this tracks lease
     IDs that have been given out previously to avoid reusing LeaseIDs. If
     reuse were allowed, it's possible that a lease expires & its keys are
     deleted, then another client creates a lease with the same ID and
     attaches the same keys, after which the first expired client would
     incorrectly see its keys still attached with its leaseid. -/
  used_lease_ids : gset w64
  /-- If an ID is used but not in here, then it has been expired. -/
  lease_expiration : gmap w64 w64
end EtcdState

/-- Effects for etcd specification. -/
inductive etcdE : Type → Type 1 where
  | SuchThat {A : Type} (pred : A → Prop) : etcdE A
  | GetState : etcdE EtcdState.t
  | SetState (σ' : EtcdState.t) : etcdE Unit
  | GetTime : etcdE w64
  | Assume (b : Prop) : etcdE Unit
  | Assert (b : Prop) : etcdE Unit

/-! Monads can't be composed in general (see the Rocq source for a discussion
of itree exceptions). `exnT M R` is Rocq's `M ∘ (sum R)`. -/

def exnT (M : Type → Type v) (R : Type) (A : Type) : Type v := M (R ⊕ A)

instance exception_compose_Monad {M : Type → Type v} [Monad M] (R : Type) : Monad (exnT M R) where
  pure a := (pure (Sum.inr a) : M (R ⊕ _))
  bind a kmb := (bind (m := M) a (fun ea => match ea with
    | .inl r => pure (Sum.inl r)
    | .inr a => kmb a) : M (R ⊕ _))

inductive with_exceptionE (R : Type) (E : Type → Type u) (A : Type) : Type u where
  | Throw (r : R)
  | Ok (e : E A)

def handle_exceptionE {R : Type} {E : Type → Type u} :
    Handler (with_exceptionE R E) (exnT (ecomp E) R) :=
  fun _A e =>
    match e with
    | .Throw r => ecomp.Pure (Sum.inl r)
    | .Ok e => ecomp.Effect e (fun x => ecomp.Pure (Sum.inr x))

/-- Handle etcd effects with the `relation.t EtcdState.t` monad. -/
def handle_etcdE (t : w64) : Handler etcdE (relation.t EtcdState.t) :=
  fun _A e =>
    match e with
    | .SuchThat pred => fun σ σ' a => pred a ∧ σ' = σ
    | .GetState => fun σ σ' ret => σ' = σ ∧ ret = σ
    | .SetState σnew => fun _σ σ' _ret => σ' = σnew
    | .GetTime => fun σ σ' tret => tret = t ∧ σ' = σ
    | .Assume P => fun σ σ' _tret => P ∧ σ = σ'
    | .Assert P => fun σ σ' _tret => (P → σ = σ')
    /- FIXME (from Rocq): the [Assert] case is a bit sketchy, and probably
       wrong in some way; it implies that after an assert statement, there *is*
       some next state, but nothing about that state is known unless `P` is
       true. -/

def «do» {E : Type → Type u} {R : Type} (e : E R) : ecomp E R := .Effect e ecomp.Pure

/-- This covers all transitions of the etcd state that are not tied to a client
API call, e.g. lease expiration happens "in the background". This will be called
as a prelude by all the client-facing operations, since it is sound to delay
running spontaneous transitions until they would actually affect the client.
This relies on `SpontaneousTransition` being monotonic: if a transition can
happen at time `t`, then for any `t' > t` it must be possible at `t'` as well.
The following lemma confirms this. -/
def SingleSpontaneousTransition : ecomp etcdE Unit := do
  -- expire some lease
  -- XXX: this is a "partial" transition: it is not always possible to expire a lease.
  let time ← «do» etcdE.GetTime
  let σ ← «do» etcdE.GetState
  let lease_id ← «do» (etcdE.SuchThat (fun l => ∃ exp, σ.lease_expiration !! l = some exp ∧
                                       uint.nat time > uint.nat exp))
  -- FIXME: delete attached keys
  «do» (etcdE.SetState { σ with lease_expiration := gmap.delete lease_id σ.lease_expiration })

theorem SingleSpontaneousTransition_monotonic (time time' : w64) (σ σ' : EtcdState.t) :
    uint.nat time < uint.nat time' →
    interp (handle_etcdE time) SingleSpontaneousTransition σ σ' () →
    interp (handle_etcdE time') SingleSpontaneousTransition σ σ' () := by
  intro Htime Hstep
  simp only [SingleSpontaneousTransition, «do», ecomp_bind_Effect, ecomp_bind_Pure, interp,
    handle_etcdE] at Hstep ⊢
  obtain ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, l, _, ⟨⟨exp, Hexp, Hlt⟩, rfl⟩, _, _, rfl, Hret⟩ :=
    Hstep
  exact ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, l, _, ⟨⟨exp, Hexp, by omega⟩, rfl⟩, _, _, rfl, Hret⟩

/-- This does a non-deterministic number of spontaneous transitions. -/
def SpontaneousTransition : ecomp etcdE Unit := do
  let num_steps ← «do» (etcdE.SuchThat (fun (_ : Nat) => True))
  Nat.repeat (fun p => do SingleSpontaneousTransition; p) num_steps (pure ())

namespace LeaseGrantRequest
structure t where
  mk ::
  TTL : w64
  ID : w64
end LeaseGrantRequest

namespace LeaseGrantResponse
structure t where
  mk ::
  TTL : w64
  ID : w64
end LeaseGrantResponse

def LeaseGrant (req : LeaseGrantRequest.t) : ecomp etcdE LeaseGrantResponse.t := do
  -- FIXME (from Rocq): add this back
  -- SpontaneousTransition
  -- req.TTL is advisory, so it is ignored.
  let ttl ← «do» (etcdE.SuchThat (fun (ttl : w64) => uint.nat ttl > 0))
  let σ ← «do» etcdE.GetState
  let lease_id ← (if req.ID = W64 0 then
                    «do» (etcdE.SuchThat (fun lease_id => lease_id ∉ σ.used_lease_ids))
                  else do
                    «do» (etcdE.Assert (req.ID ∉ σ.used_lease_ids))
                    pure req.ID)
  let time ← «do» etcdE.GetTime
  let σ := { σ with used_lease_ids := {[lease_id]} ∪ σ.used_lease_ids }
  let σ := { σ with lease_expiration := <[lease_id := time + ttl]> σ.lease_expiration }
  «do» (etcdE.SetState σ)
  pure (LeaseGrantResponse.t.mk lease_id ttl)

namespace LeaseKeepAliveRequest
structure t where
  mk ::
  ID : w64
end LeaseKeepAliveRequest

namespace LeaseKeepAliveResponse
structure t where
  mk ::
  TTL : w64
  ID : w64
end LeaseKeepAliveResponse

/-- If the lease is expired, returns TTL=0. See the Rocq source for questions
about the precise semantics of lease renewal. -/
def LeaseKeepAlive (req : LeaseKeepAliveRequest.t) : ecomp etcdE LeaseKeepAliveResponse.t := do
  SpontaneousTransition
  let σ ← «do» etcdE.GetState
  /- This is conservative. lessor.go looks like it avoids renewing a lease if
     its expiration is in the past, but it's actually possible for it to still
     renew something that would have been considered expired here because of
     leader change, which sets expiry to "forever" before restarting it upon
     promotion. -/
  match σ.lease_expiration !! req.ID with
  | none => pure (LeaseKeepAliveResponse.t.mk (W64 0) req.ID)
  | some expiration => do
      let ttl ← «do» (etcdE.SuchThat (fun (_ : w64) => True))
      let time ← «do» etcdE.GetTime
      let new_expiration_lower := time + ttl
      let new_expiration := if sint.Z new_expiration_lower < sint.Z expiration then
                              expiration
                            else
                              new_expiration_lower
      «do» (etcdE.SetState { σ with lease_expiration :=
        <[req.ID := new_expiration]> σ.lease_expiration })
      pure (LeaseKeepAliveResponse.t.mk ttl req.ID)

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

structure t where
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

def default : t :=
  t.mk [] [] (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0) (W64 0)
end RangeRequest

namespace RangeResponse
structure t where
  mk ::
  kvs : List KeyValue.t
  more : Bool
  count : w64
end RangeResponse

inductive Error where
  | Bad (msg : go_string)

/-
txn.go:152 which calls kvstore_txn.go:72

XXX: The etcd documentation states that if the sort_order is None, there will
be "no sorting". In fact, the implementation seems to *always* return sorted
results, as of https://github.com/etcd-io/etcd/issues/6671

Nonetheless, this model is conservative and does not guarantee sortedness if
sort_order == None.
-/

def relation_pullback {A B : Type} (f : A → B) (R : B → B → Prop) : A → A → Prop :=
  fun a1 a2 => R (f a1) (f a2)

open with_exceptionE (Throw Ok) in
def Range (req : RangeRequest.t) : ecomp etcdE (Error ⊕ RangeResponse.t) :=
show exnT (ecomp etcdE) Error RangeResponse.t from
interp handle_exceptionE (show ecomp (with_exceptionE Error etcdE) RangeResponse.t from do
  «do» (Ok (etcdE.Assert (req.serializable = false)))
  let σ ← «do» (Ok etcdE.GetState)
  let current_revision := σ.revision
  (if sint.Z req.revision > sint.Z current_revision then
     «do» (Throw (Error.Bad go!"Future revision"))
   else pure ())
  let rev := (if sint.Z req.revision < 0 then current_revision else req.revision)
  let kv_map := (σ.key_values !! rev).getD ∅
  let kvs ← «do» (Ok (etcdE.SuchThat (fun (kvs : List KeyValue.t) =>
                  match req.range_end with
                  | [] => -- just the one key
                      (∀ kv, kv ∈ kvs ↔ kv_map !! req.key = some kv)
                  | _ =>
                      if req.range_end = [W8 0] then
                        (∀ kv, kv ∈ kvs ↔
                               (go.go_string_le req.key kv.key ∧
                                kv_map !! kv.key = some kv))
                      else
                        (∀ kv, kv ∈ kvs ↔
                               (go.go_string_le req.key kv.key ∧
                                go.go_string_lt kv.key req.range_end ∧
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
  let sort_relation ← (show ecomp _ (KeyValue.t → KeyValue.t → Prop) from
    match uint.Z req.sort_target with
    | 0 => pure (relation_pullback KeyValue.t.key go.go_string_lt) -- KEY
    | 1 => pure (relation_pullback (sint.Z ∘ KeyValue.t.version) (· < ·)) -- VERSION
    | 2 => pure (relation_pullback (sint.Z ∘ KeyValue.t.create_revision) (· < ·)) -- CREATE
    | 3 => pure (relation_pullback (sint.Z ∘ KeyValue.t.mod_revision) (· < ·)) -- MOD
    | 4 => pure (relation_pullback KeyValue.t.value go.go_string_lt) -- VALUE
    | _ => do «do» (Ok (etcdE.Assert False)); «do» (Throw (Error.Bad go!"unreachable")))
  let kvs_sorted ← «do» (Ok (etcdE.SuchThat (fun kvs_sorted =>
                     List.Pairwise sort_relation kvs_sorted ∧ List.Perm kvs kvs_sorted)))
  let kvs ← (show ecomp _ (List KeyValue.t) from
    match uint.Z req.sort_order with
    | 0 => pure kvs -- NONE; XXX: the etcd implementation seems to sort even in this case.
    | 1 => pure kvs_sorted -- ASCEND
    | 2 => pure kvs_sorted.reverse -- DESCEND
    | _ => do «do» (Ok (etcdE.Assert False)); «do» (Throw (Error.Bad go!"unreachable")))
  if req.count_only then
    pure (RangeResponse.t.mk [] false (W64 kvs.length))
  else do
    let kvs_limited ← (show ecomp _ (List KeyValue.t) from
      if sint.Z req.limit = 0 then
        pure kvs
      else if sint.Z req.limit > 0 then
        pure (kvs.take (sint.Z req.limit).toNat)
      else do
        «do» (Ok (etcdE.Assert False)); «do» (Throw (Error.Bad go!"unreachable")))
    pure (RangeResponse.t.mk kvs_limited (decide (kvs_limited.length < kvs.length))
      (W64 kvs.length))
  -- XXX: keys_only is not currently handled.
  )

namespace PutRequest
structure t where
  mk ::
  key : List w8
  value : List w8
  lease : w64
  prev_kv : Bool
  ignore_value : Bool
  ignore_lease : Bool

def default : t := t.mk [] [] (W64 0) false false false
end PutRequest

namespace PutResponse
structure t where
  mk ::
  -- TODO: add response header
  -- header : ResponseHeader.t;
  prev_kv : Option KeyValue.t
end PutResponse

open with_exceptionE (Throw Ok) in
/-- server/etcdserver/txn.go:58, then server/storage/mvcc/kvstore_txn.go:196 -/
def Put (req : PutRequest.t) : ecomp etcdE (Error ⊕ PutResponse.t) :=
show exnT (ecomp etcdE) Error PutResponse.t from
interp handle_exceptionE (show ecomp (with_exceptionE Error etcdE) PutResponse.t from do
  let σ ← «do» (Ok etcdE.GetState)
  let kvs := (σ.key_values !! σ.revision).getD ∅
  -- NOTE: could use [Range] here.
  let prev_kv := kvs !! req.key

  -- compute value and lease, possibly throwing an error.
  let value ← (if req.ignore_value then
                 (prev_kv.map (ecomp.Pure ∘ KeyValue.t.value)).getD
                   («do» (Throw (Error.Bad go!"Key not found")))
               else pure req.value)
  let lease ← (if req.ignore_lease then
                 (prev_kv.map (ecomp.Pure ∘ KeyValue.t.lease)).getD
                   («do» (Throw (Error.Bad go!"Key not found")))
               else pure req.lease)

  let ret_prev_kv := (if req.prev_kv then prev_kv else none)
  let prev_ver := (prev_kv.map KeyValue.t.version).getD (W64 0)
  let ver := prev_ver + W64 1 -- should this handle overflow?
  let mod_revision := σ.revision + W64 1
  let create_revision := (prev_kv.map KeyValue.t.create_revision).getD mod_revision
  let new_kv := KeyValue.t.mk req.key create_revision mod_revision ver value lease
  let σ := { σ with key_values := <[mod_revision := <[req.key := new_kv]> kvs]> σ.key_values }
  let σ := { σ with revision := mod_revision }
  /- updating [key_values] handles attaching/detaching leases, since the map
     itself defines the association from LeaseID to Key. -/
  «do» (Ok (etcdE.SetState σ))
  pure (PutResponse.t.mk ret_prev_kv))

namespace DeleteRangeRequest
structure t where
  mk ::
  key : List w8
  range_end : List w8
  prev_kv : Bool
end DeleteRangeRequest

namespace DeleteRangeResponse
structure t where
  mk ::
  prev_kvs : List KeyValue.t
deriving Inhabited
end DeleteRangeResponse

/-- Rocq: Admitted (an opaque definition). -/
opaque DeleteRange (req : DeleteRangeRequest.t) : ecomp etcdE DeleteRangeResponse.t

namespace Compare

-- FIXME: the etcd documentation is out-of-date for this.
inductive TargetUnion where
  | Version (version : w64)
  | CreateRevision (create_revision : w64)
  | ModRevision (mod_revision : w64)
  | Value (value : List w8)
  | Lease (lease : w64)

structure t where
  mk ::
  result : w32 -- CompareResult
  target : w32 -- CompareTarget
  key : List w8
  target_union : TargetUnion
  range_end : List w8
end Compare

namespace RequestOp
inductive t where
  | Range (request_range : RangeRequest.t)
  | Put (request_put : PutRequest.t)
  | DeleteRange (request_delete_range : DeleteRangeRequest.t)
  -- | Txn (request_txn : TxnRequest.t)
  -- This does not support Txn as a RequestOp.
end RequestOp

namespace ResponseOp
inductive t where
  | Range (response_range : RangeResponse.t)
  | Put (response_put : PutResponse.t)
  | DeleteRange (response_delete_range : DeleteRangeResponse.t)
  -- | Txn (response_txn : TxnResponse.t)
  -- This does not support Txn as a ResponseOp.
end ResponseOp

namespace TxnRequest
-- FIXME: etcd documentation out of date.
structure t where
  mk ::
  compare : List Compare.t
  success : List RequestOp.t
  failure : List RequestOp.t
end TxnRequest

namespace TxnResponse
structure t where
  mk ::
  succeeded : Bool
  responses : List ResponseOp.t
deriving Inhabited
end TxnResponse

/- Q (from Rocq): What is the meaning of this from rpc.proto:
  // It is not allowed to modify the same key several times within one txn.
  In particular, does Txn return an error if the ops try to modify the same key
  multiple times? Or does the Txn coalesce that into one modification? -/
/-- Rocq: Admitted (an opaque definition). -/
opaque Txn (req : TxnRequest.t) : ecomp etcdE TxnResponse.t

end go_etcd_io.etcd.client.v3_proof

end Perennial
