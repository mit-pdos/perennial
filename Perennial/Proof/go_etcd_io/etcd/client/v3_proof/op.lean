/-
Port of `new/proof/go_etcd_io/etcd/client/v3_proof/op.v`.

Lean notes:
* Rocq's `clientv3G Σ` is an unbound (implicitly generalized) class; it is
  `[allG GF]` here.
* Rocq names the persistent points-to of `op.sort` `"%Hsort"`; it is not pure,
  so here it is `"#Hsort"`.
-/
import Perennial.Proof.go_etcd_io.etcd.client.v3_proof.base
import Perennial.Proof.go_etcd_io.etcd.client.v3_proof.definitions

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option goose.wp.extras true

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace go_etcd_io.etcd.client.v3_proof

/-- Abstraction of an etcd `Op`. -/
inductive Op.t where
  | Get (req : RangeRequest.t)
  | Put (req : PutRequest.t)
  | DeleteRange (req : DeleteRangeRequest.t)
  | Txn (req : TxnRequest.t)

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [allG GF]

local notation "pkg" => pkg_id.go_etcd_io.etcd.client.v3

def is_Op_RangeRequest (op : v3.Op.t) (req : RangeRequest.t) : IProp GF :=
  iprop(
  "%Ht" ∷ ⌜op.t' = W64 1⌝ ∗
  "#key" ∷ op.key' ↦*□ req.key ∗
  "#end" ∷ op.end' ↦*□ req.range_end ∗
  "%Hlimit" ∷ ⌜op.limit' = req.limit⌝ ∗
  "#Hsort" ∷
    op.sort' ↦□
      (v3.SortOption.t.mk (W64 (sint.Z req.sort_target)) (W64 (sint.Z req.sort_order))) ∗
  "%Hserializable" ∷ ⌜op.serializable' = req.serializable⌝ ∗
  "%HkeysOnly" ∷ ⌜op.keysOnly' = req.keys_only⌝ ∗
  "%HcountOnly" ∷ ⌜op.countOnly' = req.count_only⌝ ∗
  "%HminModRev" ∷ ⌜op.minModRev' = req.min_mod_revision⌝ ∗
  "%HmaxModRev" ∷ ⌜op.maxModRev' = req.max_mod_revision⌝ ∗
  "%HminCreateRev" ∷ ⌜op.minCreateRev' = req.min_create_revision⌝ ∗
  "%HmaxCreateRev" ∷ ⌜op.maxCreateRev' = req.max_create_revision⌝)

def is_Op_PutRequest (op : v3.Op.t) (req : PutRequest.t) : IProp GF :=
  iprop(
  "%Ht" ∷ ⌜op.t' = W64 2⌝ ∗
  "#key" ∷ op.key' ↦*□ req.key ∗
  "#value" ∷ op.val' ↦*□ req.value ∗
  "%Hlease" ∷ ⌜op.leaseID' = req.lease⌝ ∗
  "%HprevKV" ∷ ⌜op.prevKV' = req.prev_kv⌝ ∗
  "%Hignore_value" ∷ ⌜op.ignoreValue' = req.ignore_value⌝ ∗
  "%Hignore_lease" ∷ ⌜op.ignoreLease' = req.ignore_lease⌝)

def is_Op_def (op : v3.Op.t) (o : Op.t) : IProp GF :=
  match o with
  | .Get req => is_Op_RangeRequest op req
  | .Put req => is_Op_PutRequest op req
  | _ => iprop(False)
/-- (Rocq: `Opaque is_Op`) -/
@[irreducible] def is_Op (op : v3.Op.t) (o : Op.t) : IProp GF :=
  is_Op_def op o
theorem is_Op_unseal : @is_Op = @is_Op_def := by funext; with_unfolding_all rfl

instance is_Op_persistent (op : v3.Op.t) (o : Op.t) :
    Persistent (is_Op (GF := GF) op o) := by
  rw [is_Op_unseal]; unfold is_Op_def
  cases o <;> dsimp only <;> (try unfold is_Op_RangeRequest) <;> (try unfold is_Op_PutRequest) <;> infer_instance

/-- NOTE (Rocq): for simplicity, this only supports empty opts list. -/
theorem wp_OpGet (key : go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (App (Val (@! v3.OpGet)) (Val #key)) (Val #slice.nil))
    {{ (op : v3.Op.t), RET #op;
        is_Op op (.Get { RangeRequest.default with key := key }) }} := by
  sorry -- Rocq: Admitted

theorem wp_Op__applyOpts (op : loc) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (op @!! go.type.PointerType v3.Op @!! go!"applyOpts")) (Val #slice.nil))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_for
  wp_end

theorem wp_OpPut (key v : go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (App (App (Val (@! v3.OpPut)) (Val #key)) (Val #v)) (Val #slice.nil))
    {{ (op : v3.Op.t), RET #op;
        is_Op op (.Put { PutRequest.default with key := key, value := v }) }} := by
  wp_start
  wp_auto
  wp_apply wp_string_to_bytes as %key_sl ⟨key_sl, -⟩
  wp_apply wp_string_to_bytes as %val_sl ⟨val_sl, -⟩
  ipersist key_sl
  ipersist val_sl
  wp_apply wp_Op__applyOpts
  have hz : zero_val v3.Op.t = ⟨zero_val _, slice.nil, slice.nil, W64 0, loc.null, false, false, false,
      W64 0, W64 0, W64 0, W64 0, W64 0, false, false, false, false, false, false, false, false,
      slice.nil, W64 0, slice.nil, slice.nil, slice.nil, false, false⟩ := rfl
  simp only [hz]
  wp_auto
  iapply HΦ
  simp only [is_Op_unseal, is_Op_def, is_Op_PutRequest]
  iframe # ∗
  ipureintro
  simp [PutRequest.default]

theorem wp_Op__KeyBytes (op : v3.Op.t) (req : PutRequest.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ is_Op op (.Put req) }}
      (App (Val (op @!! v3.Op @!! go!"KeyBytes")) (Val #()))
    {{ (key_sl : slice.t), RET #key_sl; key_sl ↦*□ req.key }} := by
  wp_start as Hop
  wp_auto
  simp only [is_Op_unseal, is_Op_def, is_Op_PutRequest]
  iNamed Hop
  iapply HΦ $$ key

end wps

end go_etcd_io.etcd.client.v3_proof

end Perennial
end
