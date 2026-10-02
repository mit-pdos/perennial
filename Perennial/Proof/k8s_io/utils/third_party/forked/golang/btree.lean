/-
Port of `new/proof/k8s_io/utils/third_party/forked/golang/btree.v`: an
axiomatized (as in Rocq) specification of the forked `btree` package.

Differences from Rocq:
* Rocq also declares the `IsPkgInit` instance of `cmp` here; in Lean it lives in
  `Perennial/Proof/cmp.lean`, which is imported.
* Rocq re-exports `sync sort fmt go_etcd_io.etcd.client.v3`; only what this file
  needs (the `IsPkgInit` instances of the imported packages) is imported.
* In `wp_BTree__Get` and `wp_BTree__ReplaceOrInsert`, the Rocq statements pass
  `#key` (of the abstract type `V`, resp. an unbound `key`) as the argument; the
  Go argument is the item of type `T'`, so the Lean statements pass
  `#key_item` and `#item`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Proof.cmp
import Perennial.Proof.sort_proof.sort_init
import Perennial.Proof.sync_proof.base
import Perennial.Code.k8s_io.utils.third_party.forked.golang.btree
import Perennial.GeneratedProof.k8s_io.utils.third_party.forked.golang.btree

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace k8s_io.utils.third_party.forked.golang.btree

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [cmp_sem : cmp.Assumptions] [sort_sem : sort.Assumptions] [sync_sem : sync.Assumptions]
variable [package_sem : btree.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree :=
  build_get_is_pkg_init_wf

axiom own_BTree (t : loc) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {V : Type}
    (is_item : T' → V → IProp GF) (less : V → V → Prop) (items : List V) (dq : DFrac) :
    IProp GF

axiom own_BTree_dfractional (t : loc) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {V : Type} (is_item : T' → V → IProp GF) (less : V → V → Prop) (items : List V) :
    DFractional (own_BTree t is_item less items)
attribute [instance] own_BTree_dfractional

axiom wp_BTree__Clone [package_sem : btree.Assumptions] {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {T : go.type}
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (is_item : T' → V → IProp GF) (less : V → V → Prop) (items : List V) (t : loc) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
       own_BTree t is_item less items (DFrac.own 1) }}
      (App (Val (t @!! go.type.PointerType (BTree T) @!! go!"Clone")) (Val #()))
    {{ (t' : loc), RET #t';
       own_BTree t is_item less items (DFrac.own 1) ∗
       own_BTree t' is_item less items (DFrac.own 1) }}

axiom wp_BTree__Get [package_sem : btree.Assumptions] {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {T : go.type}
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (is_item : T' → V → IProp GF) (less : V → V → Prop) (items : List V)
    (t : loc) (key_item : T') (key : V) (dq : DFrac) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
       own_BTree t is_item less items dq ∗ is_item key_item key }}
      (App (Val (t @!! go.type.PointerType (BTree T) @!! go!"Get")) (Val #key_item))
    {{ (item : T') (found : Bool), RET (PairV #item #found);
       own_BTree t is_item less items dq ∗
       (match found with
        | false => ⌜item = zero_val T'⌝
        | true => ∃ itv, is_item item itv ∗ ⌜¬ less itv key ∧ ¬ less key itv ∧ itv ∈ items⌝) }}

/-- TODO (from Rocq): this is a conservative but weak spec; it does not
constrain the final tree state. -/
axiom wp_BTree__ReplaceOrInsert [package_sem : btree.Assumptions] {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {T : go.type} [IntoValTyped (GF := GF) T' T] {V : Type}
    (is_item : T' → V → IProp GF) (less : V → V → Prop) (items : List V)
    (t : loc) (item : T') (itv : V) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
       own_BTree t is_item less items (DFrac.own 1) ∗ is_item item itv }}
      (App (Val (t @!! go.type.PointerType (BTree T) @!! go!"ReplaceOrInsert")) (Val #item))
    {{ (old_item : T') (found : Bool) (items' : List V), RET (PairV #old_item #found);
       own_BTree t is_item less items' (DFrac.own 1) }}

end wps

end k8s_io.utils.third_party.forked.golang.btree

end Perennial
end
