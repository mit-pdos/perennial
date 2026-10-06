/-
Port of `new/proof/k8s_io/utils/third_party/forked/golang/btree.v`: an
axiomatized (as in Rocq) specification of the forked `btree` package.

Differences from Rocq:
* Rocq also declares the `IsPkgInit` instance of `cmp` here; in Lean it lives in
  `Perennial/Proof/cmp.lean`, which is imported.
* Rocq re-exports `sync sort fmt go_etcd_io.etcd.client.v3`; only what this file
  needs (the `IsPkgInit` instances of the imported packages) is imported.
* In `BTree.wp_Get` and `BTree.wp_ReplaceOrInsert`, the Rocq statements pass
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [cmp_sem : cmp.Assumptions] [sort_sem : sort.Assumptions] [sync_sem : sync.Assumptions]
variable [package_sem : btree.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree :=
  build_get_is_pkg_init_wf

axiom ownBTree (t : Loc) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {V : Type}
    (is_item : T' → V → IProp GF) (less : V → V → Prop) (items : List V) (dq : DFrac) :
    IProp GF

axiom ownBTree_dfractional (t : Loc) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {V : Type} (is_item : T' → V → IProp GF) (less : V → V → Prop) (items : List V) :
    DFractional (ownBTree t is_item less items)
attribute [instance] ownBTree_dfractional

axiom BTree.wp_Clone [package_sem : btree.Assumptions] {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {T : go.GoType}
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (is_item : T' → V → IProp GF) (less : V → V → Prop) (items : List V) (t : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
       ownBTree t is_item less items (DFrac.own 1) }}
      (App (Val (t @!! go.GoType.PointerType (BTree T) @!! go!"Clone")) (Val #()))
    {{ (t' : Loc), RET #t';
       ownBTree t is_item less items (DFrac.own 1) ∗
       ownBTree t' is_item less items (DFrac.own 1) }}

axiom BTree.wp_Get [package_sem : btree.Assumptions] {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {T : go.GoType}
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (is_item : T' → V → IProp GF) (less : V → V → Prop) (items : List V)
    (t : Loc) (key_item : T') (key : V) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
       ownBTree t is_item less items dq ∗ is_item key_item key }}
      (App (Val (t @!! go.GoType.PointerType (BTree T) @!! go!"Get")) (Val #key_item))
    {{ (item : T') (found : Bool), RET (PairV #item #found);
       ownBTree t is_item less items dq ∗
       (match found with
        | false => ⌜item = _root_.Perennial.zero_val T'⌝
        | true => ∃ itv, is_item item itv ∗ ⌜¬ less itv key ∧ ¬ less key itv ∧ itv ∈ items⌝) }}

/-- TODO (from Rocq): this is a conservative but weak spec; it does not
constrain the final tree state. -/
axiom BTree.wp_ReplaceOrInsert [package_sem : btree.Assumptions] {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {T : go.GoType} [IntoValTyped (GF := GF) T' T] {V : Type}
    (is_item : T' → V → IProp GF) (less : V → V → Prop) (items : List V)
    (t : Loc) (item : T') (itv : V) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
       ownBTree t is_item less items (DFrac.own 1) ∗ is_item item itv }}
      (App (Val (t @!! go.GoType.PointerType (BTree T) @!! go!"ReplaceOrInsert")) (Val #item))
    {{ (old_item : T') (found : Bool) (items' : List V), RET (PairV #old_item #found);
       ownBTree t is_item less items' (DFrac.own 1) }}

end wps

end k8s_io.utils.third_party.forked.golang.btree

end Perennial
end
