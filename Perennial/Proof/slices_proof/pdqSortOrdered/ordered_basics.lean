/-
The comparison of the `cmp.Ordered` sorts (`zsortordered.go`) and the spec of
`order2Ordered`, shared by the `pdqsortOrdered` proofs.

The `Ordered` functions are the `CmpFunc` ones (`pdqSort/`) with `cmp(x, y) < 0`
replaced by `cmp.Less(x, y)` and without the `cmp` argument; their proofs reuse every
pure lemma of `pdqSort/` and assume of `cmp.Less` at the element type what
`cmpImplements` assumes of the comparison function (`lessImplements`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.slices
public import Perennial.GeneratedProof.slices
public import Perennial.Proof.slices_proof.slices_init
public import Perennial.Proof.slices_proof.pdqSort.sort_basics
public import Perennial.Proof.cmp

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop)

/-- `cmp.Less` at the element type `Et` implements `R`. -/
def lessImplements : IProp GF :=
  iprop(∀ (x y : E),
    {{ True }}
      (App (App (Val #(functions cmp.Less [Et])) (Val #x)) (Val #y))
    {{ (b : Bool), RET #b; ⌜b = true ↔ R x y⌝ }})

instance lessImplements_persistent : Persistent (lessImplements (GF := GF) (Et := Et) R) := by
  unfold lessImplements; infer_instance

theorem wp_order2Ordered [StrictWeakOrder R] (data : GoSlice) (a b : w64) (swaps_l : Loc)
    (dq : DFrac) (xs : List E) (swaps : w64) (xa xb : E)
    (Ha_bound : 0 ≤ sint.Z a) (Hb_bound : 0 ≤ sint.Z b) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦*{dq} xs ∗
        "%Hxa" ∷ ⌜xs[sint.nat a]? = some xa⌝ ∗
        "%Hxb" ∷ ⌜xs[sint.nat b]? = some xb⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hless" ∷ lessImplements (Et := Et) R }}
      (App (App (App (App (Val #(functions order2Ordered [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #swaps_l))
    {{ (a' b' : w64) (swaps' : w64), RET (PairV #a' #b');
        data ↦*{dq} xs ∗
        ⌜(a' = a ∧ b' = b ∧ ¬ R xb xa) ∨ (a' = b ∧ b' = a ∧ R xb xa)⌝ ∗
        swaps_l ↦ swaps' }} := by
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  have := lookup_lt_Some Hxa
  have := lookup_lt_Some Hxb
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z b) xs dq xb Hb_bound $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxb
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z a) xs dq xa Ha_bound $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxa
  unfold lessImplements
  wp_apply Hless with %r %Hr
  wp_if_destruct
  · iapply HΦ
    iframe
    ipureintro
    left; exact ⟨rfl, rfl, fun h => absurd (Hr.2 h) (by simp)⟩
  · iapply HΦ
    iframe
    ipureintro
    right; exact ⟨rfl, rfl, Hr.1 rfl⟩

end proof

section uint64
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : cmp.Assumptions]

/-- On `uint64`, `cmp.Less` implements `<` on the unsigned values. -/
theorem lessImplements_uint64 :
    ⊢ lessImplements (GF := GF) (Et := go.uint64) (fun (x y : w64) => uint.Z x < uint.Z y) := by
  unfold lessImplements
  iintro %x %y
  imodintro
  iintro %Φ _ HΦ
  wp_apply cmp.wp_Less_uint64 x y with %b %Hb
  iapply HΦ
  ipureintro
  exact Hb

end uint64

end slices

end Perennial
end
