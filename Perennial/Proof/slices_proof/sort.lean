/-
The specs of `slices.SortFunc` and `slices.Sort`.

We assume a binary relation `R` on elements, which is a "strict weak order".
The comparison function `cmp_code` implements `R`:
    `cmp_code x y < 0  ↔  R x y`
The sorting procedure returns a permutation of the input slice and ensures
that the output is ordered with respect to `R`.

For integers, `R` can be `(<)`, and the postcondition `Hsorted` gives
(informally) `∀ i < j, data[i] ≤ data[j]`.

`slices.Sort` (for `cmp.Ordered` element types) is specified the same way, with
`cmp.Less` at the element type implementing `R` (`lessImplements`); for `uint64` that
holds for `<` on the unsigned values (`lessImplements_uint64`), so `wp_Sort_uint64`
needs no premise about the order.

Both need `len ≤ 2^62`: past that, the heapsort fallback's `2*root+1` overflows `int`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.slices
public import Perennial.GeneratedProof.slices
public import Perennial.Proof.math.bits
public import Perennial.Proof.slices_proof.slices_init
public import Perennial.Proof.slices_proof.pdqSort.sort_basics
public import Perennial.Proof.slices_proof.pdqSort.pdqSort
public import Perennial.Proof.slices_proof.pdqSortOrdered.pdqSort

@[expose] public section

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

theorem wp_SortFunc {S : go.GoType} [S ↓u go.SliceType Et] (data : GoSlice) (cmp_code : GoFunc)
    (xs : List E) (SWO : StrictWeakOrder R) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hlength_bound" ∷ ⌜xs.length ≤ 2 ^ 62⌝ ∗
        "#Hcmp" ∷ cmpImplements R cmp_code }}
      (App (App (Val #(functions SortFunc [S, Et])) (Val #data)) (Val #cmp_code))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ data ↦* xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜∀ (i j : Nat) (xi xj : E), xs'[i]? = some xi → xs'[j]? = some xj →
          i < j → ¬ R xj xi⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  wp_apply math.bits.wp_Len with %l _
  wp_apply wp_pdqsortCmpFunc R data (W64 0) data.len l cmp_code xs $$ [Hxs]
    with %xs' ⟨Hxs, %Hperm, %Hsorted, %Houtside⟩
  · iframe Hxs; iframe #; ipureintro
    refine ⟨by word, ?_⟩
    unfold header; simp
  iapply HΦ
  iframe Hxs
  ipureintro
  refine ⟨Hperm, ?_⟩
  intro i j xi xj Hi Hj Hij
  apply isSortedSeg_is_sorted R xs' _ i j xi xj Hij Hi Hj
  rw [← Hperm.length_eq, Hlen.1]
  exact Hsorted

theorem wp_Sort {S : go.GoType} [S ↓u go.SliceType Et] (data : GoSlice)
    (xs : List E) (SWO : StrictWeakOrder R) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hlength_bound" ∷ ⌜xs.length ≤ 2 ^ 62⌝ ∗
        "#Hless" ∷ lessImplements (Et := Et) R }}
      (App (Val #(functions «Sort» [S, Et])) (Val #data))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ data ↦* xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜∀ (i j : Nat) (xi xj : E), xs'[i]? = some xi → xs'[j]? = some xj →
          i < j → ¬ R xj xi⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  wp_apply math.bits.wp_Len with %l _
  wp_apply wp_pdqsortOrdered R data (W64 0) data.len l xs $$ [Hxs]
    with %xs' ⟨Hxs, %Hperm, %Hsorted, %Houtside⟩
  · iframe Hxs; iframe #; ipureintro
    refine ⟨by word, ?_⟩
    unfold header; simp
  iapply HΦ
  iframe Hxs
  ipureintro
  refine ⟨Hperm, ?_⟩
  intro i j xi xj Hi Hj Hij
  apply isSortedSeg_is_sorted R xs' _ i j xi xj Hij Hi Hj
  rw [← Hperm.length_eq, Hlen.1]
  exact Hsorted

end proof

section uint64
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

/-- `slices.Sort` on a `[]uint64` (any slice type `S` with that underlying type):
it permutes the slice into ascending order. -/
theorem wp_Sort_uint64 {S : go.GoType} [S ↓u go.SliceType go.uint64] (data : GoSlice)
    (xs : List w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hlength_bound" ∷ ⌜xs.length ≤ 2 ^ 62⌝ }}
      (App (Val #(functions «Sort» [S, go.uint64])) (Val #data))
    {{ (xs' : List w64), RET #();
        "Hxs" ∷ data ↦* xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜∀ (i j : Nat) (xi xj : w64), xs'[i]? = some xi → xs'[j]? = some xj →
          i < j → uint.Z xi ≤ uint.Z xj⌝ }} := by
  wp_start_folded as H
  iNamed H
  ihave #Hless := lessImplements_uint64 (GF := GF)
  wp_apply wp_Sort (fun (x y : w64) => uint.Z x < uint.Z y) data xs StrictWeakOrder_unsigned_lt
    $$ [Hxs] with %xs' ⟨Hxs, %Hperm, %Hsorted⟩
  · iframe Hxs; iframe #; ipureintro; exact Hlength_bound
  iapply HΦ
  iframe Hxs
  ipureintro
  refine ⟨Hperm, fun i j xi xj Hi Hj Hij => ?_⟩
  have := Hsorted i j xi xj Hi Hj Hij
  omega

end uint64

end slices

end Perennial
end
