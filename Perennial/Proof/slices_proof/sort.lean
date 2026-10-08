/-
The spec of `slices.SortFunc`.

We assume a binary relation `R` on elements, which is a "strict weak order".
The comparison function `cmp_code` implements `R`:
    `cmp_code x y < 0  ↔  R x y`
The sorting procedure returns a permutation of the input slice and ensures
that the output is ordered with respect to `R`.

For integers, `R` can be `(<)`, and the postcondition `Hsorted` gives
(informally) `∀ i < j, data[i] ≤ data[j]`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.slices
public import Perennial.GeneratedProof.slices
public import Perennial.Proof.math.bits
public import Perennial.Proof.slices_proof.slices_init
public import Perennial.Proof.slices_proof.pdqSort.sort_basics
public import Perennial.Proof.slices_proof.pdqSort.pdqSort

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
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

end proof

end slices

end Perennial
end
