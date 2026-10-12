/-
The spec of `pdqsort` (and `reverseRange`) over a `sort.Interface`
(`slices_proof/pdqSort/pdqSort.lean` with `Less`/`Swap` calls).
-/
module

public import Perennial.Proof.sort_proof.pdqSort.sort_basics
public import Perennial.Proof.sort_proof.pdqSort.partition
public import Perennial.Proof.sort_proof.pdqSort.insertionSort
public import Perennial.Proof.sort_proof.pdqSort.heapSort
public import Perennial.Proof.slices_proof.pdqSort.pdqSort

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace sort

open slices

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]
variable {E : Type} (x : GoInterfaceOk) (own : List E → IProp GF)
variable (R : E → E → Prop) [StrictWeakOrder R]

theorem wp_reverseRange (a b : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "%pivot_range" ∷ ⌜sint.Z a < sint.Z b⌝ }}
      (App (App (App (Val (@! reverseRange)) (Val #(interface.ok x))) (Val #a)) (Val #b))
    {{ (xs' : List E), RET #();
        own xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  sorry

theorem wp_pdqsort (a b limit : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a ≤ sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "%Header" ∷ ⌜header R xs (sint.nat a) (sint.nat b)⌝ ∗
        "#Hsrt" ∷ isSorter x own R }}
      (App (App (App (App (Val (@! pdqsort)) (Val #(interface.ok x))) (Val #a)) (Val #b)) (Val #limit))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ own xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜IsSortedSeg R xs' (sint.nat a) (sint.nat b)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  sorry

end proof

end sort

end Perennial
end
