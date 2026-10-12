/-
Specs of `order2`, `median`, `medianAdjacent`, `choosePivot`, `breakPatterns`,
`partition` and `partitionEqual` over a `sort.Interface`, and of `xorshift.Next` and
`nextPowerOfTwo` (`slices_proof/pdqSort/partition.lean` with `Less`/`Swap` calls).
-/
module

public import Perennial.Proof.sort_proof.pdqSort.sort_basics
public import Perennial.Proof.slices_proof.pdqSort.partition
public import Perennial.Proof.math.bits_exact

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

theorem wp_order2 (a b : w64) (swaps_l : Loc) (xs : List E) (swaps : w64) (xa xb : E)
    (Ha_bound : 0 ≤ sint.Z a) (Hb_bound : 0 ≤ sint.Z b) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hxa" ∷ ⌜xs[sint.nat a]? = some xa⌝ ∗
        "%Hxb" ∷ ⌜xs[sint.nat b]? = some xb⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hsrt" ∷ isSorter x own R }}
      (App (App (App (App (Val (@! order2)) (Val #(interface.ok x))) (Val #a)) (Val #b)) (Val #swaps_l))
    {{ (a' b' : w64) (swaps' : w64), RET (PairV #a' #b');
        own xs ∗
        ⌜(a' = a ∧ b' = b ∧ ¬ R xb xa) ∨ (a' = b ∧ b' = a ∧ R xb xa)⌝ ∗
        swaps_l ↦ swaps' }} := by
  sorry

theorem wp_median (a b c : w64) (swaps_l : Loc) (xs : List E) (swaps : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hbounds" ∷ ⌜(0 ≤ sint.Z a ∧ sint.Z a < (xs.length : Int)) ∧
                      (0 ≤ sint.Z b ∧ sint.Z b < (xs.length : Int)) ∧
                      (0 ≤ sint.Z c ∧ sint.Z c < (xs.length : Int))⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hsrt" ∷ isSorter x own R }}
      (App (App (App (App (App (Val (@! median)) (Val #(interface.ok x))) (Val #a)) (Val #b)) (Val #c)) (Val #swaps_l))
    {{ (r : w64) (swaps' : w64), RET #r;
        own xs ∗
        ⌜r = a ∨ r = b ∨ r = c⌝ ∗
        swaps_l ↦ swaps' }} := by
  sorry

theorem wp_medianAdjacent (a : w64) (swaps_l : Loc) (xs : List E) (swaps : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hbounds" ∷ ⌜(1 ≤ sint.Z a ∧ sint.Z a < (xs.length : Int) - 1) ∧ xs.length ≤ 2 ^ 62⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hsrt" ∷ isSorter x own R }}
      (App (App (App (Val (@! medianAdjacent)) (Val #(interface.ok x))) (Val #a)) (Val #swaps_l))
    {{ (r : w64) (swaps' : w64), RET #r;
        own xs ∗
        ⌜sint.Z a - 1 ≤ sint.Z r ∧ sint.Z r ≤ sint.Z a + 1⌝ ∗
        swaps_l ↦ swaps' }} := by
  sorry

theorem wp_choosePivot (a b : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (Val (@! choosePivot)) (Val #(interface.ok x))) (Val #a)) (Val #b))
    {{ (r : w64) (hint : sort.sortedHint), RET (PairV #r #hint);
        own xs ∗
        "%Hr_bound" ∷ ⌜sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b⌝ }} := by
  sorry

omit [StrictWeakOrder R] in
theorem xorshift.wp_Next (r : Loc) (v : xorshift) :
    {{ (r ↦ v : IProp GF) }}
      (App (Val (r @!! go.GoType.PointerType xorshift.ty @!! go!"Next")) (Val #()))
    {{ (v' : xorshift) (n : w64), RET #n; r ↦ v' }} := by
  sorry

omit [StrictWeakOrder R] in
theorem wp_nextPowerOfTwo (length : w64) (h : 0 < sint.Z length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort }}
      (App (Val (@! nextPowerOfTwo)) (Val #length))
    {{ (m : w64), RET #m; ⌜sint.Z length < uint.Z m ∧ uint.Z m ≤ 2 * sint.Z length⌝ }} := by
  sorry

theorem wp_breakPatterns (a b : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "%pivot_range" ∷ ⌜sint.Z a < sint.Z b⌝ }}
      (App (App (App (Val (@! breakPatterns)) (Val #(interface.ok x))) (Val #a)) (Val #b))
    {{ (xs' : List E), RET #();
        own xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  sorry

theorem wp_partition (a b pivot : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "%pivot_range" ∷ ⌜sint.Z a ≤ sint.Z pivot ∧ sint.Z pivot < sint.Z b⌝ }}
      (App (App (App (App (Val (@! partition)) (Val #(interface.ok x))) (Val #a)) (Val #b)) (Val #pivot))
    {{ (xs' : List E) (bl : Bool) (r : w64), RET (PairV #r #bl);
        own xs' ∗
        "%range" ∷ ⌜sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b⌝ ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hpart" ∷ ⌜IsPartitioned R xs' (sint.nat a) (sint.nat b) (sint.nat r)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  sorry

theorem wp_partitionEqual (a b pivot : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "%pivot_range" ∷ ⌜sint.Z a ≤ sint.Z pivot ∧ sint.Z pivot < sint.Z b⌝ ∗
        "%Hmin" ∷ ⌜OneLeSeg R xs (sint.nat pivot) (sint.nat a) (sint.nat b)⌝ }}
      (App (App (App (App (Val (@! partitionEqual)) (Val #(interface.ok x))) (Val #a)) (Val #b)) (Val #pivot))
    {{ (xs' : List E) (r : w64), RET #r;
        own xs' ∗
        "%range" ∷ ⌜sint.Z a < sint.Z r ∧ sint.Z r ≤ sint.Z b⌝ ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hpart" ∷ ⌜IsEqPartitioned R xs' (sint.nat a) (sint.nat b) (sint.nat r)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  sorry

end proof

end sort

end Perennial
end
