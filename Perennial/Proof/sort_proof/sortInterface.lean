/-
The specs of `sort.Sort` and `sort.Reverse`, over a `sort.Interface` (`isSorter`).

`sort.Sort(data)` sorts the list a sorter holds by a strict weak order `R`: it leaves
the sorter holding a permutation of the list in which no element is `R`-less than an
earlier one. As `slices.SortFunc` (`slices_proof/sort.lean`), it needs at most `2^62`
elements: past that, the heapsort fallback's `2*root+1` overflows `int`.
`sort.Reverse(data)` is a sorter of the same list by the converse order.
-/
module

public import Perennial.Proof.math.bits
public import Perennial.Proof.sort_proof.pdqSort.pdqSort

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
variable {E : Type}

theorem wp_Sort (x : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop)
    (SWO : StrictWeakOrder R) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "Hxs" ∷ own xs ∗
        "%Hlength_bound" ∷ ⌜xs.length ≤ 2 ^ 62⌝ }}
      (App (Val (@! «Sort»)) (Val #(interface.ok x)))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ own xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜∀ (i j : Nat) (xi xj : E), xs'[i]? = some xi → xs'[j]? = some xj →
          i < j → ¬ R xj xi⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_sorter_Len x own R xs $$ [$Hsrt $Hxs] as Hxs
  have hn : sint.Z (W64 xs.length) = xs.length := by word
  wp_if_destruct
  · iapply HΦ
    iframe Hxs
    ipureintro
    refine ⟨List.Perm.refl _, fun i j xi xj Hi Hj Hij => ?_⟩
    have := lookup_lt_Some Hj
    have : xs.length ≤ 1 := by word
    omega
  wp_apply math.bits.wp_Len with %l _
  wp_apply wp_pdqsort x own R (W64 0) (W64 xs.length) l xs $$ [Hxs]
    with %xs' ⟨Hxs, %Hperm, %Hsorted, %Houtside⟩
  · iframe Hxs; iframe #; ipureintro
    refine ⟨⟨by word, by word, by word, Hlength_bound⟩, ?_⟩
    unfold header; simp
  iapply HΦ
  iframe Hxs
  ipureintro
  refine ⟨Hperm, ?_⟩
  intro i j xi xj Hi Hj Hij
  apply isSortedSeg_is_sorted R xs' _ i j xi xj Hij Hi Hj
  rw [← Hperm.length_eq]
  rw [show sint.nat (W64 xs.length) = xs.length by word,
    show sint.nat (W64 0) = 0 by word] at Hsorted
  exact Hsorted

omit package_sem in
/-- `isSorter` from its three method specs (to prove one without unfolding the
`isSorter`s in the context). -/
theorem isSorter_intro (y : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop) :
    iprop(
      □ (∀ l : List E,
        {{ own l }} (App (Val #(methods y.ty go!"Len" y.v)) (Val #()))
        {{ RET #(W64 l.length); own l }}) ∗
      □ (∀ (l : List E) (i j : w64) (a b : E),
        ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b⌝ -∗
        {{ own l }} (App (App (Val #(methods y.ty go!"Less" y.v)) (Val #i)) (Val #j))
        {{ (r : Bool), RET #r; own l ∗ ⌜r = true ↔ R a b⌝ }}) ∗
      □ (∀ (l : List E) (i j : w64) (a b : E),
        ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b⌝ -∗
        {{ own l }} (App (App (Val #(methods y.ty go!"Swap" y.v)) (Val #i)) (Val #j))
        {{ RET #(); own ((l.set (sint.nat i) b).set (sint.nat j) a) }})) ⊢
    isSorter y own R := by
  unfold isSorter; exact .rfl

theorem wp_Reverse (x : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ isSorter x own R }}
      (App (Val (@! Reverse)) (Val #(interface.ok x)))
    {{ (y : GoInterfaceOk), RET #(interface.ok y); isSorter y own (fun a b => R b a) }} := by
  wp_start as #Hsrt
  wp_auto
  wp_alloc l as Hl
  ipersist Hl
  ihave Hl2 := Hl
  iStructNamed Hl2
  wp_auto
  iapply HΦ
  iapply isSorter_intro
  isplitr
  · iintro !> %l' %Φ' !> Hown HΦ'
    dsimp only
    rw [method_unfold (t := go.GoType.PointerType reverse.ty)]
    wp_auto
    wp_apply wp_sorter_Len x own R l' $$ [$Hsrt $Hown] as Hown
    iapply HΦ' $$ Hown
  isplitr
  · iintro !> %l' %i %j %a %b %Hij %Φ' !> Hown HΦ'
    dsimp only
    rw [method_unfold (t := go.GoType.PointerType reverse.ty)]
    wp_auto
    rw [method_unfold (t := reverse.ty)]
    wp_auto
    wp_apply wp_sorter_Less x own R l' j i b a Hij.2.1 Hij.1 Hij.2.2.2 Hij.2.2.1
      $$ [$Hsrt $Hown] as %r ⟨Hown, %Hr⟩
    iapply HΦ'
    iframe Hown
    ipureintro; exact Hr
  · iintro !> %l' %i %j %a %b %Hij %Φ' !> Hown HΦ'
    dsimp only
    rw [method_unfold (t := go.GoType.PointerType reverse.ty)]
    wp_auto
    wp_apply wp_sorter_Swap x own R l' i j a b Hij.1 Hij.2.1 Hij.2.2.1 Hij.2.2.2
      $$ [$Hsrt $Hown] as Hown
    iapply HΦ'
    rw [swap_set_comm l' (sint.nat i) (sint.nat j) a b Hij.2.2.1 Hij.2.2.2]
    iexact Hown

end proof

end sort

end Perennial
end
