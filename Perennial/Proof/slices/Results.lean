/-
Results of `slices` derived from the linked ones: `wp_siftDownCmpFunc_Trivial` and
`wp_siftDownOrdered_Trivial` (the second conjuncts of the specs of `siftDownCmpFunc` and
`siftDownOrdered`, under their old names), `lessImplements_uint64` (from `cmp.wp_Less_uint64`)
`wp_Sort_uint64` (`Sort` on `[]uint64`), `lessImplements_uint8` and `wp_Sort_uint8` (the same at
`uint8`) and `wp_ContainsFunc_pure` (`ContainsFunc` of a function
computing a pure predicate).
-/
module

public import Perennial.Proof.slices.Link
public import Perennial.Proof.cmp

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

section trivial
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop) [StrictWeakOrder R]

/-- `siftDownCmpFunc` with `lo = hi = 0` returns at once (the second conjunct of
`siftDownCmpFunc.spec`). -/
theorem wp_siftDownCmpFunc_Trivial (data : GoSlice) (a b : w64) (cmp_code : GoFunc)
    (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hcmp" ∷ cmpImplements R cmp_code ∗
        "%H_bounds" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (App (App (Val #(functions siftDownCmpFunc [Et])) (Val #data))
        (Val #(W64 0))) (Val #(W64 0))) (Val #a)) (Val #cmp_code))
    {{ RET #(); "Hxs" ∷ data ↦* xs }} :=
  wp_siftDownCmpFunc.2 R data a b cmp_code xs

/-- `siftDownOrdered` with `lo = hi = 0` returns at once (the second conjunct of
`siftDownOrdered.spec`). -/
theorem wp_siftDownOrdered_Trivial (data : GoSlice) (a b : w64)
    (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hless" ∷ lessImplements (Et := Et) R ∗
        "%H_bounds" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (App (Val #(functions siftDownOrdered [Et])) (Val #data))
        (Val #(W64 0))) (Val #(W64 0))) (Val #a))
    {{ RET #(); "Hxs" ∷ data ↦* xs }} :=
  wp_siftDownOrdered.2 R data a b xs

end trivial

section uint64
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
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

/-- On `uint8`, `cmp.Less` implements `<` on the unsigned values. -/
theorem lessImplements_uint8 :
    ⊢ lessImplements (GF := GF) (Et := go.uint8) (fun (x y : w8) => uint.Z x < uint.Z y) := by
  unfold lessImplements
  iintro %x %y
  imodintro
  iintro %Φ _ HΦ
  wp_apply cmp.wp_Less_uint8 x y with %b %Hb
  iapply HΦ
  ipureintro
  exact Hb

end uint64

section uint64
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
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

/-- `slices.Sort` on a `[]uint8` (any slice type `S` with that underlying type):
it permutes the slice into ascending order. -/
theorem wp_Sort_uint8 {S : go.GoType} [S ↓u go.SliceType go.uint8] (data : GoSlice)
    (xs : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hlength_bound" ∷ ⌜xs.length ≤ 2 ^ 62⌝ }}
      (App (Val #(functions «Sort» [S, go.uint8])) (Val #data))
    {{ (xs' : List w8), RET #();
        "Hxs" ∷ data ↦* xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜∀ (i j : Nat) (xi xj : w8), xs'[i]? = some xi → xs'[j]? = some xj →
          i < j → uint.Z xi ≤ uint.Z xj⌝ }} := by
  wp_start_folded as H
  iNamed H
  ihave #Hless := lessImplements_uint8 (GF := GF)
  wp_apply wp_Sort (fun (x y : w8) => uint.Z x < uint.Z y) data xs StrictWeakOrder_unsigned_lt_w8
    $$ [Hxs] with %xs' ⟨Hxs, %Hperm, %Hsorted⟩
  · iframe Hxs; iframe #; ipureintro; exact Hlength_bound
  iapply HΦ
  iframe Hxs
  ipureintro
  refine ⟨Hperm, fun i j xi xj Hi Hj Hij => ?_⟩
  have := Hsorted i j xi xj Hi Hj Hij
  omega

end uint64

section containsFunc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

/-- `slices.ContainsFunc(s, f)` of an `f` computing a pure predicate `p` on the elements of `s`:
whether some element satisfies `p` (`xs.any p`, that is `decide (∃ x ∈ xs, p x)`). -/
theorem wp_ContainsFunc_pure {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {Et : go.GoType}
    [IntoValTyped (GF := GF) V Et] {S : go.GoType} [S ↓u go.SliceType Et]
    (s : GoSlice) (dq : DFrac) (xs : List V) (f : GoFunc) (p : V → Bool) :
    {{ s ↦*{dq} xs ∗ funcAnswers (GF := GF) (fun x b => b = p x) xs f }}
      (App (App (Val #(functions ContainsFunc [S, Et])) (Val #s)) (Val #f))
    {{ RET #(xs.any p); s ↦*{dq} xs }} := by
  wp_start_folded as ⟨Hs, #Hf⟩
  wp_apply wp_ContainsFunc s dq xs f (fun x b => b = p x) $$ [Hs] as %b ⟨Hs, %Hb⟩
  · iframe; iframe #
  have hb : b = xs.any p := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at Hb
      symm
      rw [List.any_eq_false]
      intro x hx
      simp [Hb x hx]
    · simp only [↓reduceIte] at Hb
      obtain ⟨x, hx, hpx⟩ := Hb
      symm
      rw [List.any_eq_true]
      exact ⟨x, hx, hpx.symm⟩
  subst hb
  iapply HΦ
  iexact Hs

end containsFunc

end slices

end Perennial
