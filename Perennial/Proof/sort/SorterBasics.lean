/-
The `sort.Interface` sorts (`zsortinterface.go`): the sorter predicate and the specs
of its `Len`, `Less` and `Swap` calls, shared by the `pdqsort` proofs of `sort`.

The `sort.Interface` functions are the `CmpFunc` ones of `slices` (`Perennial/Proof/slices/`,
generated from the same template, `gen_sort_variants.go`) with the slice accesses replaced
by method calls: `cmp(data[i], data[j]) < 0` is `data.Less(i, j)`, and
`data[i], data[j] = data[j], data[i]` is `data.Swap(i, j)`. Their proofs reuse every pure
lemma of the `slices` sort proofs (`SortBasics.lean`, ...: `IsSortedSeg`, `header`,
`OutsideSame`, ...), with the
collection the sorter `x` holds in place of the slice's elements: a list `l` with the
resource `own l` (`isSorter`).
-/
module

public import Perennial.Proof.sort.Base
public import Perennial.Proof.slices.SortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace sort

open slices

-- (declared before the proofs, as `slice_index_if`)
/-- Reduce the `if`s on a comparison of two Boolean literals,
`if decide (#b1 = #b2) = true then _ else _` (a loop's condition, `break` or `continue`). -/
macro "bool_if" : tactic =>
  `(tactic| (simp only [decide_eq_true_eq, false_neq_true, true_neq_false, ↓reduceIte]))

/-- Swapping by two `set`s does not depend on their order: `xs[i]` and `xs[j]` exchanged. -/
theorem swap_set_comm {T : Type} (xs : List T) (i j : Nat) (xi xj : T)
    (hi : xs[i]? = some xi) (hj : xs[j]? = some xj) :
    (xs.set i xj).set j xi = (xs.set j xi).set i xj := by
  by_cases h : i = j
  · subst h
    rw [hi] at hj; cases hj
    simp
  · exact List.set_comm _ _ h

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {E : Type}

/-- **The `sort.Interface` value `x` sorts a list by `R`.** Its state is the resource
`own l` for the list `l` of elements it holds: `Len()` returns `l`'s length, `Less(i, j)`
(indices of `l`) whether `R l[i] l[j]`, and `Swap(i, j)` exchanges the two elements. -/
def isSorter (x : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop) : IProp GF :=
  iprop(
    □ (∀ l : List E,
      {{ own l }} (App (Val #(methods x.ty go!"Len" x.v)) (Val #()))
      {{ RET #(W64 l.length); own l }}) ∗
    □ (∀ (l : List E) (i j : w64) (a b : E),
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b⌝ -∗
      {{ own l }} (App (App (Val #(methods x.ty go!"Less" x.v)) (Val #i)) (Val #j))
      {{ (r : Bool), RET #r; own l ∗ ⌜r = true ↔ R a b⌝ }}) ∗
    □ (∀ (l : List E) (i j : w64) (a b : E),
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b⌝ -∗
      {{ own l }} (App (App (Val #(methods x.ty go!"Swap" x.v)) (Val #i)) (Val #j))
      {{ RET #(); own ((l.set (sint.nat i) b).set (sint.nat j) a) }}))

instance isSorter_persistent (x : GoInterfaceOk) (own : List E → IProp GF)
    (R : E → E → Prop) : Persistent (isSorter x own R) := by
  unfold isSorter; infer_instance

/-! The calls, with `isSorter` kept folded in the caller's context: unfolded, its `▷`s
make every symbolic execution step search for laters to strip in all hypotheses. -/

theorem wp_sorter_Len (x : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop)
    (l : List E) :
    {{ isSorter x own R ∗ own l }}
      (App (Val #(methods x.ty go!"Len" x.v)) (Val #()))
    {{ RET #(W64 l.length); own l }} := by
  iintro %Φ ⟨#Hs, Hl⟩ HΦ
  unfold isSorter
  icases Hs with ⟨#HLen, -, -⟩
  iapply HLen $$ Hl HΦ

theorem wp_sorter_Less (x : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop)
    (l : List E) (i j : w64) (a b : E) (hi : 0 ≤ sint.Z i) (hj : 0 ≤ sint.Z j)
    (ha : l[sint.nat i]? = some a) (hb : l[sint.nat j]? = some b) :
    {{ isSorter x own R ∗ own l }}
      (App (App (Val #(methods x.ty go!"Less" x.v)) (Val #i)) (Val #j))
    {{ (r : Bool), RET #r; own l ∗ ⌜r = true ↔ R a b⌝ }} := by
  iintro %Φ ⟨#Hs, Hl⟩ HΦ
  unfold isSorter
  icases Hs with ⟨-, #HLess, -⟩
  iapply HLess $$ %l %i %j %a %b [] Hl HΦ
  ipureintro; exact ⟨hi, hj, ha, hb⟩

/-- `Swap(i, j)`, with the result in the form of the slice proofs' swaps
(`swap_perm`, `outsideSame_swap`: `<[i := xj]> (<[j := xi]> xs)`). -/
theorem wp_sorter_Swap (x : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop)
    (l : List E) (i j : w64) (a b : E) (hi : 0 ≤ sint.Z i) (hj : 0 ≤ sint.Z j)
    (ha : l[sint.nat i]? = some a) (hb : l[sint.nat j]? = some b) :
    {{ isSorter x own R ∗ own l }}
      (App (App (Val #(methods x.ty go!"Swap" x.v)) (Val #i)) (Val #j))
    {{ RET #(); own (<[sint.nat i := b]> (<[sint.nat j := a]> l)) }} := by
  iintro %Φ ⟨#Hs, Hl⟩ HΦ
  unfold isSorter
  icases Hs with ⟨-, -, #HSwap⟩
  iapply HSwap $$ %l %i %j %a %b [] Hl
  · ipureintro; exact ⟨hi, hj, ha, hb⟩
  rw [swap_set_comm l (sint.nat i) (sint.nat j) a b ha hb]
  iexact HΦ

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

/-- `isSorter` under an opaque name (`pdqHide` of `slices`): for the Löb induction
hypothesis of `wp_pdqsort`, which contains `▷`s. -/
def sortHide (P : IProp GF) : IProp GF := P

theorem sortHide_intro {P Q : IProp GF} : (□ sortHide P -∗ Q) ⊢ (□ P -∗ Q) := .rfl

theorem sortHide_elim {P Q : IProp GF} : (□ P -∗ Q) ⊢ (□ sortHide P -∗ Q) := .rfl

end proof

end sort

end Perennial
end
