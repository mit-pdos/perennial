/-
Results of `maps` derived from the linked ones: `Clone`, `Equal` and `Copy` at `map[string]bool`, which
check that the specs' premises (`SafeMapKey`, `IsStrictlyComparable`) are found for a key type
and a value type that are strictly comparable; and `wp_Sorted_Keys_string`,
`slices.Sorted(maps.Keys(m))` of a map with `string` keys (its keys, strictly increasing).
-/
module

public import Perennial.Proof.maps.Link
public import Perennial.Proof.slices.Link
public import Perennial.Proof.cmp.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std map

namespace maps

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : maps.Assumptions]

/-- `maps.Clone` of a `map[string]bool`. -/
theorem wp_Clone_string_bool (m : Loc) (dq : DFrac) (M : GMap GoString Bool) :
    {{ (m ↦${dq} M : IProp GF) }}
      (App (Val #(functions maps.Clone [go.MapType go.string go.bool, go.string, go.bool]))
        (Val #m))
    {{ (m' : Loc), RET #m'; m ↦${dq} M ∗ m' ↦$ M }} :=
  (maps.wp_Clone (GF := GF) (hG := hG)).1 m dq M

/-- `maps.Equal` of two `map[string]bool`. -/
theorem wp_Equal_string_bool (m1 m2 : Loc) (dq1 dq2 : DFrac) (M1 M2 : GMap GoString Bool) :
    {{ (m1 ↦${dq1} M1 ∗ m2 ↦${dq2} M2 : IProp GF) }}
      (App (App (Val #(functions maps.Equal [go.MapType go.string go.bool,
        go.MapType go.string go.bool, go.string, go.bool])) (Val #m1)) (Val #m2))
    {{ (b : Bool), RET #b; ⌜b = true ↔ M1 = M2⌝ ∗ m1 ↦${dq1} M1 ∗ m2 ↦${dq2} M2 }} :=
  maps.wp_Equal (GF := GF) (hG := hG) m1 m2 dq1 dq2 M1 M2

/-- `maps.Copy` of one `map[string]bool` into another. -/
theorem wp_Copy_string_bool (dst src : Loc) (dq : DFrac) (D S : GMap GoString Bool) :
    {{ (dst ↦$ D ∗ src ↦${dq} S : IProp GF) }}
      (App (App (Val #(functions maps.Copy [go.MapType go.string go.bool,
        go.MapType go.string go.bool, go.string, go.bool])) (Val #dst)) (Val #src))
    {{ RET #(); dst ↦$ (S ∪ D) ∗ src ↦${dq} S }} :=
  maps.wp_Copy (GF := GF) (hG := hG) dst src dq D S

end results

/-- A list without duplicates that sorts (no later element is below an earlier one) is
strictly increasing in Go's order on strings. -/
theorem pairwise_goStringLt_of_sorted (ys : List GoString) (hnd : ys.Nodup)
    (hs : ∀ (i j : Nat) (yi yj : GoString), ys[i]? = some yi → ys[j]? = some yj → i < j →
      ¬ go.GoStringLt yj yi) :
    ys.Pairwise go.GoStringLt := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hn := hs i j ys[i] ys[j] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  apply Classical.byContradiction
  intro hlt
  have heq := go.goStringLt_eq_of_not_lt hlt hn
  rw [List.Nodup, List.pairwise_iff_getElem] at hnd
  exact hnd i j hi hj hij heq

section sortedKeys
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : maps.Assumptions] [package_sem' : slices.Assumptions]
variable [package_sem'' : cmp.Assumptions]

/-- `slices.Sorted(maps.Keys(m))` of a map `m` with `string` keys (at any type `T` whose underlying
type is `map[string]Vt`): `Keys` returns an iterator `f`; each `Sorted(f)` reads the map as it is
then (any fraction) and returns a fresh slice of its keys, each once, strictly increasing in Go's
order on strings. The map has at most `2^62` keys (`slices.Sorted`'s premise). -/
theorem wp_Sorted_Keys_string {V : Type} [ZeroVal V] {T Vt : go.GoType}
    [T ↓u go.MapType go.string Vt] (m : Loc) :
    {{ (True : IProp GF) }}
      (App (Val #(functions maps.Keys [T, go.string, Vt])) (Val #m))
    {{ (f : GoFunc), RET #f;
        □ ∀ (dq : DFrac) (M : GMap GoString V) (Φ : val → IProp GF),
          isPkgInit pkg_id.slices -∗ m ↦${dq} M -∗ ⌜GMap.size M ≤ 2 ^ 62⌝ -∗
          ▷ (∀ (s : GoSlice) (ks : List GoString),
              m ↦${dq} M -∗ s ↦* ks -∗ ownSliceCap GoString s (DFrac.own 1) -∗
              ⌜(∀ k, k ∈ ks ↔ (M !! k).isSome) ∧ ks.Pairwise go.GoStringLt⌝ -∗ Φ #s) -∗
          WP (App (Val #(functions slices.Sorted [go.string])) (Val #f)) {{ Φ }} }} := by
  wp_start_folded as _
  wp_apply (maps.wp_Keys (K := GoString) (V := V) (T := T) (Kt := go.string) (Vt := Vt)).1 m
    with %f #Hf
  iapply HΦ
  imodintro
  iintro %dq %M %Ψ #Hinit HM %Hsize HΨ
  ihave #Hless := slices.lessImplements_string_of (GF := GF) cmp.wp_Less
  iapply slices.wp_Sorted (E := GoString) (Et := go.string) go.GoStringLt
    slices.StrictWeakOrder_goStringLt f (m ↦${dq} M)
    (fun ks => (∀ k, k ∈ ks ↔ (M !! k).isSome) ∧ ks.Nodup) $$ [HM]
  · isplitr
    · iexact Hinit
    isplitr
    · iexact Hf
    isplitl [HM]
    · iexact HM
    isplitr
    · ipureintro
      intro xs ⟨hmem, hnd⟩
      rw [GMap.size_eq_length M xs hnd hmem] at Hsize
      exact Hsize
    iexact Hless
  inext
  iintro %s %xs %ys H
  iNamed H
  obtain ⟨hmem, hnd⟩ := Hok
  iapply HΨ $$ HR Hs Hcap
  ipureintro
  refine ⟨fun k => by rw [← Hperm.mem_iff]; exact hmem k, ?_⟩
  exact pairwise_goStringLt_of_sorted ys (Hperm.nodup_iff.1 hnd) Hsorted

end sortedKeys

end maps

end Perennial
