/-
Results of `maps` derived from the linked ones: `Clone`, `Equal` and `Copy` at `map[string]bool`, which
check that the specs' premises (`SafeMapKey`, `IsStrictlyComparable`) are found for a key type
and a value type that are strictly comparable.
-/
module

public import Perennial.Proof.maps.Link

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

end maps

end Perennial
