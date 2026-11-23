/-
`maps.Equal`'s spec.
-/
module

public import Perennial.Proof.maps.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std map

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : maps.Assumptions]

/-- `maps.Equal(m1, m2)`, at any two types `M1`, `M2` whose underlying type is `map[Kt]Vt`, with
safe keys (`SafeMapKey`: `==` on them is equality) and a strictly comparable value type (`==` on
values is equality, so it never panics: not an interface holding an uncomparable value, nor a
float `NaN`): of two maps (any fractions of them, possibly the same map), whether they have the
same entries; both are only read. The `nil` map (equal in Go to an empty one) is not covered. -/
abbrev maps.Equal.spec : Prop :=
  ∀ {K V : Type} [ZeroVal K] [DecidableEq K] [MapKeys K] [ZeroVal V] [DecidableEq V]
    [go.IntoValInj K] {Kt Vt T1 T2 : go.GoType} [T1 ↓u go.MapType Kt Vt] [T2 ↓u go.MapType Kt Vt]
    [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K Kt]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V Vt]
    [∀ k : K, SafeMapKey (GF := GF) Kt k] [go.IsStrictlyComparable Vt V]
    (m1 m2 : Loc) (dq1 dq2 : DFrac) (M1 M2 : GMap K V),
  {{ (m1 ↦${dq1} M1 ∗ m2 ↦${dq2} M2 : IProp GF) }}
    (App (App (Val #(functions maps.Equal [T1, T2, Kt, Vt])) (Val #m1)) (Val #m2))
  {{ (b : Bool), RET #b; ⌜b = true ↔ M1 = M2⌝ ∗ m1 ↦${dq1} M1 ∗ m2 ↦${dq2} M2 }}

end spec

end Perennial
