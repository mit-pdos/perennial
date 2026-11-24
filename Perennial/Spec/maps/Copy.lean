/-
`maps.Copy`'s spec.
-/
module

public import Perennial.Proof.maps.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI map

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : maps.Assumptions]

/-- `maps.Copy(dst, src)` (`for k, v := range src { dst[k] = v }`), at any map types `M1`, `M2`
whose underlying type is `map[Kt]Vt`, with safe keys (`SafeMapKey`, as `Equal`'s spec): `dst` (owned)
ends holding `src`'s entries over its own (`S ∪ D`, `GMap`'s union prefers its left operand); `src`
(any fraction) is only read. -/
abbrev maps.Copy.spec : Prop :=
  ∀ {K V : Type} [ZeroVal K] [DecidableEq K] [MapKeys K] [ZeroVal V]
    [go.IntoValInj K] {Kt Vt M1 M2 : go.GoType} [M1 ↓u go.MapType Kt Vt] [M2 ↓u go.MapType Kt Vt]
    [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K Kt]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V Vt]
    [∀ k : K, SafeMapKey (GF := GF) Kt k]
    (dst src : Loc) (dq : DFrac) (D S : GMap K V),
  {{ (dst ↦$ D ∗ src ↦${dq} S : IProp GF) }}
    (App (App (Val #(functions maps.Copy [M1, M2, Kt, Vt])) (Val #dst)) (Val #src))
  {{ RET #(); dst ↦$ (S ∪ D) ∗ src ↦${dq} S }}

end spec

end Perennial
