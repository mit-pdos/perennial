/-
`maps.Clone`'s spec.
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

/-- `maps.Clone(m)` (Go's calls the runtime's `maps_clone` through `clone`, whose model is the
semantics' `InternalMapClone`), at any type `T` whose underlying type is `map[Kt]Vt`: of a map `m`
(any fraction of it), a fresh map `m'` with the same entries, which the caller owns alone; `m` is
only read. Of the `nil` map, `nil`. -/
abbrev maps.Clone.spec : Prop :=
  ∀ {K V : Type} [ZeroVal K] [DecidableEq K] [MapKeys K] [ZeroVal V] [go.IntoValInj K]
    {T Kt Vt : go.GoType} [T ↓u go.MapType Kt Vt],
  (∀ (m : Loc) (dq : DFrac) (M : GMap K V),
    {{ (m ↦${dq} M : IProp GF) }}
      (App (Val #(functions maps.Clone [T, Kt, Vt])) (Val #m))
    {{ (m' : Loc), RET #m'; m ↦${dq} M ∗ m' ↦$ M }}) ∧
  {{ (True : IProp GF) }}
    (App (Val #(functions maps.Clone [T, Kt, Vt])) (Val #map.nil))
  {{ RET #map.nil; True }}

end spec

end Perennial
