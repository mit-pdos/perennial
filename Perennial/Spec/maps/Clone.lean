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

/-- `maps.Clone(m)` (a trusted model, `TrustedCode/maps.lean`: Go's calls the runtime), at a map
type `map[Kt]Vt` whose keys are safe (`SafeMapKey`: `==` on them is equality): of a map `m` (any
fraction of it), a fresh map `m'` with the same entries, which the caller owns alone; `m` is only
read. Of the `nil` map, `nil`. Stated at the literal map type: the model's `make(M, len(m))` is
defined only there (the semantics' `make` of a map takes the literal type). -/
abbrev maps.Clone.spec : Prop :=
  ∀ {K V : Type} [ZeroVal K] [DecidableEq K] [MapKeys K] [ZeroVal V] [go.IntoValInj K]
    {Kt Vt : go.GoType} [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K Kt]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V Vt]
    [∀ k : K, SafeMapKey (GF := GF) Kt k],
  (∀ (m : Loc) (dq : DFrac) (M : GMap K V),
    {{ (m ↦${dq} M : IProp GF) }}
      (App (Val #(functions maps.Clone [go.MapType Kt Vt, Kt, Vt])) (Val #m))
    {{ (m' : Loc), RET #m'; m ↦${dq} M ∗ m' ↦$ M }}) ∧
  {{ (True : IProp GF) }}
    (App (Val #(functions maps.Clone [go.MapType Kt Vt, Kt, Vt])) (Val #map.nil))
  {{ RET #map.nil; True }}

end spec

end Perennial
