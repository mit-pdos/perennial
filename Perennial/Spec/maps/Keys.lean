/-
`maps.Keys`'s spec.
-/
module

public import Perennial.Proof.maps.Base
public import Perennial.Golang.Theory.RangeFunc

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

/-- `maps.Keys(m)`, at any type `T` whose underlying type is `map[Kt]Vt`: an iterator over the
keys of `m` (`iter.Seq[Kt]`), returned without reading the map. Each run of the iterator reads the
map as it is then (any fraction of it, held for the whole run, so no write races with it) and
yields each of its keys once, in an order it chooses (Go's is random), stopping early when yield
returns `false` (`iter.SeqRuns`). It may be run any number of times. The iterator of the `nil`
map yields nothing. -/
abbrev maps.Keys.spec : Prop :=
  ∀ {K V : Type} [ZeroVal K] [DecidableEq K] [MapKeys K] [ZeroVal V] [go.IntoValInj K]
    {T Kt Vt : go.GoType} [T ↓u go.MapType Kt Vt]
    [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K Kt],
  (∀ (m : Loc),
    {{ (True : IProp GF) }}
      (App (Val #(functions maps.Keys [T, Kt, Vt])) (Val #m))
    {{ (f : GoFunc), RET #f;
        □ ∀ (dq : DFrac) (M : GMap K V), iter.SeqRuns f (m ↦${dq} M)
          (fun ks => (∀ k, k ∈ ks ↔ (M !! k).isSome) ∧ ks.Nodup) }}) ∧
  {{ (True : IProp GF) }}
    (App (Val #(functions maps.Keys [T, Kt, Vt])) (Val #map.nil))
  {{ (f : GoFunc), RET #f; □ iter.SeqRuns (E := K) f emp (fun ks => ks = []) }}

end spec

end Perennial
