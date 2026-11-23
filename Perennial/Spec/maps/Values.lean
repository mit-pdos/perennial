/-
`maps.Values`'s spec.
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

/-- `maps.Values(m)`, at any type `T` whose underlying type is `map[Kt]Vt`: an iterator over the
values of `m` (`iter.Seq[Vt]`), returned without reading the map, as `maps.Keys`'s: each run reads the
map as it is then (any fraction, held for the whole run) and yields the value of each of its keys
`ks` once, in an order it chooses (`vs` lists the values of `ks` in that order), stopping early
when yield returns `false` (`iter.SeqRuns`). It may be run any number of times. The iterator of
the `nil` map yields nothing. -/
abbrev maps.Values.spec : Prop :=
  ∀ {K V : Type} [ZeroVal K] [DecidableEq K] [MapKeys K] [ZeroVal V] [go.IntoValInj K]
    {T Kt Vt : go.GoType} [T ↓u go.MapType Kt Vt]
    [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K Kt]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V Vt],
  (∀ (m : Loc),
    {{ (True : IProp GF) }}
      (App (Val #(functions maps.Values [T, Kt, Vt])) (Val #m))
    {{ (f : GoFunc), RET #f;
        □ ∀ (dq : DFrac) (M : GMap K V), iter.SeqRuns f (m ↦${dq} M)
          (fun vs => ∃ ks : List K, ((∀ k, k ∈ ks ↔ (M !! k).isSome) ∧ ks.Nodup) ∧
            List.Forall₂ (fun k v => M !! k = some v) ks vs) }}) ∧
  {{ (True : IProp GF) }}
    (App (Val #(functions maps.Values [T, Kt, Vt])) (Val #map.nil))
  {{ (f : GoFunc), RET #f; □ iter.SeqRuns (E := V) f emp (fun vs => vs = []) }}

end spec

end Perennial
