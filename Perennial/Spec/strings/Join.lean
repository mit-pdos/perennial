/-
`strings.Join`'s spec.
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `strings.Join(elems, sep)`: the elements of `elems` separated by `sep`, if the result is
shorter than `2^61` bytes. Go's `Join` panics when the result's length overflows an `int`, which a
program can reach with a few gigabytes of aliased elements and a long separator; the bound also
covers `Builder.Grow`'s (`Builder.Grow.spec`). -/
abbrev strings.Join.spec : Prop :=
  ∀ (elems : GoSlice) (xs : List GoString) (dq : DFrac) (sep : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ elems ↦*{dq} xs ∗
        ⌜(sep.intercalate xs).length < 2 ^ 61⌝ }}
      (App (App (Val (@! Join)) (Val #elems)) (Val #sep))
    {{ RET #(sep.intercalate xs); elems ↦*{dq} xs }}

end spec

end Perennial
