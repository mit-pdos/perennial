/-
`bytes.growSlice`'s spec.
-/
module

public import Perennial.Proof.bytes.BufferBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

/-- `growSlice(s, n)` (`n ≥ 0`): a new slice holding `s`'s bytes, with room for `n` more in its
(owned) capacity; it only reads `s`. Go's arithmetic on `len(s) + n` and `2 * cap(s)` does not
overflow for the sizes of an owned buffer (at most `2 * maxAddr`), so it does not panic. -/
abbrev bytes.growSlice.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (bs : List w8) (n : w64),
    {{ (s ↦*{dq} bs : IProp GF) ∗ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 2 * maxAddr ∧ sint.Z s.cap ≤ 2 * maxAddr⌝ }}
      (App (App (Val (@! bytes.growSlice)) (Val #s)) (Val #n))
    {{ (s' : GoSlice), RET #s';
        s ↦*{dq} bs ∗ s' ↦* bs ∗ ownSliceCap w8 s' (DFrac.own 1) ∗
        ⌜sint.Z s.len + sint.Z n ≤ sint.Z s'.cap⌝ }}

end spec

end Perennial
