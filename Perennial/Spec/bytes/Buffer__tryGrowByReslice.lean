/-
`bytes.Buffer.tryGrowByReslice`'s spec.
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

/-- `b.tryGrowByReslice(n)` (`n ≥ 0`) of a `*Buffer` whose `buf` holds `all`, with its capacity,
and whose unread bytes are `all[off:]`: if `n` more bytes fit in `buf`'s capacity, it extends
`buf` by `n` bytes and returns its old length and `true` (`bytes.bufferGrown`); else `0, false`,
changing nothing. -/
abbrev bytes.Buffer.tryGrowByReslice.spec : Prop :=
  ∀ (l : Loc) (b : bytes.Buffer) (all : List w8) (n : w64),
    {{ l ↦ b ∗ b.buf' ↦* all ∗ ownSliceCap w8 b.buf' (DFrac.own 1) ∗
        ⌜0 ≤ sint.Z n ∧ 0 ≤ sint.Z b.off' ∧ sint.nat b.off' ≤ all.length⌝ }}
      (App (Val (l @!! go.GoType.PointerType bytes.Buffer.ty @!! go!"tryGrowByReslice")) (Val #n))
    {{ (i : w64) (ok : Bool), RET (PairV #i #ok);
        if ok then bytes.bufferGrown (GF := GF) l (all.drop (sint.nat b.off')) i n
        else iprop(⌜sint.Z b.buf'.cap - sint.Z b.buf'.len < sint.Z n ∧ i = W64 0⌝ ∗
          l ↦ b ∗ b.buf' ↦* all ∗ ownSliceCap w8 b.buf' (DFrac.own 1)) }}

end spec

end Perennial
