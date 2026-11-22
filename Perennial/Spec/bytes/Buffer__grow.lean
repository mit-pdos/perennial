/-
`bytes.Buffer.grow`'s spec.
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

/-- `b.grow(n)` (`0 ≤ n ≤ maxAddr`, the length of an owned slice) of a `*Buffer` whose `buf` holds
`all`, with its capacity, and whose unread bytes are `all[off:]`: makes room for `n` more bytes
and returns the index `i` where they go (`bytes.bufferGrown`: the unread bytes kept before
`i`). Its `panic(ErrTooLarge)` is unreachable: an owned buffer's capacity is at most
`2 * maxAddr`. -/
abbrev bytes.Buffer.grow.spec : Prop :=
  ∀ (l : Loc) (b : bytes.Buffer) (all : List w8) (n : w64),
    {{ l ↦ b ∗ b.buf' ↦* all ∗ ownSliceCap w8 b.buf' (DFrac.own 1) ∗
        ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ maxAddr ∧ 0 ≤ sint.Z b.off' ∧ sint.nat b.off' ≤ all.length⌝ }}
      (App (Val (l @!! go.GoType.PointerType bytes.Buffer.ty @!! go!"grow")) (Val #n))
    {{ (i : w64), RET #i; bytes.bufferGrown (GF := GF) l (all.drop (sint.nat b.off')) i n }}

end spec

end Perennial
