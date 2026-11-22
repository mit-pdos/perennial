/-
`bytes.Buffer.Bytes`'s spec.
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

/-- `b.Bytes()` of a `*Buffer` holding the unread bytes `bs`: the slice `b.buf[b.off:]` of them. It
aliases the buffer (Go: "The slice is valid for use only until the next buffer modification"),
so the buffer is given up for the slice, and is back, holding the slice's bytes then, when the
slice is given back. -/
abbrev bytes.Buffer.Bytes.spec : Prop :=
  ∀ (l : Loc) (bs : List w8),
    {{ bytes.ownBuffer (GF := GF) l bs }}
      (App (Val (l @!! go.GoType.PointerType bytes.Buffer.ty @!! go!"Bytes")) (Val #()))
    {{ (s : GoSlice), RET #s;
        s ↦* bs ∗ (∀ bs' : List w8, s ↦* bs' -∗ bytes.ownBuffer l bs') }}

end spec

end Perennial
