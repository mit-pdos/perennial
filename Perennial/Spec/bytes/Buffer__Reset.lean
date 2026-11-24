/-
`bytes.Buffer.Reset`'s spec (`buffer.go:99-104`).
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

/-- `b.Reset()` empties the `*Buffer` at `l` (`b.buf = b.buf[:0]`, `b.off = 0`), keeping its
storage for future writes. -/
abbrev bytes.Buffer.Reset.spec : Prop :=
  ∀ (l : Loc) (bs : List w8),
    {{ bytes.ownBuffer (GF := GF) l bs }}
      (App (Val (l @!! go.GoType.PointerType bytes.Buffer.ty @!! go!"Reset")) (Val #()))
    {{ RET #(); bytes.ownBuffer l [] }}

end spec

end Perennial
