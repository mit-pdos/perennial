/-
`bytes.Buffer.String`'s spec (`buffer.go:72-78`).
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

/-- `b.String()` of a `*Buffer` holding the unread bytes `bs`: the string of them,
`string(b.buf[b.off:])` (a copy: the buffer is kept). (A `nil` `b` returns `"<nil>"`; an owned
buffer is not `nil`.) -/
abbrev bytes.Buffer.String.spec : Prop :=
  ∀ (l : Loc) (bs : List w8),
    {{ bytes.ownBuffer (GF := GF) l bs }}
      (App (Val (l @!! go.GoType.PointerType bytes.Buffer.ty @!! go!"String")) (Val #()))
    {{ RET #(bs : GoString); bytes.ownBuffer l bs }}

end spec

end Perennial
