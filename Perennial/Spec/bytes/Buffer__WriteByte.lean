/-
`bytes.Buffer.WriteByte`'s spec.
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

/-- `b.WriteByte(c)` of a `*Buffer` holding the unread bytes `bs`: appends `c` (growing the buffer
as needed) and returns `nil`. Go's `WriteByte` panics with `ErrTooLarge` only when the buffer
cannot grow, which an owned buffer's size excludes. -/
abbrev bytes.Buffer.WriteByte.spec : Prop :=
  ∀ (l : Loc) (bs : List w8) (c : w8),
    {{ bytes.ownBuffer (GF := GF) l bs }}
      (App (Val (l @!! go.GoType.PointerType bytes.Buffer.ty @!! go!"WriteByte")) (Val #c))
    {{ RET #interface.nil; bytes.ownBuffer l (bs ++ [c]) }}

end spec

end Perennial
