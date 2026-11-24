/-
`fmt.(*buffer).writeByte`'s spec.
-/
module

public import Perennial.Proof.fmt.PrintDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- `b.writeByte(c)`: appends `c` to the buffer at `b`. -/
abbrev fmt.buffer.writeByte.spec : Prop :=
  ∀ (b : Loc) (bs : GoString) (c : w8),
    {{ bufferOwn (GF := GF) b bs }}
      (App (Val (b @!! go.GoType.PointerType buffer.ty @!! go!"writeByte")) (Val #c))
    {{ RET #(); bufferOwn b (bs ++ [c]) }}

end spec

end Perennial
