/-
`fmt.(*buffer).write`'s spec.
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

/-- `b.write(p)`: appends the bytes of `p` to the buffer at `b`. -/
abbrev fmt.buffer.write.spec : Prop :=
  ∀ (b : Loc) (bs : GoString) (sl : GoSlice) (ys : GoString) (q : DFrac),
    {{ bufferOwn (GF := GF) b bs ∗ sl ↦*{q} ys }}
      (App (Val (b @!! go.GoType.PointerType buffer.ty @!! go!"write")) (Val #sl))
    {{ RET #(); bufferOwn b (bs ++ ys) ∗ sl ↦*{q} ys }}

end spec

end Perennial
