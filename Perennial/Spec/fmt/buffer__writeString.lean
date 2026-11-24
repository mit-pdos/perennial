/-
`fmt.(*buffer).writeString`'s spec.
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

/-- `b.writeString(s)`: appends `s` to the buffer at `b`. -/
abbrev fmt.buffer.writeString.spec : Prop :=
  ∀ (b : Loc) (bs s : GoString),
    {{ bufferOwn (GF := GF) b bs }}
      (App (Val (b @!! go.GoType.PointerType buffer.ty @!! go!"writeString")) (Val #s))
    {{ RET #(); bufferOwn b (bs ++ s) }}

end spec

end Perennial
