/-
`fmt.(*fmt).pad`'s spec.
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

/-- `f.pad(p)`: appends the bytes `ys` of `p`, when no padding is needed: no width, or ASCII bytes
at least as many as the width (what `fmtInteger` pads with `%0N`, its digits already zero-padded
to the width). -/
abbrev fmt.fmt.pad.spec : Prop :=
  ∀ (f b : Loc) (F : fmtFlags) (wid prec : w64) (bs : GoString) (sl : GoSlice) (ys : GoString)
    (q : DFrac),
    F.widPresent' = false ∨ wid = W64 0 ∨
      ((∀ c ∈ ys, uint.Z c < 128) ∧ sint.Z wid ≤ ys.length) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ fmtOwn (GF := GF) f b F wid prec ∗ bufferOwn b bs ∗ sl ↦*{q} ys }}
      (App (Val (f @!! go.GoType.PointerType fmt.fmt.ty @!! go!"pad")) (Val #sl))
    {{ RET #(); fmtOwn f b F wid prec ∗ bufferOwn b (bs ++ ys) ∗ sl ↦*{q} ys }}

end spec

end Perennial
