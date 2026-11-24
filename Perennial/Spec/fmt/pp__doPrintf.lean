/-
`fmt.(*pp).doPrintf`'s spec.
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

/-- `p.doPrintf(format, a)`, for a format made of the pieces `ps` and arguments that are the `as`
(`isArg`), in the verified subset (`Fits`): appends `out` with `Out ps args out`. -/
abbrev fmt.pp.doPrintf.spec : Prop :=
  ∀ (p : Loc) (bs format : GoString) (ps : List Piece) (args_sl : GoSlice)
    (xs : List GoInterface) (args : List Arg) (dq : DFrac),
    format = encode ps → Fits ps args →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ isPrinterAny p bs ∗ args_sl ↦*{dq} xs ∗
        [∗list] x;a ∈ xs;args, isArg x a }}
      (App (App (Val (p @!! go.GoType.PointerType pp.ty @!! go!"doPrintf")) (Val #format)) (Val #args_sl))
    {{ RET #(); ∃ out : GoString, ⌜Out ps args out⌝ ∗ isPrinterAny p (bs ++ out) ∗
        args_sl ↦*{dq} xs ∗ [∗list] x;a ∈ xs;args, isArg x a }}

end spec

end Perennial
