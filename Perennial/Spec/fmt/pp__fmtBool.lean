/-
`fmt.(*pp).fmtBool`'s spec.
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

/-- `p.fmtBool(v, verb)`, `%v` without flags: appends `true` or `false`. -/
abbrev fmt.pp.fmtBool.spec : Prop :=
  ∀ (p : Loc) (x : GoInterface) (bs : GoString) (wid prec : w64) (v : Bool),
    {{ isPrinterA (GF := GF) p x bs noFlags wid prec }}
      (App (App (Val (p @!! go.GoType.PointerType pp.ty @!! go!"fmtBool")) (Val #v)) (Val #(W32 118)))
    {{ RET #(); isPrinterA p x (bs ++ if v then go!"true" else go!"false") noFlags wid prec }}

end spec

end Perennial
