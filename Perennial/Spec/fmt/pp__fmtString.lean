/-
`fmt.(*pp).fmtString`'s spec.
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

/-- `p.fmtString(v, verb)` without flags, `verb` one of `s v x`: appends `v` (`s`, `v`) or its
hexadecimal (`x`). -/
abbrev fmt.pp.fmtString.spec : Prop :=
  ∀ (p : Loc) (x : GoInterface) (bs : GoString) (wid prec : w64) (v : GoString) (verb : w8),
    (verb = verb_s ∨ verb = verb_v ∨ verb = verb_x) →
    {{ isPrinterA (GF := GF) p x bs noFlags wid prec }}
      (App (App (Val (p @!! go.GoType.PointerType pp.ty @!! go!"fmtString")) (Val #v)) (Val #(W32 (uint.nat verb))))
    {{ RET #(); isPrinterA p x (bs ++ if verb = verb_x then bytesHex false v else v)
        noFlags wid prec }}

end spec

end Perennial
