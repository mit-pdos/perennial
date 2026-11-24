/-
`fmt.(*pp).fmtBytes`'s spec.
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

/-- `p.fmtBytes(v, verb, typeString)` without flags, `verb` one of `s v d x`: appends the bytes `ys`
of `v` (`s`), their decimals in brackets (`v`, `d`: `bytesDec`) or their hexadecimal (`x`). -/
abbrev fmt.pp.fmtBytes.spec : Prop :=
  ∀ (p : Loc) (x : GoInterface) (bs : GoString) (wid prec : w64) (sl : GoSlice) (ys : GoString)
    (q : DFrac) (verb : w8) (typeString : GoString),
    (verb = verb_s ∨ verb = verb_v ∨ verb = verb_d ∨ verb = verb_x) →
    (verb = verb_x → ys.length < 2 ^ 62) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ isPrinterA p x bs noFlags wid prec ∗ sl ↦*{q} ys }}
      (App (App (App (Val (p @!! go.GoType.PointerType pp.ty @!! go!"fmtBytes")) (Val #sl)) (Val #(W32 (uint.nat verb))))
        (Val #typeString))
    {{ RET #(); isPrinterA p x (bs ++ if verb = verb_s then ys
          else if verb = verb_x then bytesHex false ys else bytesDec ys) noFlags wid prec ∗
        sl ↦*{q} ys }}

end spec

end Perennial
