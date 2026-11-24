/-
`fmt.(*fmt).fmtQ`'s spec.
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

/-- `f.fmtQ(s)` without the flags `#` and `+`, a precision or a width: appends `s` double-quoted as
a Go literal (`strconv.AppendQuote` into `f.intbuf[:0]`, then `pad`), of which `strconv`'s spec
says nothing more: some bytes. For `s` of at most `maxAddr` bytes (`strconv.AppendQuote`). -/
abbrev fmt.fmt.fmtQ.spec : Prop :=
  ∀ (f b : Loc) (F : fmtFlags) (wid prec : w64) (bs s : GoString),
    F.sharp' = false → F.plus' = false → F.precPresent' = false →
    (F.widPresent' = false ∨ wid = W64 0) → s.length ≤ maxAddr →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ fmtOwn (GF := GF) f b F wid prec ∗ intbufOwn f ∗
        bufferOwn b bs }}
      (App (Val (f @!! go.GoType.PointerType fmt.fmt.ty @!! go!"fmtQ")) (Val #s))
    {{ RET #(); ∃ q : GoString, fmtOwn f b F wid prec ∗ intbufOwn f ∗ bufferOwn b (bs ++ q) }}

end spec

end Perennial
