/-
`fmt.(*pp).printArg`'s spec.
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

/-- `p.printArg(arg, verb)` for the directive `%verb`, `%0Nverb` or `%.Pverb` (`md`: the flags,
width and precision `doPrintf` sets for it, `Mod.flags`, `Mod.wid`, `Mod.precW`) of an argument
`arg` that is `a` (`isArg`), in the verified subset (`Mod.Ok`): appends what Go writes for it
(`Mod.Out`), leaving `arg` in `p.arg`. -/
abbrev fmt.pp.printArg.spec : Prop :=
  ∀ (p : Loc) (arg : GoInterface) (a : Arg) (bs : GoString) (md : Mod) (verb : w8),
    md.Ok verb a →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ isPrinter p bs md.flags md.wid md.precW ∗
        isArg arg a }}
      (App (App (Val (p @!! go.GoType.PointerType pp.ty @!! go!"printArg")) (Val #arg)) (Val #(W32 (uint.nat verb))))
    {{ RET #(); ∃ o : GoString, ⌜md.Out verb a o⌝ ∗
        isPrinterA p arg (bs ++ o) md.flags md.wid md.precW ∗ isArg arg a }}

end spec

end Perennial
