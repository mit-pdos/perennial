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

/-- `p.printArg(arg, verb)` for the directive `%verb` or `%0Nverb` (`dirFlags zw`, `dirWid zw`) of
an argument `arg` that is `a` (`isArg`), in the verified subset (`DirOk`): appends what Go writes
for it (`DirOut`), leaving `arg` in `p.arg`. -/
abbrev fmt.pp.printArg.spec : Prop :=
  ∀ (p : Loc) (arg : GoInterface) (a : Arg) (bs : GoString) (zw : Option Nat) (verb : w8),
    DirOk zw verb a →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ isPrinter p bs (dirFlags zw) (dirWid zw) (W64 0) ∗
        isArg arg a }}
      (App (App (Val (p @!! go.GoType.PointerType pp.ty @!! go!"printArg")) (Val #arg)) (Val #(W32 (uint.nat verb))))
    {{ RET #(); ∃ o : GoString, ⌜DirOut zw verb a o⌝ ∗
        isPrinterA p arg (bs ++ o) (dirFlags zw) (dirWid zw) (W64 0) ∗ isArg arg a }}

end spec

end Perennial
