/-
`log.Println`'s spec.
-/
module

public import Perennial.Proof.log.Base
public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions]

/-- `log.Println(args...)` returns; the output is not modelled. The model
(`goose/model/overlay/log`) formats the arguments as `fmt.Fprintln` does, or does nothing, and Go
formats them as `fmt.Appendln` does, calling the `Error()`/`String()` methods of arguments that have
them: here the arguments are of predeclared basic types or named integer types without formatting
methods (`fmt.ArgsWf`), for which Go calls no method. -/
abbrev log.Println.spec : Prop :=
  ∀ (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
  fmt.ArgsWf xs →
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs }}
      (App (Val (@! Println)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}

end spec

end Perennial
