/-
`log.Printf`'s spec.
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

/-- `log.Printf(format, args...)` returns; the output is not modelled. The model
(`TrustedCode/log.lean`) does nothing, while Go formats the arguments as `fmt.Sprintf` does,
calling the `Error()`/`String()` methods of arguments that have them: so the arguments must be of
predeclared basic types (`fmt.ArgsWf`), for which Go calls no method. -/
abbrev log.Printf.spec : Prop :=
  ∀ (msg : GoString) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
  fmt.ArgsWf xs →
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs }}
      (App (App (Val (@! Printf)) (Val #msg)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}

end spec

end Perennial
