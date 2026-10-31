/-
`fmt.Sprintf`'s spec.
-/
module

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
variable [package_sem : fmt.Assumptions]

/-- `fmt.Sprintf(format, args...)` returns a string `s` with `SprintfOut format args s`: `%%`,
`%s` of a `string`, and `%d`, `%v`, `%0Nd` and `%x` of an integer are formatted, the rest of the
output is arbitrary from any other directive on (see the model of `Sprintf`,
`Perennial/TrustedCode/fmt.lean`). The arguments' values must be of their dynamic types where
these are `string` or an integer type, and be of predeclared basic types or of named integer
types without formatting methods (`IsIntArgType`, formatted as integers) (`ArgsWf`). -/
abbrev fmt.Sprintf.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
  ArgsWf xs →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs }}
      (App (App (Val (@! Sprintf)) (Val #format)) (Val #args_sl))
    {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗ ⌜SprintfOut format xs s⌝ }}

end spec

end Perennial
