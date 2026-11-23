/-
`fmt.Sprintf`'s spec.
-/
module

public import Perennial.Proof.fmt.Args

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

/-- `fmt.Sprintf(format, args...)` returns a string `s` with `SprintfOut format args s`: `%%`, and
`%s`/`%v` of a string (a `string`, or a named string type without formatting methods,
`StrArgValue`), `%d`, `%v`, `%0Nd` and `%x` of an integer, are formatted, the rest of the output is
arbitrary from any other directive on (see the model of `Sprintf`, `Perennial/TrustedCode/fmt.lean`).
The arguments are `argsOk` the format under the method verbs `v s x X q`: Go calls their
`Error()`/`String()` methods where its formatting does, which must return some string needing
nothing (`argOk`); the arguments' slice comes back. -/
abbrev fmt.Sprintf.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗
        fmt.argsOk fmt.methodVerbs format xs }}
      (App (App (Val (@! Sprintf)) (Val #format)) (Val #args_sl))
    {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗ ⌜SprintfOut format xs s⌝ }}

end spec

end Perennial
