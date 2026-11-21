/-
`fmt.Errorf`'s spec.
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

/-- `fmt.Errorf(format, args...)` returns a non-nil error `err` (`errorfErr`) whose `Error()` returns
the formatted string `s`, with `SprintfOut format args s` (as `Sprintf`'s output; a `%w` of an error
is formatted as `%v`, which `SprintfOut` leaves arbitrary): an `*errors.errorString` when the format
has no `%w` directive with an argument, a `*fmt.wrapError` holding the argument as an `error` when
it has one, a `*fmt.wrapErrors` when it has several, as Go's `errorf` returns (only the first two
facts when the format has a directive `fmtDirectives` refuses). The arguments are `argsOk` the
format under `Errorf`'s verbs (the method verbs and `w`); the arguments' slice comes back. -/
abbrev fmt.Errorf.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗
        fmt.argsOk fmt.errorfVerbs format xs }}
      (App (App (Val (@! Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err);
        args_sl ↦*{dq} xs ∗ ∃ s : GoString, ⌜SprintfOut format xs s⌝ ∗ fmt.errorfErr format xs s err }}

end spec

end Perennial
