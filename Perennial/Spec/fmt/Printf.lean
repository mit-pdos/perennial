/-
`fmt.Printf`'s spec.
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

/-- `fmt.Printf(format, args...)` returns; the output is not modelled, nor the results. The
arguments are `argsOk` the format under the method verbs, as for `Sprintf` (Go calls their
`Error()`/`String()` methods where its formatting does); the arguments' slice comes back. -/
abbrev fmt.Printf.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗
        fmt.argsOk fmt.methodVerbs format xs }}
      (App (App (Val (@! Printf)) (Val #format)) (Val #args_sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); args_sl ↦*{dq} xs }}

end spec

end Perennial
