/-
`fmt.Printf`'s spec.
-/
module

public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- `fmt.Printf(format, args...)` returns; the output is not modelled, nor the results. The
arguments `args_sl ↦*{dq} xs` must be of predeclared basic types (`ArgsWf`), as for
`wp_Sprintf`: Go calls the methods of other arguments, which the model does not. -/
abbrev fmt.Printf.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
  ArgsWf xs →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs }}
      (App (App (Val (@! Printf)) (Val #format)) (Val #args_sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); args_sl ↦*{dq} xs }}

end spec

end Perennial
