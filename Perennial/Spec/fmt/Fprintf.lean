/-
`fmt.Fprintf`'s spec.
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

/-- `fmt.Fprintf(w, format, args...)` formats as `Sprintf` does (a string `s` with
`SprintfOut format args s`; the arguments `argsOk` the format under the method verbs, their slice
coming back), then calls `w.Write` once with the bytes of `s`, and returns what it returns. The
writer `w` is not `nil` (Go panics calling `Write` of a `nil` interface), and its `Write` has
`writeSpec` from `P` to `Q`: the caller chooses what `Write` needs and gives back. -/
abbrev fmt.Fprintf.spec : Prop :=
  ∀ (w : GoInterface) (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac)
    (P : IProp GF) (Q : GoString → w64 → GoInterface → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗
        fmt.argsOk fmt.methodVerbs format xs ∗ P ∗
        ∃ ii, ⌜w = interface.ok ii⌝ ∗ fmt.writeSpec ii P Q }}
      (App (App (App (Val (@! Fprintf)) (Val #w)) (Val #format)) (Val #args_sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); args_sl ↦*{dq} xs ∗
        ∃ s : GoString, ⌜SprintfOut format xs s⌝ ∗ Q s n err }}

end spec

end Perennial
