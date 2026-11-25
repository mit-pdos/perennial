/-
`fmt.Fprintln`'s spec.
-/
module

public import Perennial.Proof.fmt.PrintArgs

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

/-- `fmt.Fprintln(w, a...)` prints each operand under `%v` (as `fmt.Fprint.spec`; Go also puts a space
between every two operands and a newline at the end, in the unspecified output; `fmt.printArgOk R`: Go calls at most its
`Error()` or `String()`, whose spec may need the resource `R` the caller lends, given back; the
operands' slice comes back too), then calls `w.Write` once with the bytes of some string `s` (the
output is not specified), and returns what `Write` returns. The writer `w` is not `nil`, and its
`Write` has `writeSpec` from `P` to `Q`, as in `fmt.Fprintf.spec`. -/
abbrev fmt.Fprintln.spec : Prop :=
  ∀ (w : GoInterface) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac)
    (P R : IProp GF) (Q : GoString → w64 → GoInterface → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗
        ([∗list] x ∈ xs, fmt.printArgOk R x) ∗ R ∗ P ∗
        ∃ ii, ⌜w = interface.ok ii⌝ ∗ fmt.writeSpec ii P Q }}
      (App (App (Val (@! Fprintln)) (Val #w)) (Val #args_sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); args_sl ↦*{dq} xs ∗ R ∗
        ∃ s : GoString, Q s n err }}

end spec

end Perennial
