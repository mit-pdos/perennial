/-
`github.com/goose-lang/std.BytesEqual`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.std.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

/-- `BytesEqual(s1, s2)`: whether the two byte slices have the same contents. -/
abbrev github_com.goose_lang.std.BytesEqual.spec : Prop :=
  ∀ (s1 s2 : GoSlice) (xs1 xs2 : List w8) (dq1 dq2 : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std ∗
        s1 ↦*{dq1} xs1 ∗ s2 ↦*{dq2} xs2 }}
      (App (App (Val (@! BytesEqual)) (Val #s1)) (Val #s2))
    {{ RET #(decide (xs1 = xs2)); s1 ↦*{dq1} xs1 ∗ s2 ↦*{dq2} xs2 }}

end spec

end Perennial
