/-
`pageBytes`'s spec (`goose/testdata/examples/unsafememory`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Pages

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Assumptions]

/-- `pageBytes(p, n)` is the byte slice of the `n` bytes from `p`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageBytes.spec : Prop :=
  ∀ (p : Loc) (n : w64),
    {{ (⌜0 < p.addr ∧ p.addr + sint.Z n ≤ maxAddr ∧ 0 ≤ sint.Z n⌝ : IProp GF) }}
      (App (App (Val (@! pageBytes)) (Val #p)) (Val #n))
    {{ RET #(slice.mk p n n); True }}

end spec

end Perennial
