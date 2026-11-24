/-
`repanicInner`'s spec (a goose semantics test, `recover_deferred.go`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Base

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

/-- `repanicInner(c)`: the deferred `c.catchAndRepanic()` recovers 5, counts, and panics with 6. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.repanicInner.spec : Prop :=
  ∀ (c : Loc) (s : w64) (Φ : val → IProp GF),
    (c.[catcher, go!"seen"] ↦ s : IProp GF) -∗
    ((c.[catcher, go!"seen"] ↦ (s + W64 1) : IProp GF) -∗
      Φ (PanicV #(interface.mkOk go.uint64 #(W64 6)))) -∗
    WP (App (Val (@! repanicInner)) (Val #c)) {{ Φ }}

end spec

end Perennial
