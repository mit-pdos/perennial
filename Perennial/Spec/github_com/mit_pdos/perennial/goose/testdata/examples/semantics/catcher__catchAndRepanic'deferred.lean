/-
`catcher.catchAndRepanic'deferred`'s spec (a goose semantics test, `recover_deferred.go`).
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

/-- `c.catchAndRepanic()` deferred, with the panic `w` in the cell `pnc`: it clears the cell, counts, and panics with `w + 1`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catcher.catchAndRepanic'deferred.spec : Prop :=
  ∀ (c pnc : Loc) (s w : w64) (Φ : val → IProp GF),
    (c.[catcher, go!"seen"] ↦ s : IProp GF) -∗ pnc ↦ interface.mkOk go.uint64 #w -∗
    ((c.[catcher, go!"seen"] ↦ (s + W64 1) : IProp GF) -∗ pnc ↦ (interface.nil : GoInterface) -∗
      Φ (PanicV #(interface.mkOk go.uint64 #(w + W64 1)))) -∗
    WP (App (App (Val (c @!! go.GoType.PointerType catcher.ty @!! go!"catchAndRepanic'deferred"))
      (Val #pnc)) (Val #())) {{ Φ }}

end spec

end Perennial
