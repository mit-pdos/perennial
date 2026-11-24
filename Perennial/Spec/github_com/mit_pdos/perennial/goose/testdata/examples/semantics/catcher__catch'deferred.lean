/-
`catcher.catch'deferred`'s spec (a goose semantics test, `recover_deferred.go`).
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

/-- `c.catch(res)` deferred, with the panic `w` (a `uint64`) in the cell `pnc` that its `recover()` reads (`$recover`): it clears the cell, counts and stores `w` through `res`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catcher.catch'deferred.spec : Prop :=
  ∀ (c res pnc : Loc) (s x w : w64),
    {{ (c.[catcher, go!"seen"] ↦ s : IProp GF) ∗ res ↦ x ∗ pnc ↦ interface.mkOk go.uint64 #w }}
      (App (App (Val (c @!! go.GoType.PointerType catcher.ty @!! go!"catch'deferred")) (Val #pnc))
        (Val #res))
    {{ RET #(); c.[catcher, go!"seen"] ↦ (s + W64 1) ∗ res ↦ w ∗ pnc ↦ (interface.nil : GoInterface) }}

end spec

end Perennial
