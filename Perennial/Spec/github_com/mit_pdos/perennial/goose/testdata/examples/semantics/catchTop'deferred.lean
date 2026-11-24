/-
`catchTop'deferred`'s spec (a goose semantics test, `recover_deferred.go`).
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

/-- `catchTop(res)` deferred, with the panic `w` in the cell `pnc`: it clears the cell and stores `w` through `res`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catchTop'deferred.spec : Prop :=
  ∀ (res pnc : Loc) (x w : w64),
    {{ (res ↦ x : IProp GF) ∗ pnc ↦ interface.mkOk go.uint64 #w }}
      (App (App (Val (@! deferred'catchTop)) (Val #pnc)) (Val #res))
    {{ RET #(); res ↦ w ∗ pnc ↦ (interface.nil : GoInterface) }}

end spec

end Perennial
