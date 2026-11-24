/-
`catcher.catchTwice'deferred`'s spec (a goose semantics test, `recover_deferred.go`).
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

/-- `c.catchTwice(res)` deferred, with the panic `w` in the cell `pnc` (its `$recover`): it recovers `w`, panics with `w + 1`, and its own deferred literal recovers that through its own `$panic` cell and stores `(w + 1) * 10`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catcher.catchTwice'deferred.spec : Prop :=
  ∀ (c res pnc : Loc) (x w : w64),
    {{ (res ↦ x : IProp GF) ∗ pnc ↦ interface.mkOk go.uint64 #w }}
      (App (App (Val (c @!! go.GoType.PointerType catcher.ty @!! go!"catchTwice'deferred")) (Val #pnc))
        (Val #res))
    {{ RET #(); res ↦ ((w + W64 1) * W64 10) ∗ pnc ↦ (interface.nil : GoInterface) }}

end spec

end Perennial
