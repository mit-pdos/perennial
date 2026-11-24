/-
`fmt.(*pp).catchPanic (deferred)`'s spec.
-/
module

public import Perennial.Proof.fmt.PrintDefs

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

/-- `p.catchPanic(arg, verb, method)` deferred while nothing is panicking (the cell `pnc` that its
`recover()` reads is `nil`): does nothing. -/
abbrev fmt.pp.catchPanic'deferred.spec : Prop :=
  ∀ (p pnc : Loc) (arg : GoInterface) (verb : w32) (method : GoString),
    {{ (pnc ↦ (interface.nil : GoInterface) : IProp GF) }}
      (App (App (App (App (Val (p @!! go.GoType.PointerType pp.ty @!! go!"catchPanic'deferred")) (Val #pnc))
        (Val #arg)) (Val #verb)) (Val #method))
    {{ RET #(); pnc ↦ (interface.nil : GoInterface) }}

end spec

end Perennial
