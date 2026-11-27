/-
`runtime.Caller`'s spec.
-/
module

public import Perennial.Proof.runtime.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

/-- `Caller(skip)` returns some program counter, file name, line and `ok` (arbitrary: the model
does not know the stack or the binary's symbol tables, `TrustedCode/runtime.lean`); it cannot
panic. -/
abbrev runtime.Caller.spec : Prop :=
  ∀ (skip : w64),
    {{ (True : IProp GF) }}
      (App (Val (@! Caller)) (Val #skip))
    {{ (pc : w64) (file : GoString) (line : w64) (ok : Bool),
        RET (PairV (PairV (PairV #pc #file) #line) #ok); True }}

end spec

end Perennial
