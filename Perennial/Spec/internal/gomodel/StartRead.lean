/-
`internal.gomodel.StartRead`'s spec.
-/
module

public import Perennial.Proof.internal.gomodel.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.gomodel.Assumptions]

/-- `gomodel.StartRead[T](p)`, at a cell `p` that is read-only already (a persistent
points-to): it leaves a reader on it, and returns. It reads no package variable, so it needs
no initialized package. -/
abbrev internal.gomodel.StartRead.spec : Prop :=
  ∀ (T : go.GoType) {V : Type} (l : Loc) (x : V),
    {{ (heapPointsto l DFrac.discard #x : IProp GF) }}
      (App (Val #(functions internal.gomodel.StartRead [T])) (Val #l))
    {{ RET #(); True }}

end spec

end Perennial
