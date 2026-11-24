/-
`sync.runtime_notifyListNotifyAll`'s spec.
-/
module

public import Perennial.Proof.sync.CondDefs

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
variable [package_sem : sync.Assumptions]

abbrev sync.runtime_notifyListNotifyAll.spec : Prop :=
  ∀ (l : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isNotifyList (GF := GF) l }}
      (App (Val (@! runtime_notifyListNotifyAll)) (Val #l))
    {{ RET #(); True }}

end spec

end Perennial
