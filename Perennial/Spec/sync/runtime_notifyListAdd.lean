/-
`sync.runtime_notifyListAdd`'s spec.
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

abbrev sync.runtime_notifyListAdd.spec : Prop :=
  ∀ (l : Loc) (l_v : notifyList) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ typedPointsto (GF := GF) l l_v dq }}
      (App (Val (@! runtime_notifyListAdd)) (Val #l))
    {{ (x : w32), RET #x; typedPointsto (GF := GF) l l_v dq }}

end spec

end Perennial
