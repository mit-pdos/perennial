module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

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
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : go.StringSemantics]

/-- `DecodeRune(s, k)`, the step of a range loop over `s` at byte `k`, returns the rune
there and the index after it (`go.decodeRune`). -/
abbrev github_com.mit_pdos.perennial.goose.model.strings.DecodeRune.spec : Prop :=
  ∀ {s : Stuckness} {E : CoPset} (str : GoString) (k : w64),
    0 ≤ sint.Z k → sint.nat k < str.length →
    {{ (True : IProp GF) }}
      (App (App (Val (@! DecodeRune)) (Val #str)) (Val #k)) @ s; E
    {{ RET (PairV #(go.decodeRune str (sint.nat k)).1
        #(W64 (go.decodeRune str (sint.nat k)).2)); True }}

end spec

end Perennial
