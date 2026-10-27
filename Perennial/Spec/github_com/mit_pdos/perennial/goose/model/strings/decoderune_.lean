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

/-- `decoderune(s, k)` decodes the rune at byte `k` of `s` (`go.decodeMulti`) and returns
it with the index after it. -/
abbrev github_com.mit_pdos.perennial.goose.model.strings.decoderune.spec : Prop :=
  ∀ {s : Stuckness} {E : CoPset} (str : GoString) (k : w64),
    0 ≤ sint.Z k → sint.nat k < str.length →
    {{ (True : IProp GF) }}
      (App (App (Val (@! decoderune)) (Val #str)) (Val #k)) @ s; E
    {{ RET (PairV #(go.decodeMulti (str.drop (sint.nat k))).1
        #(k + W64 (go.decodeMulti (str.drop (sint.nat k))).2)); True }}

end spec

end Perennial
