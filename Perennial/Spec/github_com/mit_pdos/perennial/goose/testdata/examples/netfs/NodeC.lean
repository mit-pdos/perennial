/-
`github.com/mit-pdos/perennial/goose/testdata/examples/netfs.NodeC`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std fs_ext net_ext

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.Assumptions]

/-- `NodeC()` at `"c"`: its junk follows the protocol, since it comes from `"c"`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeC.spec : Prop :=
  ∀ (c0 : GoString), netAddr (GF := GF) = go!"c" →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs ∗
        inv netN (netInv (gooseNetGS (GF := GF)) c0) }}
      (App (Val (@! NodeC)) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
