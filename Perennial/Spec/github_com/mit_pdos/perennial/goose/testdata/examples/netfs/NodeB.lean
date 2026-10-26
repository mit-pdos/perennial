/-
`github.com/mit-pdos/perennial/goose/testdata/examples/netfs.NodeB`'s spec.
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

/-- `NodeB()` at `"b"`, at every boot: under the protocol and the invariant of
its files, it sends only `c0`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeB.spec : Prop :=
  ∀ (c0 : GoString) (γ : GName), netAddr (GF := GF) = go!"b" →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs ∗
        inv netN (netInv (gooseNetGS (GF := GF)) c0) ∗
        inv outN (bInv (gooseFsGS (GF := GF)) c0 γ) }}
      (App (Val (@! NodeB)) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
