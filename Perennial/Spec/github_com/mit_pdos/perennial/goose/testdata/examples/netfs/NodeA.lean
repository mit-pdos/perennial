/-
`github.com/mit-pdos/perennial/goose/testdata/examples/netfs.NodeA`'s spec.
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

/-- `NodeA()` at `"a"`, whose file `"in"` holds `c0` for good: under the
protocol, it does not panic (the round trip returns `c0`). -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeA.spec : Prop :=
  ∀ (c0 : GoString), netAddr (GF := GF) = go!"a" →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs ∗
        inv netN (netInv (gooseNetGS (GF := GF)) c0) ∗ go!"in" fs↦□ c0 }}
      (App (Val (@! NodeA)) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
