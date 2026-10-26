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

/-- `NodeB()` at `"b"`, which owns its file `"out"`: under the protocol, it
does not panic (the write is kept). -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeB.spec : Prop :=
  ∀ (c0 old : GoString), netAddr (GF := GF) = go!"b" →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs ∗
        inv netN (netInv (gooseNetGS (GF := GF)) c0) ∗ go!"out" fs↦ old }}
      (App (Val (@! NodeB)) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
