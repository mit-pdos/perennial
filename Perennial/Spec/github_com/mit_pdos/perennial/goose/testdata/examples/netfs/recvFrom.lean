/-
`github.com/mit-pdos/perennial/goose/testdata/examples/netfs.recvFrom`'s spec.
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

/-- `recvFrom(peer)` at `"a"` or `"b"`, from a `peer` other than `"c"`: under the
protocol, the data received is `c0`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.netfs.recvFrom.spec : Prop :=
  ∀ (c0 peer : GoString), peer ≠ go!"c" →
    (netAddr (GF := GF) = go!"a" ∨ netAddr (GF := GF) = go!"b") →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs ∗
        inv netN (netInv (gooseNetGS (GF := GF)) c0) }}
      (App (Val (@! recvFrom)) (Val #peer))
    {{ (sl : GoSlice), RET #sl; sl ↦* c0 }}

end spec

end Perennial
