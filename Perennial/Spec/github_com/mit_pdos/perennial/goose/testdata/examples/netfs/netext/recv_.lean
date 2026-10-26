/-
`github.com/mit-pdos/perennial/goose/testdata/examples/netfs/netext.recv`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std net_ext

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Assumptions]

/-- `recv()`: some message `m` sent to the node, as `(m.sender, m.data)`, a
logically atomic spec. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.recv.spec : Prop :=
  ⊢ ∀ Φ : val → IProp GF, (|={⊤,∅}=> ∃ (q : DFrac) (ms : GSet NetMsg), netAddr (GF := GF) n↦{q} ms ∗
        ∀ m, ⌜m ∈ ms⌝ -∗ netAddr (GF := GF) n↦{q} ms ={∅,⊤}=∗ Φ (PairV (#m.sender) (#m.data))) -∗
      WP (App (Val (@! recv)) (Val #())) {{ Φ }}

end spec

end Perennial
