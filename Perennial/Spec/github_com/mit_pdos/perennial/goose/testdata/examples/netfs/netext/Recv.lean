/-
`github.com/mit-pdos/perennial/goose/testdata/examples/netfs/netext.Recv`'s spec.
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

/-- `Recv()`: some message `m` sent to the node, as its sender and a new slice of
its data, a logically atomic spec. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Recv.spec : Prop :=
  ⊢ ∀ Φ : val → IProp GF, (|={⊤,∅}=> ∃ (q : DFrac) (ms : GSet NetMsg), netAddr (GF := GF) n↦{q} ms ∗
        ∀ m, ⌜m ∈ ms⌝ -∗ netAddr (GF := GF) n↦{q} ms ={∅,⊤}=∗
          ∀ sl : GoSlice, sl ↦* m.data -∗ ownSliceCap w8 sl (DFrac.own 1) -∗
            Φ (PairV (#m.sender) (#sl))) -∗
      WP (App (Val (@! Recv)) (Val #())) {{ Φ }}

end spec

end Perennial
