/-
`github.com/mit-pdos/perennial/goose/testdata/examples/netfs/netext.send`'s spec.
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

/-- `send(to, data)`: the message `(netAddr, data)` joins the messages of `to`, a
logically atomic spec (the network's points-to is needed only at the send, so
it can come from an invariant). -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.send.spec : Prop :=
  ∀ (to data : GoString),
  ⊢ ∀ Φ : val → IProp GF, (|={⊤,∅}=> ∃ ms : GSet NetMsg, to n↦ ms ∗
        (to n↦ (ms ∪ {[⟨netAddr (GF := GF), data⟩]}) ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! send)) (Val #to)) (Val #data)) {{ Φ }}

end spec

end Perennial
