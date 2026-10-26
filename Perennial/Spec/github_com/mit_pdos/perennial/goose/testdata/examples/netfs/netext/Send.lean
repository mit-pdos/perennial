/-
`github.com/mit-pdos/perennial/goose/testdata/examples/netfs/netext.Send`'s spec.
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

/-- `Send(to, data)`: the message `(netAddr, data)` joins the messages of `to`, a
logically atomic spec; the data slice is only read. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Send.spec : Prop :=
  ∀ (to : GoString) (sl : GoSlice) (data : GoString) (dq : DFrac),
  ⊢ ∀ Φ : val → IProp GF, sl ↦*{dq} data -∗
      (|={⊤,∅}=> ∃ ms : GSet NetMsg, to n↦ ms ∗
        (to n↦ (ms ∪ {[⟨netAddr (GF := GF), data⟩]}) ={∅,⊤}=∗ (sl ↦*{dq} data -∗ Φ #()))) -∗
      WP (App (App (Val (@! Send)) (Val #to)) (Val #sl)) {{ Φ }}

end spec

end Perennial
