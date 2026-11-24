/-
`time.sendTimes`'s spec.
-/
module

public import Perennial.Proof.time.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `sendTimes(c, seq, delta)`, for `c` (an `any`) holding a `chan Time` that is a bag of times
each carrying `Q`: sends one time, carrying the caller's `Q`. It calls `Now`, which reads the
package's globals (`isPkgInit`). -/
abbrev time.sendTimes.spec : Prop :=
  ∀ (ch : Loc) (γ : ChanNames) (Q : IProp GF) (seq delta : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.time ∗ isChanBag γ ch (V := time.Time) (fun _ => Q) ∗
        Q }}
      (App (App (App (Val (@! time.sendTimes))
        (Val #(interface.mkOk (go.GoType.ChannelType go.ChanDir.sendrecv time.Time.ty) #ch)))
        (Val #seq)) (Val #delta))
    {{ RET #(); True }}

end spec

end Perennial
