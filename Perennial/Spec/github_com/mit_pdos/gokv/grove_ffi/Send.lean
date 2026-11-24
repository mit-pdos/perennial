/-
`github.com/mit-pdos/gokv/grove_ffi.Send`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.gokv.grove_ffi.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std grove_ext

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt groveExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.gokv.grove_ffi.Assumptions]

/-- `Send(c, data)`: the message `(c_l, data)` joins the messages of the remote endpoint
`c_r`, a logically atomic spec; the data slice is only read. The returned error flag is
arbitrary (the message is sent either way). -/
abbrev github_com.mit_pdos.gokv.grove_ffi.Send.spec : Prop :=
  ∀ (c : Loc) (c_l c_r : Endpoint) (s : GoSlice) (data : List w8) (dq : DFrac),
  ⊢ ∀ Φ : val → IProp GF, isConnection c c_l c_r -∗ s ↦*{dq} data -∗
      (|={⊤,∅}=> ∃ ms : GSet message, c_r c↦ ms ∗
        (c_r c↦ (ms ∪ {[Message c_l data]}) ={∅,⊤}=∗
          ∀ err : Bool, s ↦*{dq} data -∗ Φ #err)) -∗
      WP (App (App (Val (@! Send)) (Val #c)) (Val #s)) {{ Φ }}

end spec

end Perennial
