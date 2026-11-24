/-
`github.com/mit-pdos/gokv/grove_ffi.Receive`'s spec.
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

/-- `Receive(c)`: either an error (`Err` set, `Data` nil) or a new slice holding the data of
some message from `c_r` sent to `c_l`, a logically atomic spec. -/
abbrev github_com.mit_pdos.gokv.grove_ffi.Receive.spec : Prop :=
  ∀ (c : Loc) (c_l c_r : Endpoint),
  ⊢ ∀ Φ : val → IProp GF, isConnection c c_l c_r -∗
      (|={⊤,∅}=> ∃ ms : GSet message, c_l c↦ ms ∗
        (c_l c↦ ms ={∅,⊤}=∗ ∀ (err : Bool) (s : GoSlice),
          (if err then ⌜s = slice.nil⌝ else
            ∃ data : List w8, ⌜Message c_r data ∈ ms⌝ ∗ s ↦* data ∗
              ownSliceCap w8 s (DFrac.own 1)) -∗
          Φ #(ReceiveRet.mk err s))) -∗
      WP (App (Val (@! Receive)) (Val #c)) {{ Φ }}

end spec

end Perennial
