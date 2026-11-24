/-
`github.com/mit-pdos/gokv/grove_ffi.GetTSC`'s spec.
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

/-- `GetTSC()`: the node's timestamp counter, at least any earlier reading, a logically atomic
spec. -/
abbrev github_com.mit_pdos.gokv.grove_ffi.GetTSC.spec : Prop :=
  ⊢ ∀ Φ : val → IProp GF,
      (|={⊤,∅}=> ∃ prev : Nat, tscLb prev ∗
        (∀ t : w64, ⌜prev ≤ t.toNat⌝ -∗ tscLb t.toNat ={∅,⊤}=∗ Φ #t)) -∗
      WP (App (Val (@! GetTSC)) (Val #())) {{ Φ }}

end spec

end Perennial
