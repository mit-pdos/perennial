/-
`github.com/mit-pdos/gokv/grove_ffi.GetTimeRange`'s spec.
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

/-- `GetTimeRange()`: bounds `(l, h)` on the global time `t` at some point during the call,
at which the caller may use `ownTime t`. -/
abbrev github_com.mit_pdos.gokv.grove_ffi.GetTimeRange.spec : Prop :=
  ⊢ ∀ Φ : val → IProp GF,
      (∀ (l h t : w64), ⌜t.toNat ≤ h.toNat⌝ -∗ ⌜l.toNat ≤ t.toNat⌝ -∗
        ownTime t ={⊤}=∗ ownTime t ∗ Φ (PairV (#l) (#h))) -∗
      WP (App (Val (@! GetTimeRange)) (Val #())) {{ Φ }}

end spec

end Perennial
