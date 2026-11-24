/-
Shared definitions of the proofs of the Go `crypto/fips140` package: its `isPkgInit` (`enabled`, which is `true` only if the `fips140` GODEBUG setting is `only`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.crypto.fips140
public import Perennial.GeneratedProof.crypto.fips140

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace crypto.fips140

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.fips140.Assumptions]

/-- The package-initialized state (persistent: nothing writes `enabled` after its initializer):
`enabled` holds `true` only if the run's `fips140` setting is `only` (`godebugFips140`,
`TrustedCode/crypto/fips140.lean`). -/
abbrev isInit : IProp GF :=
  iprop(∃ b : Bool, globalAddr enabled ↦□ b ∗ ⌜b = true → godebugFips140 = go!"only"⌝)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.crypto.fips140 :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.crypto.fips140 :=
  build_get_is_pkg_init_wf

end defs

end crypto.fips140

end Perennial

namespace Perennial.crypto.fips140
open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-- Under the environment premise, the mode is not `only`. -/
theorem godebugFips140_ne_only (H : GodebugFips140Off) : godebugFips140 ≠ go!"only" := by
  rcases H with h | h <;> rw [h] <;> decide

section access
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.fips140.Assumptions]

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.crypto.fips140 ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.crypto.fips140

end access
end Perennial.crypto.fips140
