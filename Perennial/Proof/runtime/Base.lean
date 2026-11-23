/-
Shared definitions of the proofs of `runtime`: its `isPkgInit` (the variable `buildVersion`, which
`Version` returns, holds some string), and the spec of the trusted model of `buildVersion`'s
initialization (`Perennial/TrustedCode/runtime.lean`). `runtime`'s initializer is proved by its
clients (its other variable initializers are names-only here).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.runtime
public import Perennial.GeneratedProof.runtime
public import Perennial.Proof.internal.runtime.atomic.Base
public import Perennial.Proof.internal.runtime.sys.Base
public import Perennial.Proof.arbitraryString

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace runtime

section defns
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

/-- The package-initialized state (persistent: nothing writes `buildVersion` after the linker,
`TrustedCode/runtime.lean`): `buildVersion` holds some string, the build's version. -/
abbrev isInit : IProp GF :=
  iprop(∃ v : GoString, globalAddr buildVersion ↦□ v)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.runtime :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.runtime :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.runtime ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.runtime

end defns

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `buildVersion`'s initialization (the model) allocates the variable and stores some string;
`runtime`'s initializer runs it (its clients prove that initializer, and make the cell
persistent for `isInit`). -/
theorem wp_buildVersion_init :
    {{ (True : IProp GF) }} (App (Val buildVersion.init) (Val #()))
    {{ RET #(); ∃ v : GoString, globalAddr buildVersion ↦ v }} := by
  wp_start
  wp_apply wp_GlobalAlloc (V := GoString) go!"runtime.buildVersion" go.string as Hv
  wp_apply fmt.wp_arbitraryString as %s -
  iapply HΦ
  iexists _
  unfold buildVersion
  iexact Hv

end wps

end runtime

end Perennial
