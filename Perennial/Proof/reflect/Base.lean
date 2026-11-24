/-
Shared definitions of the proofs of the Go `reflect` package: its `isPkgInit` (the table
`kindNames`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.reflect
public import Perennial.GeneratedProof.reflect
public import Perennial.Proof.internal.gomodel.Base
public import Perennial.Proof.internal.reflectcore.Base
public import Perennial.Proof.iter.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.«unsafe».Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace reflect

/-- The table `kindNames` (`type.go`): the name of each `Kind`, by its number. -/
def kindNamesVal : List GoString :=
  [go!"invalid", go!"bool", go!"int", go!"int8", go!"int16", go!"int32", go!"int64", go!"uint",
   go!"uint8", go!"uint16", go!"uint32", go!"uint64", go!"uintptr", go!"float32", go!"float64",
   go!"complex64", go!"complex128", go!"array", go!"chan", go!"func", go!"interface", go!"map",
   go!"ptr", go!"slice", go!"string", go!"struct", go!"unsafe.Pointer"]

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

/-- The package-initialized state (persistent: the package never writes `kindNames` after
initialization): `kindNames` holds `kindNamesVal`, which `Kind.String` reads. -/
abbrev isInit : IProp GF :=
  iprop(∃ sl : GoSlice, globalAddr kindNames ↦□ sl ∗ sl ↦*□ kindNamesVal)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.reflect :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.reflect :=
  build_get_is_pkg_init_wf

omit package_sem in
theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.reflect ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.reflect

end defs

end reflect

end Perennial
