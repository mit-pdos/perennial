/-
Shared definitions of the proofs of the Go `math/bits` package: its `isPkgInit` (the table
`deBruijn64tab`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.math.bits
public import Perennial.GeneratedProof.math.bits
public import Perennial.Proof.«unsafe».Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace math.bits

/-- The table `deBruijn64tab` (`bits.go`): the index of the lowest set bit of `x`, at
`(x & -x) * deBruijn64 >> 58`. -/
def deBruijn64tabVal : GoArray w8 64 := array.mk 64
  [W8 0, W8 1, W8 56, W8 2, W8 57, W8 49, W8 28, W8 3,
   W8 61, W8 58, W8 42, W8 50, W8 38, W8 29, W8 17, W8 4,
   W8 62, W8 47, W8 59, W8 36, W8 45, W8 43, W8 51, W8 22,
   W8 53, W8 39, W8 33, W8 30, W8 24, W8 18, W8 12, W8 5,
   W8 63, W8 55, W8 48, W8 27, W8 60, W8 41, W8 37, W8 16,
   W8 46, W8 35, W8 44, W8 21, W8 52, W8 32, W8 23, W8 11,
   W8 54, W8 26, W8 40, W8 15, W8 34, W8 20, W8 31, W8 10,
   W8 25, W8 14, W8 19, W8 9, W8 13, W8 8, W8 7, W8 6]

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

/-- The package-initialized state (persistent: the package never writes its tables after
initialization): `deBruijn64tab` holds `deBruijn64tabVal`, which `TrailingZeros64` reads. -/
abbrev isInit : IProp GF :=
  iprop(typedPointsto (globalAddr deBruijn64tab) deBruijn64tabVal DFrac.discard)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.math.bits :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math.bits :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.math.bits ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.math.bits

end defs

end math.bits

end Perennial
