/-
Shared definitions of the proofs of the Go `unicode/utf8` package: its `isPkgInit` (the tables
`first` and `acceptRanges`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.unicode.utf8
public import Perennial.GeneratedProof.unicode.utf8

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace unicode.utf8

/-- The table `first` (`utf8.go`): for each first byte of a UTF-8 sequence, its size in the low
bits and the index of its `acceptRanges` entry in the high bits (`xx` invalid, `as` ASCII). -/
def firstVal : GoArray w8 256 := array.mk 256
  [W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240, W8 240,
   W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241,
   W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241,
   W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241,
   W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241,
   W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241,
   W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241,
   W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241,
   W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241,
   W8 241, W8 241, W8 2, W8 2, W8 2, W8 2, W8 2, W8 2,
   W8 2, W8 2, W8 2, W8 2, W8 2, W8 2, W8 2, W8 2,
   W8 2, W8 2, W8 2, W8 2, W8 2, W8 2, W8 2, W8 2,
   W8 2, W8 2, W8 2, W8 2, W8 2, W8 2, W8 2, W8 2,
   W8 19, W8 3, W8 3, W8 3, W8 3, W8 3, W8 3, W8 3,
   W8 3, W8 3, W8 3, W8 3, W8 3, W8 35, W8 3, W8 3,
   W8 52, W8 4, W8 4, W8 4, W8 68, W8 241, W8 241, W8 241,
   W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241, W8 241]

section defs
variable [GooseExts]

/-- The table `acceptRanges` (`utf8.go`): the range of valid second bytes of a UTF-8 sequence,
by the index in the high bits of its `first` entry (the entries from 5 on are zero). -/
def acceptRangesVal : GoArray acceptRange 16 := array.mk 16
  [acceptRange.mk (W8 128) (W8 191),
   acceptRange.mk (W8 160) (W8 191),
   acceptRange.mk (W8 128) (W8 159),
   acceptRange.mk (W8 144) (W8 191),
   acceptRange.mk (W8 128) (W8 143),
   acceptRange.mk (W8 0) (W8 0),
   acceptRange.mk (W8 0) (W8 0),
   acceptRange.mk (W8 0) (W8 0),
   acceptRange.mk (W8 0) (W8 0),
   acceptRange.mk (W8 0) (W8 0),
   acceptRange.mk (W8 0) (W8 0),
   acceptRange.mk (W8 0) (W8 0),
   acceptRange.mk (W8 0) (W8 0),
   acceptRange.mk (W8 0) (W8 0),
   acceptRange.mk (W8 0) (W8 0),
   acceptRange.mk (W8 0) (W8 0)]

end defs

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : unicode.utf8.Assumptions]

/-- The package-initialized state (persistent: the package never writes its tables after
initialization): `first` holds `firstVal` and `acceptRanges` holds `acceptRangesVal`. -/
abbrev isInit : IProp GF :=
  iprop(typedPointsto (globalAddr first) firstVal DFrac.discard ∗
    typedPointsto (globalAddr acceptRanges) acceptRangesVal DFrac.discard)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.unicode.utf8 :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.unicode.utf8 :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.unicode.utf8

end init

end unicode.utf8

end Perennial
