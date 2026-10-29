/-
The proof of `testMixedWidthAtomics`: a `uint32` atomic add on the low half of a `uint64`
(integers are little-endian).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testMixedWidthAtomics
public import Perennial.Golang.Theory.Bytes

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testMixedWidthAtomics.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testMixedWidthAtomics.spec
      (GF := GF) (hG := hG) := by
  unsafememory_auto
  wp_bind (AddBytes _ _ _)
  wp_apply_core wp_add_bytes_typed _ _ u_ptr _ (W64 1) $$ u
  iintro u
  wp_auto
  -- the `uint32` view: the low 4 bytes of `u`
  icases (typedPointsto_w64_split u_ptr _ _).1 $$ u with ⟨u, uhi⟩
  rw [show (zero_val w64 + W64 1).setWidth 32 = W32 1 by decide,
    show (zero_val w64 + W64 1).toNat / 2 ^ 32 = (W64 2).toNat / 2 ^ 32 by decide]
  unsafememory_steps
  wp_bind (AddBytes _ _ _)
  wp_apply_core wp_add_bytes_typed _ _ u_ptr _ (W32 1) $$ u
  iintro u
  rw [show W32 1 + W32 1 = (W64 2).setWidth 32 by decide]
  ihave u := (typedPointsto_w64_split u_ptr _ _).2 $$ [u uhi]
  · iframe
  unsafememory_steps
  iexact HΦ

end proof

end Perennial
