/-
The proof of `testByteSliceToString` (a goose semantics test, `conversions.go`).
The `[]byte -> string` conversion is handled with `wp_bytes_to_string`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testByteSliceToString
public import Perennial.Golang.Theory.String

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testByteSliceToString.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testByteSliceToString.spec (GF := GF) (hG := hG) := by
  semantics_auto
  simp only [sliceIndexRef]
  icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ _ (zero_val w8) (by decide) rfl $$ p with ⟨Hp0, p⟩
  steps
  ihave p := p $$ Hp0
  simp only [sliceIndexRef]
  icases array_acc (GF := GF) _ (sint.Z (W64 1)) _ _ _ (zero_val w8) (by decide) rfl $$ p with ⟨Hp1, p⟩
  steps
  ihave p := p $$ Hp1
  simp only [sliceIndexRef]
  icases array_acc (GF := GF) _ (sint.Z (W64 2)) _ _ _ (zero_val w8) (by decide) rfl $$ p with ⟨Hp2, p⟩
  steps
  ihave p := p $$ Hp2
  simp only [show (sint.Z (W64 0)).toNat = 0 from rfl, show (sint.Z (W64 1)).toNat = 1 from rfl,
    show (sint.Z (W64 2)).toNat = 2 from rfl,
    show (zero_val (GoArray w8 (sint.Z (W64 3)))).arr = [W8 0, W8 0, W8 0] from rfl,
    List.set_cons_zero, List.set_cons_succ]
  ihave Hsl := slice_array (GF := GF) p_ptr _ _ (by decide) $$ p
  rw [show W64 (sint.Z (W64 3)) = W64 3 from rfl]
  wp_apply wp_bytes_to_string (slice.mk p_ptr (W64 3) (W64 3)) [W8 65, W8 66, W8 67] $$ Hsl
  iintro _
  steps
  iexact HΦ

end proof

end Perennial
