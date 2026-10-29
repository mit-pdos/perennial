/-
The proof of `(*Page).pageElementSize`: both element sizes are 16.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__pageElementSize

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.pageElementSize.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.pageElementSize.spec (GF := GF) (hG := hG) := by
  intro p hdr dq
  wp_start as ⟨Hp, %Hnn⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨Hid, Hflags, Hcount, Hoverflow, -⟩
  simp only [leafPageFlag, leafPageElementSize, branchPageElementSize]
  wp_auto
  wp_if_destruct <;> (try wp_auto) <;>
    (iapply HΦ; iapply typedPointsto_combine _ _ _ Hnn; simp only [TypedPointsto.typedPointstoDef];
     iframe)

end proof

end Perennial
