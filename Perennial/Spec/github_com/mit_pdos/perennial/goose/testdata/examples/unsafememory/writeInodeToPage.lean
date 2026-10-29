/-
`writeInodeToPage`'s spec (`goose/testdata/examples/unsafememory`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Pages

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Assumptions]

/-- `writeInodeToPage(inodes, p)` lays `ms` out after the header of `p` (over zeros), as a leaf or a branch page as `p`'s flags say. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInodeToPage.spec : Prop :=
  ∀ (s : GoSlice) (ms : List InodeM) (p : Loc) (hdr : Page) (R : Nat),
    {{ (inodesOwn s ms ∗ p ↦ hdr ∗ bytesPointsto (p +ₗ 16) (DFrac.own 1) (List.replicate R 0) ∗
        ⌜0 < p.addr ∧ pageFits ms ∧ (pageBody true ms).length ≤ R⌝ : IProp GF) }}
      (App (App (Val (@! writeInodeToPage)) (Val #s)) (Val #p))
    {{ (w : w32), RET #w; p ↦ hdr ∗
        bytesPointsto (p +ₗ 16) (DFrac.own 1)
          (pageBody (pageIsLeaf hdr) ms ++ List.replicate (R - (pageBody true ms).length) 0) }}

end spec

end Perennial
