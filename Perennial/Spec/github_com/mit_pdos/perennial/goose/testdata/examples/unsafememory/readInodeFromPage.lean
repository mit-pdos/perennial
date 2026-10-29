/-
`readInodeFromPage`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `readInodeFromPage(p)` reads back the inodes laid out after the header of `p`; their keys and values alias the page. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.readInodeFromPage.spec : Prop :=
  ∀ (p : Loc) (hdr : Page) (ms : List InodeM) (tail : List w8),
    {{ (p ↦□ hdr ∗ bytesPointsto (p +ₗ 16) DFrac.discard (pageBody (pageIsLeaf hdr) ms ++ tail) ∗
        ⌜0 < p.addr ∧ hdr.count' = W16 (ms.length : Int) ∧ pageFits ms⌝ : IProp GF) }}
      (App (Val (@! readInodeFromPage)) (Val #p))
    {{ (s : GoSlice), RET #s; inodesOwn s (readBack (pageIsLeaf hdr) ms) }}

end spec

end Perennial
