/-
`searchLeaf`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `searchLeaf(p, key)` is the number of keys of the leaf page `p` less than `key`, when the keys less than `key` are the first `r`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.searchLeaf.spec : Prop :=
  ∀ (p : Loc) (hdr : Page) (ms : List InodeM) (tail : List w8) (key : GoSlice) (k : List w8)
      (dk : DFrac) (r : Nat),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory ∗ p ↦□ hdr ∗
        bytesPointsto (p +ₗ 16) DFrac.discard (pageBody true ms ++ tail) ∗ key ↦*{dk} k ∗
        ⌜0 < p.addr ∧ hdr.count' = W16 (ms.length : Int) ∧ pageFits ms ∧ r ≤ ms.length ∧
          ∀ (i : Nat) (h : i < ms.length), (go.GoStringLt ms[i].key k ↔ i < r)⌝ }}
      (App (App (Val (@! searchLeaf)) (Val #p)) (Val #key))
    {{ RET #(W64 (r : Int)); key ↦*{dk} k }}

end spec

end Perennial
