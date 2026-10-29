/-
`writeLeaf`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `writeLeaf(buf, inodes)` lays a leaf page holding `ms` over the start of the zeroed `buf`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeLeaf.spec : Prop :=
  ∀ (buf s : GoSlice) (ms : List InodeM) (N : Nat),
    {{ (inodesOwn s ms ∗ bytesPointsto buf.ptr (DFrac.own 1) (List.replicate N 0) ∗
        ⌜buf.len = W64 (N : Int) ∧ N < 2 ^ 63 ∧ pageFits ms ∧ 16 + (pageBody true ms).length ≤ N⌝ :
        IProp GF) }}
      (App (App (Val (@! writeLeaf)) (Val #buf)) (Val #s))
    {{ RET #buf.ptr;
       bytesPointsto buf.ptr (DFrac.own 1) (encode (leafHeader ms) ++ pageBody true ms ++
         List.replicate (N - 16 - (pageBody true ms).length) 0) }}

end spec

end Perennial
