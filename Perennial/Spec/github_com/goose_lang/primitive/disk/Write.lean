/-
`github.com/goose-lang/primitive/disk.Write`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.primitive.disk.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE disk_ffi

section spec
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.primitive.disk.Assumptions]

/-- `Write(a, s)`: writes the block in `s` to disk address `a`. (The logically atomic
form is `wp_Write_atomic`, in `Results`.) -/
abbrev github_com.goose_lang.primitive.disk.Write.spec : Prop :=
  ∀ (a : w64) (s : GoSlice) (q : DFrac) (b : _root_.Perennial.Block),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        ∃ b0, uint.Z a d↦ b0 ∗ s ↦*{q} b.toList }}
      (App (App (Val (@! Write)) (Val #a)) (Val #s))
    {{ RET #(); uint.Z a d↦ b ∗ s ↦*{q} b.toList }}

end spec

end Perennial
