/-
`github.com/goose-lang/primitive/disk.Read`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.primitive.disk.Assumptions]

/-- `Read(a)`: returns a fresh slice holding the block at disk address `a`. (The logically
atomic form is `wp_Read_atomic`, in `Results`.) -/
abbrev github_com.goose_lang.primitive.disk.Read.spec : Prop :=
  ∀ (a : w64) (q : DFrac) (b : _root_.Perennial.Block),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        uint.Z a d↦{q} b }}
      (App (Val (@! Read)) (Val #a))
    {{ (s : GoSlice), RET #s; uint.Z a d↦{q} b ∗ isBlockFull s b }}

end spec

end Perennial
