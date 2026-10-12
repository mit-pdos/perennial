/-
`elimination_stack.(*LockedStack).Push`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.LockedStack.Push.spec : Prop :=
  ∀ (v : GoString) (γ : GName) (s : Loc),
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg ∗ isLockedStack s γ) -∗
      (|={⊤,∅}=> ∃ σ, ownLockedStack γ σ ∗ (ownLockedStack γ (v :: σ) ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (s @!! go.GoType.PointerType LockedStack.ty @!! go!"Push")) (Val #v)) {{ Φ }}

end spec

end Perennial
