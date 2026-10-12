/-
`elimination_stack.(*EliminationStack).Push`'s spec.
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

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.EliminationStack.Push.spec : Prop :=
  ∀ (v : GoString) (γ : EliminationStackNames) (s : Loc) (N : Namespace),
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg ∗ isEliminationStack s γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ σ, ownEliminationStack γ σ ∗
        (ownEliminationStack γ (v :: σ) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (s @!! go.GoType.PointerType EliminationStack.ty @!! go!"Push")) (Val #v)) {{ Φ }}

end spec

end Perennial
