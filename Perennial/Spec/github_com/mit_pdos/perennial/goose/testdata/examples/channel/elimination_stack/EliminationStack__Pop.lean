/-
`elimination_stack.(*EliminationStack).Pop`'s spec.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.EliminationStack.Pop.spec : Prop :=
  ∀ (γ : EliminationStackNames) (s : Loc) (N : Namespace),
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg ∗ isEliminationStack s γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ σ, ownEliminationStack γ σ ∗
        (match σ with
         | [] => ownEliminationStack γ [] ={∅,⊤ \ ↑N}=∗ Φ (PairV #(go!"") #false)
         | v :: σ => ownEliminationStack γ σ ={∅,⊤ \ ↑N}=∗ Φ (PairV #v #true))) -∗
      WP (App (Val (s @!! go.GoType.PointerType EliminationStack.ty @!! go!"Pop")) (Val #())) {{ Φ }}

end spec

end Perennial
