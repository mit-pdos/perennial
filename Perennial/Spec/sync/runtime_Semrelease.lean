/-
`sync.runtime_Semrelease`'s spec.
-/
module

public import Perennial.Proof.sync.SemaDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

abbrev sync.runtime_Semrelease.spec : Prop :=
  ∀ (sema : Loc) (γ : GName) (N : Namespace) (_u1 : Bool) (_u2 : w64),
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isSema sema γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ v, ownSema γ v ∗
        (ownSema γ (v + W32 1) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (App (App (Val (@! runtime_Semrelease)) (Val #sema)) (Val #_u1)) (Val #_u2)) {{ Φ }}

end spec

end Perennial
