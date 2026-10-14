/-
`errors.asType`'s spec.
-/
module

public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- Spec of the recursive helper `asType(err, ppe)`. `ppe` points to the
lazily allocated `*E` target passed to `As` methods. (New in Lean.) -/
abbrev errors.asType.spec : Prop :=
  ∀ (S : GoError → Prop) (err : GoError) (ppe pe : Loc)
    {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {T : go.GoType} [IntoValTyped (GF := GF) T' T],
    {{ "#Htree" ∷ isErrorTree (GF := GF) S T' T ∗ "%HS" ∷ ⌜S err⌝ ∗
        "Hppe" ∷ ppe ↦ pe ∗
        "Hpe" ∷ (⌜pe = Loc.null⌝ ∨ ∃ v : T', pe ↦ v) }}
      (App (App (Val #(functions asType [T])) (Val #err)) (Val #ppe))
    {{ (e : T') (found : Bool) (pe' : Loc), RET (PairV #e #found);
        ppe ↦ pe' ∗ (⌜pe' = Loc.null⌝ ∨ ∃ v : T', pe' ↦ v) }}

end spec

end Perennial
