/-
`internal.strconv.ParseBool`'s spec.
-/
module

public import Perennial.Proof.internal.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

/-- `ParseBool(str)`: the boolean `str` spells (`parseBool`) and a nil error, or `false` and
`ErrSyntax`. -/
abbrev internal.strconv.ParseBool.spec : Prop :=
  ∀ (str : GoString),
    {{ (True : IProp GF) }}
      (App (Val (@! ParseBool)) (Val #str))
    {{ (b : Bool) (err : GoInterface), RET (PairV #b #err);
        ⌜match internal.strconv.parseBool str with
        | some b' => b = b' ∧ err = interface.nil
        | none => b = false ∧ err = interface.mkOk internal.strconv.Error.ty #(W64 2)⌝ }}

end spec

end Perennial
