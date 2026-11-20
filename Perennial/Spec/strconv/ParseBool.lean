/-
`strconv.ParseBool`'s spec.
-/
module

public import Perennial.Proof.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

/-- `strconv.ParseBool(str)`: the boolean `str` spells (`internal.strconv.parseBool`) and a nil
error; else `false` and a fresh `*NumError{"ParseBool", str, ErrSyntax}`. -/
abbrev strconv.ParseBool.spec : Prop :=
  ∀ (str : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (Val (@! ParseBool)) (Val #str))
    {{ (b : Bool) (err : GoInterface), RET (PairV #b #err);
        match internal.strconv.parseBool str with
        | some b' => ⌜b = b' ∧ err = interface.nil⌝
        | none => ⌜b = false⌝ ∗ strconv.numErrorOf err go!"ParseBool" str strconv.ErrSyntax }}

end spec

end Perennial
