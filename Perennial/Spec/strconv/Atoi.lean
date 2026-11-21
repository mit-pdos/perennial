/-
`strconv.Atoi`'s spec.
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

/-- `strconv.Atoi(s)` returns, with a nil error or a fresh `*NumError{"Atoi", s, ErrSyntax}` or
`*NumError{"Atoi", s, ErrRange}` (`internal.strconv.Atoi.spec`: the number is not specified). -/
abbrev strconv.Atoi.spec : Prop :=
  ∀ (s : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (Val (@! Atoi)) (Val #s))
    {{ (x : w64) (err : GoInterface), RET (PairV #x #err);
        ⌜err = interface.nil⌝ ∨ strconv.numErrorOf err go!"Atoi" s strconv.ErrSyntax ∨
          strconv.numErrorOf err go!"Atoi" s strconv.ErrRange }}

end spec

end Perennial
