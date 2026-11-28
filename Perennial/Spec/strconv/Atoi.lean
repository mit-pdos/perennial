/-
`strconv.Atoi`'s spec.
-/
module

public import Perennial.Proof.strconv.Base
public import Perennial.Proof.internal.strconv.AtoiBasics

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

/-- `strconv.Atoi(s)` returns what `internal.strconv.Atoi.spec` says (`parseInt s 10 0`): the number
`s` denotes and a nil error; else `0` and a fresh `*NumError{"Atoi", s, ErrSyntax}`, or the bound of
the `int64` range it exceeds and a fresh `*NumError{"Atoi", s, ErrRange}`. So
`Atoi(FormatInt(m, 10))` is `m` and a nil error (`internal.strconv.parseInt_fmtInt10_0`). -/
abbrev strconv.Atoi.spec : Prop :=
  ∀ (s : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (Val (@! Atoi)) (Val #s))
    {{ (x : w64) (err : GoInterface), RET (PairV #x #err);
        match internal.strconv.parseInt s 10 0 with
        | .ok n => ⌜x = W64 n ∧ err = interface.nil⌝
        | .errSyntax => ⌜x = W64 0⌝ ∗ strconv.numErrorOf err go!"Atoi" s strconv.ErrSyntax
        | .errRange n => ⌜x = W64 n⌝ ∗ strconv.numErrorOf err go!"Atoi" s strconv.ErrRange }}

end spec

end Perennial
