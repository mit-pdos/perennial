/-
`strconv.ParseInt`'s spec.
-/
module

public import Perennial.Proof.strconv.Base
public import Perennial.Proof.internal.strconv.FormatBasics

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

/-- `strconv.ParseInt(s, base, bitSize)` in a base between 2 and 36 and a bit size between 0 and
64 (0 meaning 64): what `internal.strconv.parseInt` says. The number `s` denotes after an optional
sign and a nil error; else `0` and a fresh `*NumError{"ParseInt", s, ErrSyntax}` (`s` empty or not
a number), or the bound of the signed range it exceeds and a `*NumError{"ParseInt", s, ErrRange}`.
(`internal.strconv.parseInt_fmtInt10`: it reads back what `FormatInt(m, 10)` writes.) -/
abbrev strconv.ParseInt.spec : Prop :=
  ∀ (s : GoString) (base bitSize : w64),
    2 ≤ sint.Z base → sint.Z base ≤ 36 → 0 ≤ sint.Z bitSize → sint.Z bitSize ≤ 64 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (App (App (Val (@! ParseInt)) (Val #s)) (Val #base)) (Val #bitSize))
    {{ (x : w64) (err : GoInterface), RET (PairV #x #err);
        match internal.strconv.parseInt s (sint.nat base) (sint.nat bitSize) with
        | .ok n => ⌜x = W64 n ∧ err = interface.nil⌝
        | .errSyntax => ⌜x = W64 0⌝ ∗ strconv.numErrorOf err go!"ParseInt" s strconv.ErrSyntax
        | .errRange n => ⌜x = W64 n⌝ ∗ strconv.numErrorOf err go!"ParseInt" s strconv.ErrRange }}

end spec

end Perennial
