/-
`internal.strconv.Atoi`'s spec.
-/
module

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
variable [package_sem : internal.strconv.Assumptions]

/-- `Atoi(s)` returns what `ParseInt(s, 10, 0)` does (`parseInt s 10 0`, which its slow path calls
and its fast path, for 1 to 18 bytes, computes): the number `s` denotes, after an optional sign, and
a nil error; else `0` and `ErrSyntax` (`s` empty or not a decimal number), or the bound of the
`int64` range it exceeds and `ErrRange` (each error an `internal/strconv.Error` converted to
`error`). So `Atoi` reads back what `FormatInt(m, 10)` writes (`parseInt_fmtInt10_0`). -/
abbrev internal.strconv.Atoi.spec : Prop :=
  ∀ (s : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.strconv }}
      (App (Val (@! Atoi)) (Val #s))
    {{ (x : w64) (err : GoInterface), RET (PairV #x #err);
        ⌜match internal.strconv.parseInt s 10 0 with
         | .ok n => x = W64 n ∧ err = interface.nil
         | .errSyntax => x = W64 0 ∧ err = interface.mkOk internal.strconv.Error.ty #(W64 2)
         | .errRange n => x = W64 n ∧ err = interface.mkOk internal.strconv.Error.ty #(W64 1)⌝ }}

end spec

end Perennial
