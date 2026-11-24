/-
`fmt.(*pp).handleMethods`'s spec.
-/
module

public import Perennial.Proof.fmt.PrintDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- `p.handleMethods(verb)` of the argument `x` in `p.arg`, which Go formats by its method `m`
(`MethodArg`), without flags, `verb` one of `s v x q`: calls `m`, which returns some `s` with
`P s`, appends what `fmtString` writes for it (`StrOut`), and returns `true`. -/
abbrev fmt.pp.handleMethods.spec : Prop :=
  ∀ (p : Loc) (x : GoInterface) (ii : GoInterfaceOk) (m : GoString) (P : GoString → Prop)
    (bs : GoString) (wid prec : w64) (verb : w8),
    x = interface.ok ii → MethodArg ii m →
    (verb = verb_s ∨ verb = verb_v ∨ verb = verb_x ∨ verb = verb_q) →
    (verb = verb_x → ∀ s, P s → s.length < 2 ^ 62) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ isPrinterA (GF := GF) p x bs noFlags wid prec ∗
        methodSpec ii m P }}
      (App (Val (p @!! go.GoType.PointerType pp.ty @!! go!"handleMethods")) (Val #(W32 (uint.nat verb))))
    {{ RET #true; ∃ s o : GoString, ⌜P s ∧ StrOut verb s o⌝ ∗
        isPrinterA p x (bs ++ o) noFlags wid prec }}

end spec

end Perennial
