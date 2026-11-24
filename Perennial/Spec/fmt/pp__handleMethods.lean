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
(`MethodArg`), without flags, `verb` one of `s v x`: calls `m`, which returns some `s` with
`P s`, appends `s` (`s`, `v`) or its hexadecimal (`x`), and returns `true`. -/
abbrev fmt.pp.handleMethods.spec : Prop :=
  ∀ (p : Loc) (x : GoInterface) (ii : GoInterfaceOk) (m : GoString) (P : GoString → Prop)
    (bs : GoString) (wid prec : w64) (verb : w8),
    x = interface.ok ii → MethodArg ii m → (verb = verb_s ∨ verb = verb_v ∨ verb = verb_x) →
    {{ isPrinterA (GF := GF) p x bs noFlags wid prec ∗ methodSpec ii m P }}
      (App (Val (p @!! go.GoType.PointerType pp.ty @!! go!"handleMethods")) (Val #(W32 (uint.nat verb))))
    {{ RET #true; ∃ s : GoString, ⌜P s⌝ ∗
        isPrinterA p x (bs ++ if verb = verb_x then bytesHex false s else s) noFlags wid prec }}

end spec

end Perennial
