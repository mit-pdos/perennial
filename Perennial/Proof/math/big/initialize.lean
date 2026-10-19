/-
The proof of `math/big.initialize'`, from the trust-boundary axiom `math.big.wp_opaque_inits`
on the package's untranslated variable initializers.
-/
module

public import Perennial.Spec.math.big.initialize
public import Perennial.Spec.fmt.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- `x ∈ [a, ..., x, ...]`, linear in the list. -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary: `math/big`'s untranslated variable initializers return.**
`math/big` is translated without its variables' initializers (`natOne`, `intOne`,
`pow5tab`, `hasADX`, the thresholds `karatsubaThreshold`, ..., the errors `errNoDigits`
and `errInvalSep`, and the interface checks `var _ fmt.Formatter = intOne`, ..., which all
share the one `«_».init`), so goose emits each as an axiomatized `X.init : val` with no
semantics; in Go they run at program start and return without panicking. The package's
`isPkgInit` is `True`, so nothing is assumed about what they store. Satisfiable: the
`X.init` are uninterpreted constants, and `fun _ => #()` meets the triple. -/
axiom math.big.wp_opaque_inits :
    ∀ v ∈ ([math.big._Accuracy_index.init,
        math.big.hasADX.init,
        math.big.pow5tab.init,
        math.big.«_».init,
        math.big.natOne.init,
        math.big.intOne.init,
        math.big.natTwo.init,
        math.big.natFive.init,
        math.big.natTen.init,
        math.big.errNoDigits.init,
        math.big.errInvalSep.init,
        math.big.leafSize.init,
        math.big.divRecursiveThreshold.init,
        math.big.karatsubaThreshold.init,
        math.big.basicSqrThreshold.init,
        math.big.karatsubaSqrThreshold.init,
        math.big._RoundingMode_index.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

variable [package_sem : math.big.Assumptions]

theorem math.big.initialize'.wp_proof
    (wp_fmt_initialize : fmt.initialize'.spec (GF := GF) (hG := hG)) :
    math.big.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_fmt_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hfmt⟩
  wp_apply (math.big.wp_opaque_inits math.big._Accuracy_index.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.hasADX.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.pow5tab.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.«_».init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.«_».init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.natOne.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.intOne.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.«_».init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.«_».init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.natTwo.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.natFive.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.natTen.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.errNoDigits.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.errInvalSep.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.leafSize.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.divRecursiveThreshold.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.karatsubaThreshold.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.basicSqrThreshold.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.karatsubaSqrThreshold.init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big.«_».init (by mem_tac))
  wp_apply (math.big.wp_opaque_inits math.big._RoundingMode_index.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
