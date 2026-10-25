/-
Results of `cmp` derived from the linked ones: the specs of `isNaN` and `Less` at
`uint64` under their old names.
-/
module

public import Perennial.Proof.cmp.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : cmp.Assumptions]

/-- `isNaN` on `uint64` is `false` (`cmp.wp_isNaN`'s first half). -/
theorem cmp.wp_isNaN_uint64 (x : w64) :
    {{ (True : IProp GF) }}
      (App (Val #(functions isNaN [go.uint64])) (Val #x))
    {{ RET #false; True }} :=
  cmp.wp_isNaN.1 x

/-- `isNaN` on `string` is `false` (`cmp.wp_isNaN`'s second half). -/
theorem cmp.wp_isNaN_string (x : GoString) :
    {{ (True : IProp GF) }}
      (App (Val #(functions isNaN [go.string])) (Val #x))
    {{ RET #false; True }} :=
  cmp.wp_isNaN.2 x

/-- `Less` on `uint64` is `<` on the unsigned values (`cmp.wp_Less`'s first half). -/
theorem cmp.wp_Less_uint64 (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions Less [go.uint64])) (Val #x)) (Val #y))
    {{ (b : Bool), RET #b; ⌜b = true ↔ uint.Z x < uint.Z y⌝ }} :=
  cmp.wp_Less.1 x y

/-- `Less` on `string` is Go's order on strings (`cmp.wp_Less`'s second half). -/
theorem cmp.wp_Less_string (x y : GoString) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions Less [go.string])) (Val #x)) (Val #y))
    {{ (b : Bool), RET #b; ⌜b = true ↔ go.GoStringLt x y⌝ }} :=
  cmp.wp_Less.2 x y

end results

end Perennial
