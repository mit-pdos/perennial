/-
The proof of `math.initialize'`, from the trust-boundary axiom `math.wp_opaque_inits` on the
package's untranslated variable initializers.
-/
module

public import Perennial.Spec.math.initialize

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

/-- **Trust boundary: `math`'s untranslated variable initializers return.** `math.toml`
translates only a few constants, so the initializers of the package's variables (`useFMA`, a
CPU feature test, and the coefficient tables `_gamP`, `p0R8`, ..., `pow10tab`, `_sin`,
`mPi4`, ...) are each emitted as an axiomatized `X.init : val` with no semantics; in Go they
run at program start and return without panicking. The package's `isPkgInit` is `True`, so
nothing is assumed about what they store. Satisfiable: the `X.init` are uninterpreted
constants, and `fun _ => #()` meets the triple. -/
axiom math.wp_opaque_inits :
    ∀ v ∈ ([math.useFMA.init,
        math._gamP.init,
        math._gamQ.init,
        math._gamS.init,
        math.p0R8.init,
        math.p0S8.init,
        math.p0R5.init,
        math.p0S5.init,
        math.p0R3.init,
        math.p0S3.init,
        math.p0R2.init,
        math.p0S2.init,
        math.q0R8.init,
        math.q0S8.init,
        math.q0R5.init,
        math.q0S5.init,
        math.q0R3.init,
        math.q0S3.init,
        math.q0R2.init,
        math.q0S2.init,
        math.p1R8.init,
        math.p1S8.init,
        math.p1R5.init,
        math.p1S5.init,
        math.p1R3.init,
        math.p1S3.init,
        math.p1R2.init,
        math.p1S2.init,
        math.q1R8.init,
        math.q1S8.init,
        math.q1R5.init,
        math.q1S5.init,
        math.q1R3.init,
        math.q1S3.init,
        math.q1R2.init,
        math.q1S2.init,
        math._lgamA.init,
        math._lgamR.init,
        math._lgamS.init,
        math._lgamT.init,
        math._lgamU.init,
        math._lgamV.init,
        math._lgamW.init,
        math.pow10tab.init,
        math.pow10postab32.init,
        math.pow10negtab32.init,
        math._sin.init,
        math._cos.init,
        math._tanP.init,
        math._tanQ.init,
        math.tanhP.init,
        math.tanhQ.init,
        math.mPi4.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

variable [package_sem : math.Assumptions]

theorem math.initialize'.wp_proof :
    math.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (math.wp_opaque_inits math.useFMA.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._gamP.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._gamQ.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._gamS.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p0R8.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p0S8.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p0R5.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p0S5.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p0R3.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p0S3.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p0R2.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p0S2.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q0R8.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q0S8.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q0R5.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q0S5.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q0R3.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q0S3.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q0R2.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q0S2.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p1R8.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p1S8.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p1R5.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p1S5.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p1R3.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p1S3.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p1R2.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.p1S2.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q1R8.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q1S8.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q1R5.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q1S5.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q1R3.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q1S3.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q1R2.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.q1S2.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._lgamA.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._lgamR.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._lgamS.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._lgamT.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._lgamU.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._lgamV.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._lgamW.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.pow10tab.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.pow10postab32.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.pow10negtab32.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._sin.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._cos.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._tanP.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math._tanQ.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.tanhP.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.tanhQ.init (by mem_tac))
  wp_apply (math.wp_opaque_inits math.mPi4.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
