/-
The proof of `crypto/ed25519.initialize'`, from the trust-boundary axiom
`crypto.ed25519.wp_cryptocustomrand_init` on the package's one untranslated variable
initializer.
-/
module

public import Perennial.Spec.crypto.ed25519.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary: `crypto/ed25519`'s untranslated variable initializer returns.**
`var cryptocustomrand = godebug.New("cryptocustomrand")` is not translated (`internal/godebug`
is not), so goose emits an axiomatized `cryptocustomrand.init : val` with no semantics; in Go
it runs at program start and returns without panicking. The package's `isPkgInit` is `True`,
so nothing is assumed about what it stores. Satisfiable: `cryptocustomrand.init` is an
uninterpreted constant, and `fun _ => #()` meets the triple. -/
axiom crypto.ed25519.wp_cryptocustomrand_init :
    {{ (True : IProp GF) }}
      (App (Val crypto.ed25519.cryptocustomrand.init) (Val #()))
    {{ RET #(); True }}

variable [package_sem : crypto.ed25519.Assumptions]

theorem crypto.ed25519.initialize'.wp_proof :
    crypto.ed25519.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply crypto.ed25519.wp_cryptocustomrand_init
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
