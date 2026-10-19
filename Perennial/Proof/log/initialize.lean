/-
The proof of `log.initialize'`, from the trust-boundary axiom `log.wp_opaque_inits` on the
package's untranslated variable initializers.
-/
module

public import Perennial.Spec.log.initialize

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

/-- **Trust boundary: `log`'s untranslated variable initializers return.** `log.toml`
translates neither `std` (`New(os.Stderr, "", LstdFlags)`) nor `bufferPool` (a `sync.Pool`
literal), so goose emits each initializer as an axiomatized `X.init : val` with no semantics;
in Go they run at program start and return without panicking. The package's `isPkgInit` is
`True`, so nothing is assumed about what they store. Satisfiable: the `X.init` are
uninterpreted constants, and `fun _ => #()` meets the triple. -/
axiom log.wp_opaque_inits :
    ∀ v ∈ ([log.std.init,
        log.bufferPool.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

variable [package_sem : log.Assumptions]

theorem log.initialize'.wp_proof :
    log.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (log.wp_opaque_inits log.std.init (by mem_tac))
  wp_apply (log.wp_opaque_inits log.bufferPool.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
