/-
The proof of `time.initialize'`: the package's global `startNano` (`runtimeNano() - 1`,
translated) is its `isPkgInit`; the other variables' initializers are untranslated, under
the trust-boundary axiom `time.wp_opaque_inits`.
-/
module

public import Perennial.Spec.time.initialize
public import Perennial.Spec.time.runtimeNano

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

/-- **Trust boundary: `time`'s untranslated variable initializers return.** `time.toml`
translates, of the package's variables, only `startNano`; the others (the location tables
`utcLoc`, `UTC`, `Local`, `platformZoneSources`, the errors `errBad`, `errLocation`, ...,
the formatting tables `longDayNames`, ..., `std0x`, `unitMap`, and `asynctimerchan`, a
`godebug` setting) are each emitted as an axiomatized `X.init : val` with no semantics; in Go
they run at program start and return without panicking. The package's `isPkgInit` mentions
only `startNano`, so nothing is assumed about what they store. Satisfiable: the `X.init` are
uninterpreted constants, and `fun _ => #()` meets the triple. -/
axiom time.wp_opaque_inits :
    ∀ v ∈ ([time.std0x.init,
        time.longDayNames.init,
        time.shortDayNames.init,
        time.shortMonthNames.init,
        time.longMonthNames.init,
        time.errAtoi.init,
        time.errBad.init,
        time.errLeadingInt.init,
        time.unitMap.init,
        time.asynctimerchan.init,
        time.utcLoc.init,
        time.UTC.init,
        time.Local.init,
        time.errLocation.init,
        time.errBadData.init,
        time.platformZoneSources.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

variable [package_sem : time.Assumptions]

theorem time.initialize'.wp_proof
    (wp_runtimeNano : time.runtimeNano.spec (GF := GF) (hG := hG)) :
    time.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := w64) time.startNano go.int64 as HstartNano
  wp_apply (time.wp_opaque_inits time.std0x.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.longDayNames.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.shortDayNames.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.shortMonthNames.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.longMonthNames.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.errAtoi.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.errBad.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.errLeadingInt.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.unitMap.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.asynctimerchan.init (by mem_tac))
  -- `startNano = runtimeNano() - 1`; Go never writes it afterwards (`isInit`).
  wp_apply wp_runtimeNano as %x -
  ipersist HstartNano
  wp_apply (time.wp_opaque_inits time.utcLoc.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.UTC.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.Local.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.errLocation.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.errBadData.init (by mem_tac))
  wp_apply (time.wp_opaque_inits time.platformZoneSources.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish
  isplitr
  · imodintro; itrivial
  · imodintro
    iexists _
    iexact HstartNano

end proof

end Perennial
