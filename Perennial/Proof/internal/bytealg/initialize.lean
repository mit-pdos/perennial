/-
The proof of `internal.bytealg.initialize'`.
-/
module

public import Perennial.Spec.internal.bytealg.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem internal.bytealg.initialize'.wp_proof :
    internal.bytealg.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := w64) _ go.int as HMaxLen
  -- `init.0` (trusted): `MaxLen` is 63 or 31
  wp_func_call
  wp_call
  iunfold MaxLen at HMaxLen
  wp_apply wp_ArbitraryInt as %c -
  wp_if_destruct <;> (iframe Hown; is_pkg_init_finish)

end proof

end Perennial
