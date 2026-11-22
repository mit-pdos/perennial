/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/skipvars.initialize'`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.Assumptions]

open github_com.mit_pdos.perennial.goose.testdata.examples.skipvars in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.initialize'.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  -- the update makes `last`'s cell persistent once its initializer has stored it
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := w64) last go.uint64 as Hl
  wp_apply wp_GlobalAlloc (V := w64) mid go.uint64 as Hm
  wp_apply wp_GlobalAlloc (V := w64) first go.uint64 as Hf
  ipersist Hl
  imodintro
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  iframe Hown
  is_pkg_init_finish
  iunfold isInit
  have h3 : (W64 1 + W64 1 + W64 1 : w64) = W64 3 := by decide
  rw [← h3]
  iframe Hl
  imodintro
  ipureintro
  trivial

end proof

end Perennial
