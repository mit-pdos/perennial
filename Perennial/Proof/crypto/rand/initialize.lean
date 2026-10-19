/-
The proof of `crypto/rand.initialize'`.
-/
module

public import Perennial.Spec.crypto.rand.initialize
public import Perennial.Spec.math.big.initialize
public import Perennial.Spec.io.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.rand.Assumptions]

theorem crypto.rand.initialize'.wp_proof
    (wp_big_initialize : math.big.initialize'.spec (GF := GF) (hG := hG))
    (wp_io_initialize : io.initialize'.spec (GF := GF) (hG := hG)) :
    crypto.rand.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_big_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hbig⟩
  wp_apply wp_io_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hio⟩
  -- Reader: its trusted initializer allocates it and stores the reader
  wp_call
  wp_apply_core wp_GlobalAlloc (V := GoInterface) _ io.Reader.ty
  iintro HR
  wp_pures
  wp_store
  ipersist HR
  wp_auto
  iframe Hown
  is_pkg_init_finish
  imodintro
  unfold crypto.rand.isInitialized crypto.rand.Reader
  iexists _
  iexact HR

end proof

end Perennial
