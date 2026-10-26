/-
The proof of `time.initialize'`.
-/
module

public import Perennial.Spec.time.initialize
public import Perennial.Spec.time.runtimeNano
public import Perennial.Spec.errors.initialize
public import Perennial.Spec.errors.New

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

set_option maxHeartbeats 400000 in
theorem time.initialize'.wp_proof
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG))
    (wp_New : errors.New.spec (GF := GF) (hG := hG))
    (wp_runtimeNano : time.runtimeNano.spec (GF := GF) (hG := hG)) :
    time.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (first
    | wp_apply wp_GlobalAlloc (V := w64) startNano go.int64 as Hstart
    | wp_apply wp_GlobalAlloc (V := GoArray w64 _) _ (go.ArrayType _ go.int) as _
    | wp_apply wp_GlobalAlloc (V := GoSlice) _ (go.SliceType go.string) as _
    | wp_apply wp_GlobalAlloc (V := GoInterface) _ go.error as _
    | wp_apply wp_GlobalAlloc (V := Loc) _ (go.MapType go.string go.uint64) as _
    | wp_apply wp_GlobalAlloc (V := Loc) _ (go.PointerType Location.ty) as _
    | wp_apply wp_GlobalAlloc (V := Location) _ Location.ty as _)
  wp_apply wp_errors_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  -- the variables, in Go's initialization order
  repeat (first
    | (wp_apply wp_New as %_ _)
    | (wp_apply wp_slice_literal (V := GoString) _
       isplitr
       · ipureintro; rfl
       iintro %_ ⟨_, _⟩)
    | wp_call
    | wp_auto)
  -- unitMap
  wp_apply (wp_map_make1 (K := GoString) (V := w64)) as %m Hm
  repeat (wp_apply wp_mapInsert $$ Hm as Hm)
  -- asynctimerchan: its trusted initializer does nothing
  wp_call
  -- startNano = runtimeNano() - 1; Go never writes it again
  wp_apply wp_runtimeNano as %t _
  ipersist Hstart
  repeat (first
    | (wp_apply wp_New as %_ _)
    | (wp_apply wp_slice_literal (V := GoString) _
       isplitr
       · ipureintro; rfl
       iintro %_ ⟨_, _⟩)
    | wp_call
    | wp_auto)
  iframe Hown
  is_pkg_init_finish
  iexists _
  iexact Hstart

end proof

end Perennial
