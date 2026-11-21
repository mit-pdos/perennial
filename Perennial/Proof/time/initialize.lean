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
    | wp_apply wp_GlobalAlloc (V := Loc) Local (go.PointerType Location.ty) as HLocal
    | wp_apply wp_GlobalAlloc (V := Loc) UTC (go.PointerType Location.ty) as HUTC
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
  -- asynctimerchan: its trusted initializer allocates the runtime clock
  wp_call
  unfold runtimeClockInit runtimeClockType
  wp_call
  wp_apply wp_GlobalAlloc (V := Loc) runtimeClock (go.PointerType go.int64) as Hclk
  wp_apply wp_ArbitraryInt as %c0 -
  wp_apply wp_alloc_untyped #c0 as %lc Hlc
  try wp_auto
  ipersist Hclk
  imod mono_nat_own_alloc (GF := GF) (clockEnc (sint.Z c0)) with ⟨%γ, Hauth, #Hlb0⟩
  imod inv_alloc clockN ⊤ (clockInv γ lc) $$ [Hlc Hauth] with #Hinv
  · inext; iexists c0; iframe
  -- startNano = runtimeNano() - 1; Go never writes it again
  wp_apply wp_runtimeNano as %t _
  ipersist Hstart
  -- Local = &localLoc (set before startNano, in Go's order); read only from here on (`isInit`)
  ipersist HLocal
  -- UTC = &utcLoc (set just after Local); likewise read only from here on
  ipersist HUTC
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
  imodintro
  unfold isInit
  isplitr
  · iexists _; iexact Hstart
  isplitr
  · iexists _; iexact HLocal
  isplitr
  · iexists _; iexact HUTC
  unfold clockLb isRuntimeClock
  iexists γ
  isplitr
  · iexists lc; iframe #
  iapply monoNatLbOwn_le _ (by unfold clockEnc; omega) $$ Hlb0

end proof

end Perennial
