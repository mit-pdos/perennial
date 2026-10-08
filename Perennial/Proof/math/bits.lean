/-
Package initialization of `math/bits` and
specs for `Len64` and `Len`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.math.bits
import Perennial.GeneratedProof.math.bits
import Perennial.Proof.«unsafe»

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace math.bits

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.math.bits :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math.bits :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.math.bits get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.bits }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) divideError go.error with _
  wp_apply wp_GlobalAlloc (V := GoInterface) overflowError go.error with _
  wp_apply wp_GlobalAlloc (V := GoArray w8 64) deBruijn64tab (go.ArrayType 64 go.byte) with H1
  wp_apply wp_GlobalAlloc (V := GoArray w8 32) deBruijn32tab (go.ArrayType 32 go.byte) with H2
  wp_apply «unsafe».wp_initialize' _ Hinit.2.1 $$ Hown with ⟨Hown, #Hunsafe⟩
  iframe Hown
  is_pkg_init_finish

set_option maxRecDepth 100000 in
theorem len8tab_eq : ∃ s : GoString, len8tab = #s ∧ s.length = 256 :=
  ⟨_, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem wp_Len64 (x : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.bits }}
      (App (Val (@! Len64)) (Val #x))
    {{ (l : w64), RET #l; True }} := by
  wp_start
  obtain ⟨s, hs, hlen⟩ := len8tab_eq
  rw [hs]
  clear hs
  wp_auto
  wp_if_destruct <;> wp_if_destruct <;> wp_if_destruct
  all_goals wp_pures
  all_goals split
  all_goals first
    | (wp_auto; wp_end)
    | (exfalso; rename_i h; exact h _ (List.getElem?_eq_getElem (by rw [hlen]; word)))

theorem wp_Len (x : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.bits }}
      (App (Val (@! Len)) (Val #x))
    {{ (l : w64), RET #l; True }} := by
  wp_start
  wp_auto
  wp_apply wp_Len64 with %l _
  wp_end

end wps

end math.bits

end Perennial
end
