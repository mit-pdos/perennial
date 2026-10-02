/-
Port of `new/proof/math/bits.v`: package initialization of `math/bits` and
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
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.math.bits :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math.bits :=
  build_get_is_pkg_init_wf

/-! `go.error` is a `def` in Lean, so its underlying-type instances are not
found by unification with `go.InterfaceType _` (same workaround as in
`Perennial/Proof/errors.lean`). -/
abbrev error_elems : List go.interface_elem :=
  [go.MethodElem go!"Error" (go.Signature [] false [go.string])]

local instance error_is_underlying : go.error ↓u go.InterfaceType error_elems := by
  unfold go.error; infer_instance

local instance error_underlying_eq : go.error ≤u go.InterfaceType error_elems := by
  unfold go.error; exact underlying_eq _

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.math.bits get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.math.bits }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := interface.t) divideError go.error with _
  wp_apply wp_GlobalAlloc (V := interface.t) overflowError go.error with _
  wp_apply wp_GlobalAlloc (V := array.t w8 64) deBruijn64tab (go.ArrayType 64 go.byte) with H1
  wp_apply wp_GlobalAlloc (V := array.t w8 32) deBruijn32tab (go.ArrayType 32 go.byte) with H2
  wp_apply «unsafe».wp_initialize' _ Hinit.2.1 $$ Hown with ⟨Hown, #Hunsafe⟩
  iframe Hown
  is_pkg_init_finish

set_option maxRecDepth 100000 in
theorem len8tab_eq : ∃ s : go_string, len8tab = #s ∧ s.length = 256 :=
  ⟨_, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem wp_Len64 (x : w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.math.bits }}
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
    {{ is_pkg_init (PROP := IProp GF) pkg_id.math.bits }}
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
