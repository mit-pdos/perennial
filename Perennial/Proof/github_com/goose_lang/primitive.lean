/-
Port of `new/proof/github_com/goose_lang/primitive.v`: specs for
`github.com/goose-lang/primitive` (`Assume`, `RandomUint64`, `Mutex`).

The proofs live in the package namespace `github_com.goose_lang.primitive`
(Rocq: top level), so that e.g. `primitive.wp_initialize'` and
`sync.wp_initialize'` do not clash. (`primitive/disk.v` is disk-only and not
ported here.)
-/
import Perennial.Proof.ProofPrelude
import Perennial.Golang.Theory.Lock
import Perennial.Code.github_com.goose_lang.primitive
import Perennial.GeneratedProof.github_com.goose_lang.primitive

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.goose_lang.primitive

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.github_com.goose_lang.primitive :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.goose_lang.primitive :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.github_com.goose_lang.primitive get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

theorem wp_Assume (cond : Bool) :
    {{ (True : IProp GF) }} (App (Val (@! Assume)) (Val #cond)) {{ RET #(); ⌜cond = true⌝ }} := by
  wp_start
  cases cond
  · wp_auto
    iloeb as IH
    wp_pure
    iapply IH $$ Hpre HΦ
  · wp_end

theorem wp_Assume_true (Φ : val → IProp GF) :
    ⊢ Φ #() -∗ WP (App (Val (@! Assume)) (Val #true)) {{ Φ }} := by
  iintro HΦ
  wp_apply wp_Assume as %_
  iexact HΦ

theorem wp_Assume_false :
    ⊢ ∀ Φ : val → IProp GF, WP (App (Val (@! Assume)) (Val #false)) {{ Φ }} := by
  iintro %Φ
  wp_apply wp_Assume as %H
  cases H

/-- FIXME (Rocq): get rid of this, or document why a lemma for `ⁱᵐᵖˡ` is needed. -/
theorem «wp_RandomUint64__impl» :
    {{ (True : IProp GF) }} (App (Val «RandomUint64ⁱᵐᵖˡ») (Val #()))
    {{ (x : w64), RET #x; True }} := by
  wp_start as _
  wp_apply wp_ArbitraryInt as %x _
  iapply HΦ
  itrivial

theorem wp_RandomUint64 :
    {{ (True : IProp GF) }} (App (Val (@! RandomUint64)) (Val #()))
    {{ (x : w64), RET #x; True }} := by
  wp_start_folded as _
  wp_func_call
  iapply «wp_RandomUint64__impl» $$ [] HΦ
  itrivial

def is_Mutex_def (m : loc) (R : IProp GF) : IProp GF := is_lock m R
/-- This means `m` is a valid mutex with invariant `R` (Rocq `Opaque is_Mutex`). -/
@[irreducible] def is_Mutex (m : loc) (R : IProp GF) : IProp GF := is_Mutex_def m R
theorem is_Mutex_unseal : @is_Mutex = @is_Mutex_def := by funext; with_unfolding_all rfl

def own_Mutex_def (m : loc) : IProp GF := own_lock m
/-- This resource denotes ownership of the fact that the Mutex is currently
locked (Rocq `Opaque own_Mutex`). -/
@[irreducible] def own_Mutex (m : loc) : IProp GF := own_Mutex_def m
theorem own_Mutex_unseal : @own_Mutex = @own_Mutex_def := by funext; with_unfolding_all rfl

theorem own_Mutex_exclusive (m : loc) : ⊢ own_Mutex (GF := GF) m -∗ own_Mutex m -∗ False := by
  simp only [own_Mutex_unseal, own_Mutex_def]
  exact own_lock_exclusive m

instance is_Mutex_ne (m : loc) : NonExpansive (is_Mutex (GF := GF) m) := by
  rw [is_Mutex_unseal]; unfold is_Mutex_def; infer_instance

instance is_Mutex_persistent (m : loc) (R : IProp GF) : Persistent (is_Mutex m R) := by
  rw [is_Mutex_unseal]; unfold is_Mutex_def; infer_instance

instance locked_timeless (m : loc) : Timeless (own_Mutex (GF := GF) m) := by
  rw [own_Mutex_unseal]; unfold own_Mutex_def; infer_instance

theorem init_Mutex (R : IProp GF) (E : CoPset) (m : loc) :
    ⊢ typed_pointsto (GF := GF) m (zero_val Bool) (DFrac.own 1) -∗ ▷ R ={E}=∗ is_Mutex m R := by
  simp only [is_Mutex_unseal, is_Mutex_def]
  exact init_lock R E m

theorem wp_Mutex__Lock (m : loc) (R : IProp GF) :
    {{ is_Mutex m R }}
      (App (Val (m @!! go.type.PointerType Mutex @!! go!"Lock")) (Val #()))
    {{ RET #(); own_Mutex m ∗ R }} := by
  wp_start as #His
  simp only [is_Mutex_unseal, is_Mutex_def, own_Mutex_unseal, own_Mutex_def]
  wp_apply wp_lock_lock $$ His as ⟨Hown, HR⟩
  iapply HΦ
  iframe

/-- This form is useful for defer statements. -/
theorem wp_Mutex__Unlock (m : loc) (R : IProp GF) :
    {{ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}
      (App (Val (m @!! go.type.PointerType Mutex @!! go!"Unlock")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#His, Hlocked, HR⟩
  simp only [is_Mutex_unseal, is_Mutex_def, own_Mutex_unseal, own_Mutex_def]
  wp_apply wp_lock_unlock $$ [$His $Hlocked $HR]
  iapply HΦ
  itrivial

end wps

end github_com.goose_lang.primitive

end Perennial
end
