/-
Specs for `github.com/goose-lang/primitive` (`Assume`, `RandomUint64`, `Mutex`).

The proofs live in the package namespace `github_com.goose_lang.primitive`,
so that e.g. `primitive.wp_initialize'` and `sync.wp_initialize'` do not clash.
The disk-only `primitive/disk` package is not covered here.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.goose_lang.primitive :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.goose_lang.primitive :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.goose_lang.primitive get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive }} := by
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

/-- FIXME: get rid of this, or document why a lemma for `ⁱᵐᵖˡ` is needed. -/
theorem «wp_RandomUint64__impl» :
    {{ (True : IProp GF) }} (App (Val RandomUint64.impl) (Val #()))
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

def isMutexDef (m : Loc) (R : IProp GF) : IProp GF := isLock m R
/-- This means `m` is a valid mutex with invariant `R`. -/
@[irreducible] def isMutex (m : Loc) (R : IProp GF) : IProp GF := isMutexDef m R
theorem isMutex_unseal : @isMutex = @isMutexDef := by funext; with_unfolding_all rfl

def ownMutexDef (m : Loc) : IProp GF := ownLock m
/-- This resource denotes ownership of the fact that the Mutex is currently
locked. -/
@[irreducible] def ownMutex (m : Loc) : IProp GF := ownMutexDef m
theorem ownMutex_unseal : @ownMutex = @ownMutexDef := by funext; with_unfolding_all rfl

theorem ownMutex_exclusive (m : Loc) : ⊢ ownMutex (GF := GF) m -∗ ownMutex m -∗ False := by
  simp only [ownMutex_unseal, ownMutexDef]
  exact ownLock_exclusive m

instance isMutex_ne (m : Loc) : NonExpansive (isMutex (GF := GF) m) := by
  rw [isMutex_unseal]; unfold isMutexDef; infer_instance

instance isMutex_persistent (m : Loc) (R : IProp GF) : Persistent (isMutex m R) := by
  rw [isMutex_unseal]; unfold isMutexDef; infer_instance

instance locked_timeless (m : Loc) : Timeless (ownMutex (GF := GF) m) := by
  rw [ownMutex_unseal]; unfold ownMutexDef; infer_instance

theorem init_Mutex (R : IProp GF) (E : CoPset) (m : Loc) :
    ⊢ typedPointsto (GF := GF) m (zero_val Bool) (DFrac.own 1) -∗ ▷ R ={E}=∗ isMutex m R := by
  simp only [isMutex_unseal, isMutexDef]
  exact init_lock R E m

theorem Mutex.wp_Lock (m : Loc) (R : IProp GF) :
    {{ isMutex m R }}
      (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); ownMutex m ∗ R }} := by
  wp_start as #His
  simp only [isMutex_unseal, isMutexDef, ownMutex_unseal, ownMutexDef]
  wp_apply wp_lock_lock $$ His as ⟨Hown, HR⟩
  iapply HΦ
  iframe

/-- This form is useful for defer statements. -/
theorem Mutex.wp_Unlock (m : Loc) (R : IProp GF) :
    {{ isMutex m R ∗ ownMutex m ∗ ▷ R }}
      (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#His, Hlocked, HR⟩
  simp only [isMutex_unseal, isMutexDef, ownMutex_unseal, ownMutexDef]
  wp_apply wp_lock_unlock $$ [$His $Hlocked $HR]
  iapply HΦ
  itrivial

end wps

end github_com.goose_lang.primitive

end Perennial
end
