/-
Shared definitions of the proofs of `github.com/goose-lang/primitive`: its `isPkgInit`,
the lemma about `RandomUint64.impl`, and the predicates `isMutex`/`ownMutex` of `Mutex`.

The proofs live in the package namespace `github_com.goose_lang.primitive`,
so that e.g. `primitive.wp_initialize'` and `sync.wp_initialize'` do not clash.
`primitive/disk` is not translated: there is no disk extension for now.

This package lies below the channel theory (`Perennial.Golang.Theory.Chan.AuSpec.ChanInit`
imports it), so none of its files may import `Perennial.Golang.Theory.Chan*`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Lock
public import Perennial.Code.github_com.goose_lang.primitive
public import Perennial.GeneratedProof.github_com.goose_lang.primitive

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.goose_lang.primitive

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.goose_lang.primitive :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.goose_lang.primitive :=
  build_get_is_pkg_init_wf

/-- FIXME: get rid of this, or document why a lemma for `RandomUint64.impl` is needed. -/
theorem «wp_RandomUint64__impl» :
    {{ (True : IProp GF) }} (App (Val RandomUint64.impl) (Val #()))
    {{ (x : w64), RET #x; True }} := by
  wp_start as _
  wp_apply wp_ArbitraryInt as %x _
  iapply HΦ
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

end wps

end github_com.goose_lang.primitive

end Perennial
end
