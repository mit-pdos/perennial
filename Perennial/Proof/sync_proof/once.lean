/-
Port of `new/proof/sync_proof/once.v`: `sync.Once`.

A `sync.Once` will perform exactly one action. The specification realizes this
by requiring a specification for that action (a pre- and post-condition), a
proof of the precondition (which is used only once), and a proof that the
post-condition is persistent.

Every call to `Once.Do(f)` returns `Q` as a postcondition (using its
persistence to duplicate the postcondition to the first call), but uses the
pre-condition only once.

It is valid to call `Once.Do(f)` with different values of `f`, but they must
all satisfy `{P} #f #() {Q}`.
-/
import Perennial.Proof.sync_proof.base
import Perennial.Proof.sync_proof.mutex
import Perennial.Proof.sync.atomic

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

abbrev OnceDone (o : loc) : loc := struct_field_ref Once.t go!"done" o
abbrev OnceM (o : loc) : loc := struct_field_ref Once.t go!"m" o

abbrev OnceInv (o : loc) (Q : IProp GF) : IProp GF :=
  iprop(∃ done : Bool,
    "done1" ∷ sync.atomic.ownBool (GF := GF) (OnceDone (GF := GF) o) (DFrac.own (1 : Qp).half) done ∗
    "#HQ" ∷ □ (⌜done = true⌝ -∗ Q))

abbrev OnceLockInv (o : loc) (P Q : IProp GF) : IProp GF :=
  iprop(∃ done : Bool,
    "done2" ∷ sync.atomic.ownBool (GF := GF) (OnceDone (GF := GF) o) (DFrac.own (1 : Qp).half) done ∗
    "HPQ" ∷ (if done then Q else P))

def isOnceDef (o : loc) (P Q : IProp GF) : IProp GF :=
  iprop("#Q_persistent" ∷ □ (Q -∗ □ Q) ∗
    "#Qinv" ∷ inv nroot (OnceInv o Q) ∗
    "#Hm" ∷ isMutex (OnceM (GF := GF) o) (OnceLockInv o P Q))
@[irreducible] def isOnce (o : loc) (P Q : IProp GF) : IProp GF := isOnceDef o P Q
theorem isOnce_unseal : @isOnce = @isOnceDef := by funext; with_unfolding_all rfl

instance isOnce_persistent (o : loc) (P Q : IProp GF) : Persistent (isOnce o P Q) := by
  rw [isOnce_unseal]; unfold isOnceDef named; infer_instance

theorem ownBool_halves (u : loc) (b : Bool) :
    sync.atomic.ownBool (GF := GF) u (DFrac.own 1) b ⊣⊢
      sync.atomic.ownBool u (DFrac.own (1 : Qp).half) b ∗
      sync.atomic.ownBool u (DFrac.own (1 : Qp).half) b := by
  have h := (sync.atomic.ownBool_fractional (GF := GF) u b).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

theorem init_Once (o : loc) (P Q : IProp GF) (E : CoPset) [Persistent Q] :
    typed_pointsto (GF := GF) o (zero_val Once.t) (DFrac.own 1) ∗ P ⊢ |={E}=> isOnce o P Q := by
  iintro ⟨Ho, HP⟩
  rw [isOnce_unseal]; unfold isOnceDef
  iStructNamed Ho
  have hz : (zero_val sync.atomic.Bool'.t) =
      ({ _0' := zero_val _, v' := sync.atomic.b32w false } : sync.atomic.Bool'.t) := rfl
  ihave Hd := (ownBool_halves (OnceDone (GF := GF) o) false).1 $$ [done]
  · simp only [sync.atomic.ownBool_unseal, sync.atomic.ownBoolDef]
    rw [← hz]; iexact done
  icases Hd with ⟨done1, done2⟩
  imod init_Mutex (OnceLockInv o P Q) E (OnceM (GF := GF) o) $$ m [done2 HP] with #Hm
  · inext; unfold OnceLockInv; iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]; iframe
  imod inv_alloc nroot E (OnceInv o Q) $$ [done1] with #Hinv
  · inext; unfold OnceInv; iexists false; iframe
    imodintro; iintro %h; cases h
  imodintro
  iframe #
  imodintro
  iintro #HQ
  imodintro
  iexact HQ

theorem Once.wp_doSlow (o : loc) (P Q : IProp GF) (f : func.t) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isOnce o P Q ∗
        iprop({{ P }} (App (Val #f) (Val #())) {{ RET #(); Q }}) }}
      (App (Val (o @!! go.type.PointerType Once @!! go!"doSlow")) (Val #f))
    {{ RET #(); Q }} := by
  wp_start as ⟨#HO, #Hf⟩
  simp only [isOnce_unseal, isOnceDef]
  iNamed HO
  iapply wp_with_defer
  iintro %defer Hdefer
  wp_auto_lc 2
  wp_apply Mutex.wp_Lock $$ [$Hm] with ⟨Hlocked, Hlk⟩
  unfold OnceLockInv
  icases Hlk with ⟨%done, done2, HPQ⟩
  wp_apply_core sync.atomic.Bool.wp_Load $$ [] [-]
  · iPkgInit
  iinv Qinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold OnceInv
  icases Hi with ⟨%done0, done1, #HQ⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  icombine done1 done2 gives %Heq
  subst Heq
  inext
  iexists done0
  iframe done1
  iintro done1
  imod Hmask with _
  imod Hclose $$ [done1] with _
  · inext; iexists done0; iframe done1; iframe #
  imodintro
  wp_auto
  cases done0
  · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply Hf $$ HPQ with HQ'
    ihave #HQ2 := Q_persistent $$ HQ'
    wp_apply_core sync.atomic.Bool.wp_Store $$ [] [-]
    · iPkgInit
    iinv Qinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%d, done1, #HQ1⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    icombine done1 done2 gives %Heq
    subst Heq
    ihave Hfull := (ownBool_halves (OnceDone (GF := GF) o) false).2 $$ [done1 done2]
    · iframe
    inext
    iexists false
    iframe Hfull
    iintro Hfull
    icases (ownBool_halves (OnceDone (GF := GF) o) true).1 $$ Hfull with ⟨done1, done2⟩
    imod Hmask with _
    imod Hclose $$ [done1] with _
    · inext; iexists true; iframe done1; imodintro; iintro _; iexact HQ2
    imodintro
    wp_auto
    wp_apply Mutex.wp_Unlock (OnceM (GF := GF) o) (OnceLockInv o P Q) $$ [Hlocked done2 HQ']
    · iframe #; iframe Hlocked; inext; unfold OnceLockInv; iexists true
      simp only [↓reduceIte]; iframe
    iapply HΦ $$ HQ2
  · simp only [Bool.not_true, ↓reduceIte]
    ihave #HQ2 := Q_persistent $$ HPQ
    wp_auto
    wp_apply Mutex.wp_Unlock (OnceM (GF := GF) o) (OnceLockInv o P Q) $$ [Hlocked done2 HPQ]
    · iframe #; iframe Hlocked; inext; unfold OnceLockInv; iexists true
      simp only [↓reduceIte]; iframe
    iapply HΦ $$ HQ2

theorem Once.wp_Do (o : loc) (P Q : IProp GF) (f : func.t) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isOnce o P Q ∗
        iprop({{ P }} (App (Val #f) (Val #())) {{ RET #(); Q }}) }}
      (App (Val (o @!! go.type.PointerType Once @!! go!"Do")) (Val #f))
    {{ RET #(); Q }} := by
  wp_start as ⟨#HO, #Hf⟩
  simp only [isOnce_unseal, isOnceDef]
  iNamed HO
  wp_auto_lc 1
  wp_apply_core sync.atomic.Bool.wp_Load $$ [] [-]
  · iPkgInit
  iinv Qinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold OnceInv
  icases Hi with ⟨%done, done1, #HQ⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists done
  iframe done1
  iintro done1
  imod Hmask with _
  imod Hclose $$ [done1] with _
  · inext; iexists done; iframe done1; iframe #
  imodintro
  wp_auto
  cases done
  · (try wp_auto)
    wp_apply Once.wp_doSlow o P Q f $$ [] with HQ'
    · rw [isOnce_unseal]; unfold isOnceDef; iframe #
    iapply HΦ $$ HQ'
  · (try wp_auto)
    iapply HΦ
    iapply HQ
    ipureintro; rfl

end wps

end sync

end Perennial
end
