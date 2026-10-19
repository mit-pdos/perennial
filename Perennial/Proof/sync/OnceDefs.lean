/-
Shared definitions of the proofs of `sync.Once`.

A `sync.Once` will perform exactly one action. The specification realizes this
by requiring a specification for that action (a pre- and post-condition), a
proof of the precondition (which is used only once), and a proof that the
post-condition is persistent.

Every call to `Once.Do(f)` returns `Q` as a postcondition (using its
persistence to duplicate the postcondition to the first call), but uses the
pre-condition only once.

It is valid to call `Once.Do(f)` with different values of `f`, but they must
all satisfy `{P} #f #() {Q}`.

The proofs of `Once` use later credits, so they are stated for `HasLC.hasLC`.
-/
module

public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

abbrev OnceDone (o : Loc) : Loc := structFieldRef Once go!"done" o
abbrev OnceM (o : Loc) : Loc := structFieldRef Once go!"m" o

abbrev OnceInv (o : Loc) (Q : IProp GF) : IProp GF :=
  iprop(∃ done : Bool,
    "done1" ∷ sync.atomic.ownBool (GF := GF) (OnceDone (GF := GF) o) (DFrac.own (1 : Qp).half) done ∗
    "#HQ" ∷ □ (⌜done = true⌝ -∗ Q))

abbrev OnceLockInv (o : Loc) (P Q : IProp GF) : IProp GF :=
  iprop(∃ done : Bool,
    "done2" ∷ sync.atomic.ownBool (GF := GF) (OnceDone (GF := GF) o) (DFrac.own (1 : Qp).half) done ∗
    "HPQ" ∷ (if done then Q else P))

def isOnceDef (o : Loc) (P Q : IProp GF) : IProp GF :=
  iprop("#Q_persistent" ∷ □ (Q -∗ □ Q) ∗
    "#Qinv" ∷ inv nroot (OnceInv o Q) ∗
    "#Hm" ∷ isMutex (OnceM (GF := GF) o) (OnceLockInv o P Q))
@[irreducible] def isOnce (o : Loc) (P Q : IProp GF) : IProp GF := isOnceDef o P Q
theorem isOnce_unseal : @isOnce = @isOnceDef := by funext; with_unfolding_all rfl

instance isOnce_persistent (o : Loc) (P Q : IProp GF) : Persistent (isOnce o P Q) := by
  rw [isOnce_unseal]; unfold isOnceDef named; infer_instance

theorem ownBool_halves (u : Loc) (b : Bool) :
    sync.atomic.ownBool (GF := GF) u (DFrac.own 1) b ⊣⊢
      sync.atomic.ownBool u (DFrac.own (1 : Qp).half) b ∗
      sync.atomic.ownBool u (DFrac.own (1 : Qp).half) b := by
  have h := (sync.atomic.ownBool_fractional (GF := GF) u b).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

theorem init_Once (o : Loc) (P Q : IProp GF) (E : CoPset) [Persistent Q] :
    typedPointsto (GF := GF) o (zero_val Once) (DFrac.own 1) ∗ P ⊢ |={E}=> isOnce o P Q := by
  iintro ⟨Ho, HP⟩
  rw [isOnce_unseal]; unfold isOnceDef
  iStructNamed Ho
  have hz : (zero_val sync.atomic.Bool') =
      ({ _0' := zero_val _, v' := sync.atomic.b32w false } : sync.atomic.Bool') := rfl
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

end wps

end sync

end Perennial
