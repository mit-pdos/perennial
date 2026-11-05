/-
Shared definitions of the proofs of `sync.Pool`: `isPool p f R P`, a pool at `p` whose `New` is
`f`, which may assume `R`, and whose values satisfy `P`, its initialization `init_Pool`, and the spec of the model
helper `Pool.state` (`TrustedCode/sync.lean`), which finds or installs the pool's state, a
model pool of `goose/model/pool` (`Proof/github_com/mit_pdos/perennial/goose/model/pool`).
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.pool.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The receiver's type in the models of `Pool`'s methods (`TrustedCode/sync.lean`), which are
below `Pool.ty`'s definition. -/
theorem Pool_ty_eq : (go.GoType.Named go!"sync.Pool" [] : go.GoType) = Pool.ty := by
  unfold Pool.ty; rfl

open github_com.mit_pdos.perennial.goose.model in
/-- The invariant of the field `local` of the pool at `p`: `nil`, or a model pool whose
elements satisfy `P`. -/
def poolLocalInv (p : Loc) (P : GoAny → IProp GF) : IProp GF :=
  iprop(∃ (s : Loc),
    "Hlocal" ∷ p.[Pool, go!"local"] ↦ s ∗
    "Hs" ∷ (⌜s = null⌝ ∨ pool.isPool s P))

/-- `New` is `nil` or, given `R` (which it gives back), returns values satisfying `P`. `R` is
what a caller of `Get` holds and lends to `New` for the call: `True` when `New` needs nothing; a
resource when `New` reads state that is only valid while its holder is (a closure over a
variable its creator writes again later, valid only for as long as the creator's protocol
says). -/
def newSpec (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF) : IProp GF :=
  iprop(⌜f = func.nil⌝ ∨ {{ R }} (App (Val #f) (Val #())) {{ (x : GoAny), RET #x; P x ∗ R }})

instance newSpec_persistent (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF) :
    Persistent (newSpec f R P) := by
  unfold newSpec; infer_instance

/-- A `New` that needs nothing (a triple with precondition `True`) has a `newSpec` for any `R`. -/
theorem newSpec_of_true (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF) :
    iprop(⌜f = func.nil⌝ ∨ {{ True }} (App (Val #f) (Val #())) {{ (x : GoAny), RET #x; P x }}) ⊢
      newSpec f R P := by
  unfold newSpec
  iintro (%h | #H)
  · ileft; ipureintro; exact h
  iright
  wp_start as HR
  wp_apply H as %x Hx
  iapply HΦ
  iframe

def isPoolDef (p : Loc) (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF) : IProp GF :=
  iprop("#New" ∷ p.[Pool, go!"New"] ↦□ f ∗
    "#HNew" ∷ newSpec f R P ∗
    "#Hinv" ∷ inv nroot (poolLocalInv p P))
/-- `p` is a `sync.Pool` whose field `New` is `f` (no longer written), which `Get` calls lending
it the caller's `R`, and whose values (those `Put` and those `New` returns) satisfy `P`
(sealed). -/
@[irreducible] def isPool (p : Loc) (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF) :
    IProp GF :=
  isPoolDef p f R P
theorem isPool_unseal : @isPool = @isPoolDef := by funext; with_unfolding_all rfl

instance isPool_persistent (p : Loc) (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF) :
    Persistent (isPool p f R P) := by
  rw [isPool_unseal]; unfold isPoolDef named; infer_instance

/-- A pool's `isPool` holds for any other `New` spec `R'` that its `New` meets: `isPool` is the
field `New`, its spec and the pool's invariant, which does not mention the spec. (A pool
initialized once serves several `R`s: `init_Pool` at one, this lemma for the others.) -/
theorem isPool_respec (p : Loc) (f : GoFunc) (R R' : IProp GF) (P : GoAny → IProp GF) :
    isPool p f R P ∗ newSpec f R' P ⊢ isPool p f R' P := by
  rw [isPool_unseal]
  unfold isPoolDef named
  iintro ⟨⟨#HN, -, #Hinv⟩, #Hs⟩
  iframe #

/-- A pool not used yet (its field `local` is `nil`, as in the zero `Pool` and in
`Pool{New: f}`) becomes an `isPool`, with its `New`. The pool's points-to can be kept until
`New`'s spec is known (no method has been called while its owner holds it). -/
theorem init_Pool (p : Loc) (v : Pool) (R : IProp GF) (P : GoAny → IProp GF) (E : CoPset)
    (hlocal : v.local' = null) :
    typedPointsto (GF := GF) p v (DFrac.own 1) ∗ newSpec v.New' R P ⊢
      |={E}=> isPool p v.New' R P := by
  iintro ⟨Hp, #HNew⟩
  rw [isPool_unseal]; unfold isPoolDef
  iStructNamed Hp
  ipersist New
  imod inv_alloc nroot E (poolLocalInv p P) $$ [local'] with #Hinv
  · inext; unfold poolLocalInv; iexists v.local'; iframe
    ileft; ipureintro; exact hlocal
  imodintro
  iframe #

open github_com.mit_pdos.perennial.goose.model in
theorem wp_Pool_state (p : Loc) (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF) :
    {{ isPool p f R P }} (App (Val Pool.state) (Val #p)) {{ (s : Loc), RET #s; pool.isPool s P }} := by
  simp only [isPool_unseal, isPoolDef]
  wp_start as #His
  iNamed His
  rw [Pool_ty_eq]
  wp_auto
  imod pool.init_Pool new_ptr P ⊤ $$ new with #Hnew
  wp_bind (CmpXchg _ _ _)
  iinv Hinv with Hi
  unfold poolLocalInv
  icases Hi with ⟨%s, >Hlocal, Hs⟩
  by_cases Hnull : s = null
  · subst Hnull
    wp_apply_core wp_cmpxchg_suc _ (null : Loc) null new_ptr _ _ rfl $$ Hlocal
    iintro Hlocal
    imodintro
    isplitl [Hlocal]
    · inext; iexists new_ptr; iframe; iright; iexact Hnew
    wp_auto
    iapply HΦ
    iexact Hnew
  · wp_apply_core wp_cmpxchg_fail _ s null new_ptr (DFrac.own 1) _ _ Hnull $$ Hlocal
    icases Hs with (%h | #Hs)
    · exact absurd h Hnull
    iintro Hlocal
    imodintro
    isplitl [Hlocal]
    · inext; iexists s; iframe; iright; iexact Hs
    wp_auto
    iapply HΦ
    iexact Hs

end wps

end sync

end Perennial
