/-
Shared definitions of the proofs of `sync.Pool`: `isPool p f P`, a pool at `p` whose `New` is
`f` and whose values satisfy `P`, its initialization `init_Pool`, and the spec of the model
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

/-- `New` is `nil` or returns values satisfying `P`. -/
def newSpec (f : GoFunc) (P : GoAny → IProp GF) : IProp GF :=
  iprop(⌜f = func.nil⌝ ∨ {{ True }} (App (Val #f) (Val #())) {{ (x : GoAny), RET #x; P x }})

instance newSpec_persistent (f : GoFunc) (P : GoAny → IProp GF) : Persistent (newSpec f P) := by
  unfold newSpec; infer_instance

def isPoolDef (p : Loc) (f : GoFunc) (P : GoAny → IProp GF) : IProp GF :=
  iprop("#New" ∷ p.[Pool, go!"New"] ↦□ f ∗
    "#HNew" ∷ newSpec f P ∗
    "#Hinv" ∷ inv nroot (poolLocalInv p P))
/-- `p` is a `sync.Pool` whose field `New` is `f` (no longer written) and whose values (those
`Put` and those `New` returns) satisfy `P` (sealed). -/
@[irreducible] def isPool (p : Loc) (f : GoFunc) (P : GoAny → IProp GF) : IProp GF :=
  isPoolDef p f P
theorem isPool_unseal : @isPool = @isPoolDef := by funext; with_unfolding_all rfl

instance isPool_persistent (p : Loc) (f : GoFunc) (P : GoAny → IProp GF) :
    Persistent (isPool p f P) := by
  rw [isPool_unseal]; unfold isPoolDef named; infer_instance

/-- A pool not used yet (its field `local` is `nil`, as in the zero `Pool` and in
`Pool{New: f}`) becomes an `isPool`, with its `New`. -/
theorem init_Pool (p : Loc) (v : Pool) (P : GoAny → IProp GF) (E : CoPset)
    (hlocal : v.local' = null) :
    typedPointsto (GF := GF) p v (DFrac.own 1) ∗ newSpec v.New' P ⊢ |={E}=> isPool p v.New' P := by
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
theorem wp_Pool_state (p : Loc) (f : GoFunc) (P : GoAny → IProp GF) :
    {{ isPool p f P }} (App (Val Pool.state) (Val #p)) {{ (s : Loc), RET #s; pool.isPool s P }} := by
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
