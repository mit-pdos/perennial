/-
Shared definitions of the "join" idiom for
`WaitGroup`: `Add` hands out permission to call `Done` with a chosen
proposition, and `Wait` collects all of them. The specs of the idiom
(`sync.join.WaitGroup.wp_Add`, `wp_Done`, `wp_Wait`) are corollaries of `WaitGroup`'s specs,
in `Results`.
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.WaitGroupDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

namespace join

structure WaitGroupJoinNames where
  wgGn : WaitGroupNames
  wgApropGn : GName
  wgNotDoneGn : GName

abbrev wgjN : Namespace := nroot.@"wgjoin"

section waitgroup_join_idiom
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The body of the internal invariant. Maintains ownership of the waitgroup
counter so that `Done()` can run concurrently to `Add`. -/
abbrev wgjInv (γ : WaitGroupJoinNames) : IProp GF :=
  iprop(∃ (ctr : w32) (added done : Nat) (Pdone : IProp GF),
    "Hwg_ctr" ∷ ownWaitGroup γ.wgGn ctr ∗
    "Hadded" ∷ ownTokAuthDfrac γ.wgNotDoneGn (DFrac.own (1 : Qp).half) added ∗
    "Hdone_toks" ∷ ownToks γ.wgNotDoneGn done ∗
    "Hdone_aprop" ∷ ownApropFrag γ.wgApropGn Pdone done ∗
    "Hdone_P" ∷ Pdone ∗
    "%Hctr_pos" ∷ ⌜0 ≤ sint.Z ctr⌝ ∗
    "%Hctr" ∷ ⌜sint.Z ctr = (added : Int) - (done : Int)⌝)

abbrev isWgjInv (wg : Loc) (γ : WaitGroupJoinNames) : IProp GF :=
  iprop("#His" ∷ isWaitGroup wg γ.wgGn (wgjN.@"wg") ∗
    "#Hinv" ∷ inv (wgjN.@"inv") (wgjInv γ))

/-- Permission to call `Add` or `Wait`. Calling `Add` will extend `P` with a
caller-chosen proposition (as long as `num_added` doesn't overflow) and calling
`Wait` will give `P` as postcondition and reset the permission. -/
def ownAdderDef (wg : Loc) (num_added : w32) (P : IProp GF) : IProp GF :=
  iprop(∃ (γ : WaitGroupJoinNames) (P' : IProp GF),
    "Hno_waiters" ∷ ownWaitGroupWaiters γ.wgGn 0 ∗
    "Haprop" ∷ ownApropAuth γ.wgApropGn P' (sint.nat num_added) ∗
    "Hadded" ∷ ownTokAuthDfrac γ.wgNotDoneGn (DFrac.own (1 : Qp).half) (sint.nat num_added) ∗
    "%Hadded_pos" ∷ ⌜0 ≤ sint.Z num_added⌝ ∗
    "HimpliesP" ∷ (P' -∗ P) ∗
    "#Hinv" ∷ isWgjInv wg γ)
@[irreducible] def ownAdder (wg : Loc) (num_added : w32) (P : IProp GF) : IProp GF :=
  ownAdderDef wg num_added P
theorem ownAdder_unseal : @ownAdder = @ownAdderDef := by funext; with_unfolding_all rfl

/-- Permission to call `Done` as long as `P` is passed in. -/
def ownDoneDef (wg : Loc) (P : IProp GF) : IProp GF :=
  iprop(∃ (γ : WaitGroupJoinNames),
    "Haprop" ∷ ownAprop γ.wgApropGn P ∗
    "Hdone_tok" ∷ ownToks γ.wgNotDoneGn 1 ∗
    "#Hinv" ∷ isWgjInv wg γ)
@[irreducible] def ownDone (wg : Loc) (P : IProp GF) : IProp GF := ownDoneDef wg P
theorem ownDone_unseal : @ownDone = @ownDoneDef := by funext; with_unfolding_all rfl

theorem ownTokAuth_halves (γ : GName) (n : Nat) :
    ownTokAuth (GF := GF) γ n ⊣⊢
      ownTokAuthDfrac γ (DFrac.own (1 : Qp).half) n ∗
      ownTokAuthDfrac γ (DFrac.own (1 : Qp).half) n := by
  have h := (ownTokAuth_fractional (GF := GF) γ n).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

theorem init (wg : Loc) (γwg : WaitGroupNames) :
    isWaitGroup (GF := GF) wg γwg (wgjN.@"wg") ∗ ownWaitGroup γwg (W32 0) ∗
      ownWaitGroupWaiters γwg 0 ⊢ |={⊤}=> ownAdder wg (W32 0) iprop(True) := by
  iintro ⟨#His, Hctr_inv, Hwaiters⟩
  imod ownApropAuth_alloc (GF := GF) with ⟨%wgApropGn, Haprop⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%wgNotDoneGn, Hadded⟩
  icases (ownTokAuth_halves wgNotDoneGn 0).1 $$ Hadded with ⟨Hadded_inv, Hadded⟩
  imod ownToks_0 (GF := GF) wgNotDoneGn with Htoks
  ihave Hfrag := ownApropFrag_0 (GF := GF) wgApropGn
  let γ : WaitGroupJoinNames := ⟨γwg, wgApropGn, wgNotDoneGn⟩
  imod inv_alloc (wgjN.@"inv") ⊤ (wgjInv (GF := GF) γ) $$ [Hctr_inv Hadded_inv Htoks Hfrag] with #Hinv
  · inext
    iexists (W32 0), 0, 0, iprop(True)
    simp only [γ]
    iframe
    isplitr
    · itrivial
    ipureintro
    exact ⟨by decide, by decide⟩
  imodintro
  simp only [ownAdder_unseal, ownAdderDef]
  iexists γ, iprop(True)
  simp only [show sint.nat (W32 0) = 0 from rfl, γ]
  iframe
  isplitr
  · ipureintro; decide
  isplitr
  · iintro _; itrivial
  unfold isWgjInv named
  isplit <;> iassumption

theorem ownAdder_wand (P' : IProp GF) (wg : Loc) (n : w32) (P : IProp GF) :
    ⊢ (P -∗ P') -∗ ownAdder wg n P -∗ ownAdder wg n P' := by
  iintro Hwand Ha
  simp only [ownAdder_unseal, ownAdderDef]
  icases Ha with ⟨%γ, %P0, Ha⟩
  iNamed Ha
  iexists γ, P0
  iframe
  isplitr
  · ipureintro; exact Hadded_pos
  isplitl
  · iintro H
    iapply Hwand
    iapply HimpliesP $$ H
  iframe #

end waitgroup_join_idiom

end join

end sync

end Perennial
end
