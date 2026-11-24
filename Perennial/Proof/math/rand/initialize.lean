/-
The proof of `math/rand.initialize'`.
-/
module

public import Perennial.Spec.math.rand.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.sync.atomic.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

theorem math.rand.initialize'.wp_proof
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_atomic_initialize : sync.atomic.initialize'.spec (GF := GF) (hG := hG)) :
    math.rand.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := sync.atomic.Pointer math.rand.Rand) _
    (sync.atomic.Pointer.ty math.rand.Rand.ty) as Hg
  -- the invariant of `globalRandGenerator`, `nil`
  imod dghostVar_alloc (GF := GF) () with ⟨%γ, Hpend⟩
  imod inv_alloc math.rand.globalRandN ⊤ iprop(∃ v : Loc,
      sync.atomic.ownPointer (T' := math.rand.Rand) (globalAddr math.rand.globalRandGenerator)
        (DFrac.own 1) v ∗ math.rand.globalState γ v) $$ [Hg Hpend] with #Hinv
  · inext
    iexists null
    isplitl [Hg]
    · rw [sync.atomic.ownPointer_unseal]; unfold sync.atomic.ownPointerDef
      rw [show ({ «_#0'» := zero_val _, «_#1'» := zero_val _, v' := null } :
        sync.atomic.Pointer math.rand.Rand) = zero_val _ from rfl]
      iexact Hg
    iunfold math.rand.globalState; ileft; iframe Hpend; ipureintro; rfl
  wp_apply wp_atomic_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hatomic⟩
  wp_apply wp_sync_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  iframe Hown
  is_pkg_init_finish
  imodintro
  iunfold math.rand.isInit
  iexists γ
  iexact Hinv

end proof

end Perennial
