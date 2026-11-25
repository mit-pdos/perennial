/-
The proof of `math/rand.initialize'`.

The initializer ends with the store of the seeding table `rngCooked`, a literal of 607 `int64`
constants that goose translates as a run of 607 `let:`s; it is stepped by `wp_i64Table`
(`LetChain.lean`), not by `wp_auto`, whose `let:`-by-`let:` substitution is quadratic in the
length of the run (it exhausted 40 GB on this one).
-/
module

public import Perennial.Spec.math.rand.initialize
public import Perennial.Proof.math.rand.LetChain
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

-- the 607-entry literal is a deep term
set_option maxRecDepth 100000 in
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
  wp_apply wp_GlobalAlloc (V := GoArray w64 607) math.rand.rngCooked
    (go.ArrayType 607 go.int64) as Hcooked
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
  -- `+noauto`: `wp_auto` would step into the table's `let:`s
  wp_apply +noauto wp_sync_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  -- the store of the seeding table ends the initializer: keep an update to make its cell
  -- persistent afterwards
  iapply wp_fupd
  -- the four steps to the table's literal (`exceptionSeq`), then the run of `let:`s
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_bind (Let (BNamed "$v0") _ _)
  iapply math.rand.wp_i64Table 607 (by decide) _
    (by
      repeat' first
        | exact math.rand.ChainOk.nil
        | apply math.rand.ChainOk.cons
        | exact math.rand.I64Const.lit _
        | exact math.rand.I64Const.negLit _)
    rfl rfl
  iintro %ws %hws
  wp_auto
  ipersist Hcooked
  iframe Hown
  is_pkg_init_finish
  isplitr
  · itrivial
  imodintro
  imodintro
  iunfold math.rand.isInit
  isplitl []
  · iexists γ
    iexact Hinv
  · iexists _
    iexact Hcooked

end proof

end Perennial
