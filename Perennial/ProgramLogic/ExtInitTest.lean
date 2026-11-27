/-
The trusted initial states of an extension (regression test).

A toy extension, `onceExt`, has a per-node resource that can be taken once: its local
state says whether it has been taken, `take` takes it, and taking it again is stuck. Its
semantics says that a node starts with the resource not taken (`initLocal`), and a
restart gives a fresh one (`crash`, so `CrashRestartsInit` holds). The program
`take` is safe from every initial state, by `goose_adequacy_init`, whose premises
on the initial state are the semantics' (`extsInitGlobal`, `extsInitLocal`), not
the ghost state's (`once_safe`): from a state in which the resource is taken, the
program would be stuck. The initial-state predicate is satisfiable, and excludes
the taken state.
-/
module

public import Perennial.GooseLang.InitAdequacy
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace ExtInitTest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The extension -/

/-- A per-node resource that can be taken once: the local state says whether it has been
taken. -/
@[reducible] def onceExt : GooseExt where
  name := "once"
  Val := Empty
  LocalState := Bool
  GlobalState := Unit

section step
variable [GooseExts] [GoGlobalContext]

/-- `take` takes the resource if it has not been taken; otherwise it has no step. -/
inductive OnceStep : String → val → GMap Loc (NonAtomic val) → Bool → Unit → Expr →
    GMap Loc (NonAtomic val) → Bool → Unit → Prop
  | take (h : GMap Loc (NonAtomic val)) :
      OnceStep "take" #() h false () (Val #()) h true ()

end step

/-- A node starts with the resource not taken, and a restart gives a fresh one. -/
instance once_semantics : ExtSemantics onceExt where
  step := fun _ => OnceStep
  crash _ s' := s' = false
  initLocal s _ := s = false

/-- The initial states are satisfiable (`ExtSemantics.initLocal`): the resource not taken.
The predicate is an assumption about the real machine (a node starts with a fresh
resource). -/
example : ∃ g s, once_semantics.initGlobal g ∧ once_semantics.initLocal s g :=
  ⟨(), false, trivial, rfl⟩

/-- A restarted node starts afresh. -/
theorem once_crashRestartsInit : ExtSemantics.CrashRestartsInit onceExt :=
  fun _ _ _ h => h

/-! ## Its ghost state -/

/-- The ghost state of the resource: a token, owned by the program until it takes the
resource, and by the state interpretation afterwards. -/
structure OnceGS (GF : BundledGFunctors) where
  allG : AllG GF
  γ : GName

/-- The token of the resource. -/
def onceTok {GF : BundledGFunctors} (hL : OnceGS GF) : IProp GF :=
  @token GF hL.allG hL.γ

instance once_interp : ExtInterp onceExt where
  LocalGS := OnceGS
  GlobalGS _ := Unit
  localCtx hL s := bif s then onceTok hL else iprop(True)
  globalCtx _ _ := iprop(True)
  PreG := AllG
  initgP _ := True
  -- the token can be handed out only if the resource has not been taken
  initP s _ := s = false
  globalStart _ _ := iprop(True)
  localStart hL _ := onceTok hL
  global_init _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial
  local_init GF hPre s _ hs := by
    letI := hPre
    change s = false at hs
    subst hs
    imod (token_alloc (GF := GF)) with ⟨%γ, Ht⟩
    imodintro
    iexists (⟨hPre, γ⟩ : OnceGS GF)
    isplitr
    · simp only [Bool.cond_false]; itrivial
    · unfold onceTok; iexact Ht

/-- The interpretation of a taken resource is its token. -/
theorem once_ctx_true {GF : BundledGFunctors} (hL : OnceGS GF) :
    ExtInterp.localCtx (E := onceExt) hL true ⊣⊢ onceTok hL := .rfl

/-- The interpretation of a resource not taken is empty. -/
theorem once_ctx_false {GF : BundledGFunctors} (hL : OnceGS GF) :
    ExtInterp.localCtx (E := onceExt) hL false ⊣⊢ iprop(True) := .rfl

/-- The ghost state is allocated for the semantics' initial state. -/
instance once_init_compat : ExtInitCompat onceExt where
  initgP_of_init _ _ := trivial
  initP_of_init _ _ h := h

/-! ## The spec of `take` -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt onceExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

theorem wp_take :
    {{ onceTok (extLocalGS onceExt (L := L)) }} (ExternalOp onceExt.name "take" (Val #())) @ s; E
    {{ RET #(); True }} := by
  iintro %Φ Ht HΦ
  iapply wp_extStep "take" #() Φ (by simp)
  iintro %h %b %g Hh Hl Hg
  cases b with
  | true =>
    -- the resource cannot have been taken: the state interpretation would own the token
    icases (once_ctx_true _).mp $$ Hl with Hl
    unfold onceTok
    icases @token_exclusive GF (extLocalGS onceExt (L := L)).allG _ $$ Ht Hl
      with ⟨⟩
  | false =>
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro; exact ⟨_, h, true, (), OnceStep.take h⟩
    inext
    iintro %e' %h' %b' %g' %Hst _
    cases (show OnceStep _ _ _ _ _ _ _ _ _ from Hst)
    imod Hclose
    imodintro
    iframe Hh Hg
    isplitl [Ht]
    · iapply (once_ctx_true _).mpr; iexact Ht
    iapply wp_value'
    iapply HΦ
    itrivial

end spec

/-! ## A program that takes the resource, safe from every initial state -/

@[reducible] def onceExts : GooseExts := ⟨[onceExt]⟩

attribute [local instance] onceExts

@[reducible] def onceSemantics : GooseSemantics := ⟨(once_semantics, ⟨⟩)⟩

@[reducible] def onceInterp : GooseInterp := ⟨(once_interp, ⟨⟩)⟩

attribute [local instance] onceSemantics onceInterp

theorem onceExts_hasOnce : HasExt onceExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] onceExts_hasOnce

/-- The program: take the resource. -/
def takeProg [GoGlobalContext] : Expr := ExternalOp onceExt.name "take" (Val #())

/-- `takeProg` is safe on a node whose extension starts in an initial state of its
semantics: in every real execution of fewer than `N` steps along which fewer than `T`
threads are live, no thread is stuck and no thread has an unrecovered panic. Its premises
on the initial state are the trusted ones (`extsInitGlobal`, `extsInitLocal`). -/
theorem once_safe [GoGlobalContext] {GF : BundledGFunctors} [GooseGpreS GF] (N T : Nat)
    (σ : state) (g : GlobalState) (HinitG : extsInitGlobal g) (HinitL : extsInitLocal σ g)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([takeProg], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([takeProg], ((σ, g) : CfgState))) :
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧ (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have H := goose_adequacy_init (GF := GF) ⟨once_init_compat, trivial⟩ N T takeProg σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) HinitG HinitL ?_ n κs t2 σ2 Hsteps Hbound
    Hthreads Hlive
  · exact ⟨H.2.1, H.2.2⟩
  intro hG _ _ _
  iintro - Ht - -
  icases (show extsLocalStart (GF := GF) σ.world ⊢ onceTok (extLocalGS onceExt) from
    sep_elim_left) $$ Ht with Ht
  imodintro
  unfold takeProg
  iapply wp_take $$ Ht
  inext
  iintro -
  ipureintro; rfl

/-- The initial-state predicate is satisfiable: the default state is initial. -/
example : ∃ (σ : state) (g : GlobalState), extsInitGlobal g ∧ extsInitLocal σ g ∧
    σ.threads = 1 :=
  ⟨default, default, ⟨trivial, trivial⟩, ⟨rfl, trivial⟩, rfl⟩

/-- It is not trivial: a node on which the resource has been taken is not initial. -/
example (σ : state) (g : GlobalState) (h : σ.world.1 = true) : ¬ extsInitLocal σ g := by
  intro ⟨h', _⟩
  change σ.world.1 = false at h'
  rw [h] at h'
  cases h'

end ExtInitTest

end Perennial
