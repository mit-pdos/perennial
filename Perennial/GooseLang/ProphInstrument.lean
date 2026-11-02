/-
Prophecy instrumentation of a whole program, proved sound (nothing trusted).

`withProph e` runs the program `e` under a prophecy: it creates a prophecy variable
`p`, runs `e` unchanged (as the body of a thunk, so that `e` itself is never
substituted into), resolves `p` with `e`'s result `v`, and returns `v`:

    withProph e  =  (λ t. (λ p. (λ r. (λ _. r) (ResolveProph p r)) (t ())) NewProph) (λ _. e)

A proof of `WP withProph e {{ φ }}` may therefore use a prophecy of the program's
result (`wp_new_proph`, `wp_resolve_proph`), while the program that runs is `e`:
`goose_adequacy_withProph` concludes, from such a WP, `goose_adequacy`'s three
conclusions about the real executions of `e` itself, with the same bounds `N` and
`T`.

Why it holds (no change to the semantics): every step of the wrapper (`Rec`, beta,
`NewProph`, `ResolveProph`) is a plain step of the bounded language (it uses no
fuel), and `e` runs in the evaluation context `[AppRCtx (prophRet (Val #p))]`, so
each bounded step of `e`'s execution is a step of the instrumented program
(`fill_primStep`), in the same state but for the prophecy id `p` added to
`usedProphId`, which none of `e`'s steps uses (`p` is chosen outside the final
state's used ids, and they only grow). The instrumented program's adequacy then
gives `e`'s result (after the wrapper's last steps), its threads' progress
(`notStuck_fill_inv`, and the state without `p`) and the absence of unrecovered
panics (the wrapper's frame unwinds a panic).
-/
module

public import Perennial.GooseLang.Adequacy
public import Perennial.GooseLang.CrashLang

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Language.Notation

/-! ## The wrapper -/

section wrapper
variable [GooseExts] [GoGlobalContext]

/-- The unit literal (the thunk's argument). -/
abbrev unitV : val := LitV LitUnit

/-- The return continuation: `λ r. (λ _. r) (ResolveProph p r)`, which resolves `p`
with the result `r` and returns `r`. -/
def prophRet (p : Expr) : Expr :=
  Rec BAnon "r" (App (Rec BAnon BAnon (Var "r")) (ResolveProph p (Var "r")))

/-- The wrapper: `λ t. (λ p. prophRet p (t ())) NewProph`. -/
def prophWrapper : val :=
  RecV BAnon "t" (App (Rec BAnon "p" (App (prophRet (Var "p")) (App (Var "t") (Val unitV))))
    NewProph)

/-- **The program `e` under a prophecy of its result** (see the module docstring). -/
def withProph (e : Expr) : Expr := App (Val prophWrapper) (Rec BAnon BAnon e)

/-- The context the program runs in, once the prophecy `p` exists. -/
def prophCtx (p : val) : List EctxItem := [.AppRCtx (prophRet (Val p))]

end wrapper

/-! ## Adding a prophecy id to the state -/

section state
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

theorem mem_singletonU {x y : proph_id} : x ∈ ({[y := ()]} : GSet proph_id) ↔ x = y := by
  rw [GSet.mem_iff_lookup, GMap.lookup_singleton_iff]
  by_cases h : y = x
  · subst h; simp
  · simp only [h, if_false, reduceCtorEq, false_iff]; exact fun h' => h h'.symm

theorem singletonU_comm (p q : proph_id) (U : GSet proph_id) :
    ({[q := ()]} ∪ ({[p := ()]} ∪ U) : GSet proph_id) = {[p := ()]} ∪ ({[q := ()]} ∪ U) := by
  rw [← union_assoc_L, union_comm_L {[q := ()]}, union_assoc_L]

/-- The global state with the prophecy id `p` used. -/
def GlobalState.addProph (p : proph_id) (g : GlobalState) : GlobalState :=
  { g with usedProphId := {[p := ()]} ∪ g.usedProphId }

/-- The configuration with the prophecy id `p` used. -/
def CfgState.addProph (p : proph_id) (σg : CfgState) : CfgState := (σg.1, σg.2.addProph p)

theorem extStep_addProph {ext op : String} {v : val} {σ σ' : state} {g g' : GlobalState}
    {e' : Expr} (p : proph_id) (h : extStep ext op v (σ, g) e' (σ', g')) :
    extStep ext op v (σ, g.addProph p) e' (σ', g'.addProph p) ∧
      g'.usedProphId = g.usedProphId := by
  obtain ⟨E, hE, h', s', gw', hs, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨⟨E, hE, h', s', gw', hs, rfl⟩, rfl⟩

theorem extStep_delProph {ext op : String} {v : val} {σ : state} {g : GlobalState}
    {e' : Expr} {σg' : CfgState} (p : proph_id) (h : extStep ext op v (σ, g.addProph p) e' σg') :
    ∃ σg'', extStep ext op v (σ, g) e' σg'' := by
  obtain ⟨E, hE, h', s', gw', hs, -⟩ := h
  exact ⟨_, E, hE, h', s', gw', hs, rfl⟩

/-- A base step keeps the used prophecy ids (it may add one). -/
theorem BaseStep.usedProph_mono {e : Expr} {σ σ' : state} {g g' : GlobalState}
    {κ : List Observation} {e' : Expr} {efs : List Expr}
    (h : BaseStep e (σ, g) κ e' (σ', g') efs) (q : proph_id) (hq : q ∈ g.usedProphId) :
    q ∈ g'.usedProphId := by
  generalize hs : ((σ, g) : CfgState) = s at h
  generalize hs' : ((σ', g') : CfgState) = s' at h
  cases h with
  | NewProphS p σg _ =>
    subst hs; simp only [Prod.mk.injEq] at hs'; obtain ⟨-, rfl⟩ := hs'
    exact elem_of_union_r _ hq
  | ExternalOpS ext op v e' σg σg' hst =>
    subst hs hs'
    rw [(extStep_addProph 0 hst).2]; exact hq
  | _ =>
    subst hs
    simp only [Prod.mk.injEq, setHeap, stateInitHeap] at hs'
    obtain ⟨-, rfl⟩ := hs'
    exact hq

theorem HeadStep.usedProph_mono {e : Expr} {σ σ' : state} {g g' : GlobalState}
    {κ : List Observation} {e' : Expr} {efs : List Expr}
    (h : HeadStep e (σ, g) κ e' (σ', g') efs) (q : proph_id) (hq : q ∈ g.usedProphId) :
    q ∈ g'.usedProphId := by
  generalize hs : ((σ, g) : CfgState) = s at h
  generalize hs' : ((σ', g') : CfgState) = s' at h
  cases h with
  | unwind =>
    subst hs; simp only [Prod.mk.injEq] at hs'; obtain ⟨-, rfl⟩ := hs'; exact hq
  | base _ hb =>
    subst hs hs'; exact hb.usedProph_mono q hq

/-! The heap side conditions read the local state only. -/

theorem BytesAt_snd {σ : state} {g g' : GlobalState} {l : Loc} {bs : List w8} {r : Bool}
    (h : BytesAt (σ, g) l bs r) : BytesAt (σ, g') l bs r := by
  induction bs generalizing l with
  | nil => trivial
  | cons b bs ih => exact ⟨h.1, ih h.2⟩

theorem IsFresh_snd {σ : state} {g g' : GlobalState} {l : Loc} (h : IsFresh (σ, g) l) :
    IsFresh (σ, g') l := h

theorem IsFreshBytes_snd {σ : state} {g g' : GlobalState} {w : Nat} {l : Loc}
    (h : IsFreshBytes (σ, g) w l) : IsFreshBytes (σ, g') w l := h

/-- Closes a side condition of a base step taken in another global state. -/
macro "snd_step" : tactic => `(tactic| first
  | assumption
  | exact BytesAt_snd ‹BytesAt _ _ _ _›
  | exact IsFresh_snd ‹IsFresh _ _›
  | exact IsFreshBytes_snd ‹IsFreshBytes _ _ _›
  | exact fun ⟨l, h⟩ => ‹¬∃ _, IsFresh _ _› ⟨l, IsFresh_snd h⟩
  | exact fun ⟨l, h⟩ => ‹¬∃ _, IsFreshBytes _ _ _› ⟨l, IsFreshBytes_snd h⟩)

/-- A base step whose final state does not use `p` is a base step with `p` used. -/
theorem BaseStep.addProph {e : Expr} {σ σ' : state} {g g' : GlobalState}
    {κ : List Observation} {e' : Expr} {efs : List Expr}
    (h : BaseStep e (σ, g) κ e' (σ', g') efs) (p : proph_id) (hp : p ∉ g'.usedProphId) :
    BaseStep e (σ, g.addProph p) κ e' (σ', g'.addProph p) efs := by
  generalize hs : ((σ, g) : CfgState) = s at h
  generalize hs' : ((σ', g') : CfgState) = s' at h
  cases h with
  | NewProphS q σg hq =>
    subst hs; simp only [Prod.mk.injEq] at hs'; obtain ⟨rfl, rfl⟩ := hs'
    have hpq : p ≠ q := fun h => hp (by subst h; exact elem_of_union_l _ (mem_singletonU.2 rfl))
    have hq' : q ∉ (g.addProph p).usedProphId := by
      simp only [GlobalState.addProph]; intro hm
      rcases (elem_of_union _ _ _).1 hm with hm | hm
      · exact hpq (mem_singletonU.1 hm).symm
      · exact hq hm
    have := BaseStep.NewProphS q (σ', g.addProph p) hq'
    dsimp only [GlobalState.addProph] at this ⊢
    rw [singletonU_comm] at this
    exact this
  | ExternalOpS ext op v e' σg σg' hst =>
    subst hs hs'
    exact .ExternalOpS _ _ _ _ _ _ (extStep_addProph p hst).1
  | _ =>
    subst hs
    simp only [Prod.mk.injEq, setHeap, stateInitHeap] at hs'
    obtain ⟨rfl, rfl⟩ := hs'
    constructor <;> snd_step

theorem HeadStep.addProph {e : Expr} {σ σ' : state} {g g' : GlobalState}
    {κ : List Observation} {e' : Expr} {efs : List Expr}
    (h : HeadStep e (σ, g) κ e' (σ', g') efs) (p : proph_id) (hp : p ∉ g'.usedProphId) :
    HeadStep e (σ, g.addProph p) κ e' (σ', g'.addProph p) efs := by
  generalize hs : ((σ, g) : CfgState) = s at h
  generalize hs' : ((σ', g') : CfgState) = s' at h
  cases h with
  | unwind hu =>
    subst hs; simp only [Prod.mk.injEq] at hs'; obtain ⟨rfl, rfl⟩ := hs'; exact .unwind hu
  | base hu hb =>
    subst hs hs'; exact .base hu (hb.addProph p hp)

/-- A base step with `p` used is backed by a base step without it (reducibility). -/
theorem BaseStep.delProph {e : Expr} {σ : state} {g : GlobalState} {κ : List Observation}
    {e' : Expr} {σg' : CfgState} {efs : List Expr} (p : proph_id)
    (h : BaseStep e (σ, g.addProph p) κ e' σg' efs) :
    ∃ κ' e'' σg'' efs', BaseStep e (σ, g) κ' e'' σg'' efs' := by
  generalize hs : ((σ, g.addProph p) : CfgState) = s at h
  cases h with
  | NewProphS q σg hq =>
    subst hs
    refine ⟨_, _, _, _, BaseStep.NewProphS q (σ, g) fun hm => hq ?_⟩
    simp only [GlobalState.addProph]; exact elem_of_union_r _ hm
  | ExternalOpS ext op v e' σg σg' hst =>
    subst hs
    obtain ⟨σg'', h''⟩ := extStep_delProph p hst
    exact ⟨_, _, _, _, .ExternalOpS _ _ _ _ _ _ h''⟩
  | AllocS v l σg hl => subst hs; exact ⟨_, _, _, _, .AllocS v l _ (IsFresh_snd hl)⟩
  | AllocOOMS v σg hl =>
    subst hs; exact ⟨_, _, _, _, .AllocOOMS v _ fun ⟨l, h⟩ => hl ⟨l, IsFresh_snd h⟩⟩
  | AllocBytesS w v bs l σg hv hl =>
    subst hs; exact ⟨_, _, _, _, .AllocBytesS w v bs l _ hv (IsFreshBytes_snd hl)⟩
  | AllocBytesOOMS w v bs σg hv hl =>
    subst hs
    exact ⟨_, _, _, _, .AllocBytesOOMS w v bs _ hv fun ⟨l, h⟩ => hl ⟨l, IsFreshBytes_snd h⟩⟩
  | LoadBytesS w l bs v σg hb hv =>
    subst hs; exact ⟨_, _, _, _, .LoadBytesS w l bs v _ (BytesAt_snd hb) hv⟩
  | SwapBytesS w l bs v0 v bs' σg hb hv hv' =>
    subst hs; exact ⟨_, _, _, _, .SwapBytesS w l bs v0 v bs' _ (BytesAt_snd hb) hv hv'⟩
  | AddBytesS w l bs v0 v v' bs' σg hb hv ha hv' =>
    subst hs; exact ⟨_, _, _, _, .AddBytesS w l bs v0 v v' bs' _ (BytesAt_snd hb) hv ha hv'⟩
  | CmpXchgBytesFailS w l bs vl v1 v2 σg hb hv hne =>
    subst hs; exact ⟨_, _, _, _, .CmpXchgBytesFailS w l bs vl v1 v2 _ (BytesAt_snd hb) hv hne⟩
  | CmpXchgBytesSucS w l bs vl v1 v2 bs' σg hb hv heq hv' =>
    subst hs
    exact ⟨_, _, _, _, .CmpXchgBytesSucS w l bs vl v1 v2 bs' _ (BytesAt_snd hb) hv heq hv'⟩
  | CmpXchgFailS l n vl v1 v2 σg hl hne =>
    subst hs; exact ⟨_, _, _, _, .CmpXchgFailS l n vl v1 v2 _ hl hne⟩
  | CmpXchgSucS l vl v1 v2 σg hl heq =>
    subst hs; exact ⟨_, _, _, _, .CmpXchgSucS l vl v1 v2 _ hl heq⟩
  | _ =>
    subst hs
    exact ⟨_, _, _, _, by constructor <;> snd_step⟩

theorem HeadStep.delProph {e : Expr} {σ : state} {g : GlobalState} {κ : List Observation}
    {e' : Expr} {σg' : CfgState} {efs : List Expr} (p : proph_id)
    (h : HeadStep e (σ, g.addProph p) κ e' σg' efs) :
    ∃ κ' e'' σg'' efs', HeadStep e (σ, g) κ' e'' σg'' efs' := by
  cases h with
  | unwind hu => exact ⟨_, _, _, _, .unwind hu⟩
  | base hu hb =>
    obtain ⟨κ', e'', σg'', efs', hb'⟩ := hb.delProph p
    exact ⟨_, _, _, _, .base hu hb'⟩

end state

/-! ## The bounded language -/

section bounded
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

open EctxLanguage.Notation

theorem HeadStep.addProph' {e : Expr} {σg σg' : CfgState} {κ : List Observation} {e' : Expr}
    {efs : List Expr} (h : HeadStep e σg κ e' σg' efs) (p : proph_id)
    (hp : p ∉ σg'.2.usedProphId) : HeadStep e (σg.addProph p) κ e' (σg'.addProph p) efs := by
  obtain ⟨σ, g⟩ := σg; obtain ⟨σ', g'⟩ := σg'; exact HeadStep.addProph h p hp

theorem HeadStep.usedProph_mono' {e : Expr} {σg σg' : CfgState} {κ : List Observation}
    {e' : Expr} {efs : List Expr} (h : HeadStep e σg κ e' σg' efs) (q : proph_id)
    (hq : q ∈ σg.2.usedProphId) : q ∈ σg'.2.usedProphId := by
  obtain ⟨σ, g⟩ := σg; obtain ⟨σ', g'⟩ := σg'; exact HeadStep.usedProph_mono h q hq

/-- A Go instruction's step leaves the global state as it is. -/
theorem HeadStep.counted_global {e : Expr} {σg σg' : CfgState} {κ : List Observation}
    {e' : Expr} {efs : List Expr} (hk : redexKind e = .counted) (h : HeadStep e σg κ e' σg' efs) :
    σg'.2 = σg.2 := by
  unfold redexKind at hk
  split at hk <;> try cases hk
  cases h with
  | unwind => rfl
  | base _ hb => cases hb; rfl

/-- The bounded state with the prophecy id `p` used. -/
def bAddProph (p : proph_id) (s : BcfgState) : BcfgState := (s.1.addProph p, s.2)

theorem BoundedBaseStep.addProph {e : Expr} {s : BcfgState} {κ : List Observation} {e' : Expr}
    {s' : BcfgState} {efs : List Expr} (h : BoundedBaseStep e s κ e' s' efs) (p : proph_id)
    (hp : p ∉ s'.1.2.usedProphId) :
    BoundedBaseStep e (bAddProph p s) κ e' (bAddProph p s') efs := by
  cases h with
  | step hk hh => exact .step hk (hh.addProph' p hp)
  | tick hk hh => exact .tick hk (hh.addProph' p hp)
  | stutter hk hh =>
    have hg := hh.counted_global hk
    refine .stutter hk (hh.addProph' p ?_)
    rw [hg]; exact hp
  | fork hh => exact .fork (hh.addProph' p hp)
  | forkStutter => exact .forkStutter
  | exit hh => exact .exit (hh.addProph' p hp)

theorem BoundedBaseStep.usedProph_mono {e : Expr} {s : BcfgState} {κ : List Observation}
    {e' : Expr} {s' : BcfgState} {efs : List Expr} (h : BoundedBaseStep e s κ e' s' efs)
    (q : proph_id) (hq : q ∈ s.1.2.usedProphId) : q ∈ s'.1.2.usedProphId := by
  cases h with
  | step _ hh => exact hh.usedProph_mono' q hq
  | tick _ hh => exact hh.usedProph_mono' q hq
  | stutter => exact hq
  | fork hh => exact hh.usedProph_mono' q hq
  | forkStutter => exact hq
  | exit hh => exact hh.usedProph_mono' q hq

/-- A bounded step from a state with `p` used is backed by a real head step without it. -/
theorem BoundedBaseStep.delProph {e : Expr} {s : BcfgState} {κ : List Observation} {e' : Expr}
    {s' : BcfgState} {efs : List Expr} (p : proph_id)
    (h : BoundedBaseStep e (bAddProph p s) κ e' s' efs) :
    ∃ κ' e'' σg'' efs', HeadStep e s.1 κ' e'' σg'' efs' := by
  obtain ⟨κ₁, e₁, σ₁, efs₁, hh⟩ := BoundedBaseStep.real h
  obtain ⟨⟨σ, g⟩, f⟩ := s
  exact HeadStep.delProph p hh

theorem primStep_addProph {e : Expr} {s : BcfgState} {κ : List Observation} {e' : Expr}
    {s' : BcfgState} {efs : List Expr} (h : (e, s) -<κ>-> (e', s', efs)) (p : proph_id)
    (hp : p ∉ s'.1.2.usedProphId) : (e, bAddProph p s) -<κ>-> (e', bAddProph p s', efs) := by
  obtain ⟨hb⟩ := h
  exact BaseStep.ContextStep.intro (BoundedBaseStep.addProph hb p hp)

theorem primStep_usedProph_mono {e : Expr} {s : BcfgState} {κ : List Observation} {e' : Expr}
    {s' : BcfgState} {efs : List Expr} (h : (e, s) -<κ>-> (e', s', efs)) (q : proph_id)
    (hq : q ∈ s.1.2.usedProphId) : q ∈ s'.1.2.usedProphId := by
  obtain ⟨hb⟩ := h
  exact BoundedBaseStep.usedProph_mono hb q hq

theorem nsteps_usedProph_mono {n : Nat} {ρ ρ' : List Expr × BcfgState} {κs : List Observation}
    (h : Language.NSteps n ρ κs ρ') (q : proph_id) (hq : q ∈ ρ.2.1.2.usedProphId) :
    q ∈ ρ'.2.1.2.usedProphId := by
  induction h with
  | refl => exact hq
  | cons hs _ ih =>
    obtain ⟨H, t₁, t₂⟩ := hs
    exact ih (primStep_usedProph_mono H q hq)

/-- An erased thread pool, lifted: thread `0` in the context `K`. -/
def liftPool (K : List EctxItem) : List Expr → List Expr
  | [] => []
  | e :: t => EvContext.fill K e :: t

/-- **The simulation**: an execution of the bounded language whose final state does not use
`p` is an execution with thread `0` in the context `K` and `p` used. -/
theorem nsteps_lift (K : List EctxItem) (p : proph_id) {n : Nat} {ρ ρ' : List Expr × BcfgState}
    {κs : List Observation} (h : Language.NSteps n ρ κs ρ') (hp : p ∉ ρ'.2.1.2.usedProphId) :
    Language.NSteps n (liftPool K ρ.1, bAddProph p ρ.2) κs
      (liftPool K ρ'.1, bAddProph p ρ'.2) := by
  induction h with
  | refl => exact .refl _
  | @cons n ρ₁ ρ₂ ρ₃ obs obs' hs hrest ih =>
    refine .cons ?_ (ih hp)
    have hp₂ : p ∉ ρ₂.2.1.2.usedProphId := fun hm => hp (nsteps_usedProph_mono hrest p hm)
    obtain ⟨H, t₁, t₂⟩ := hs
    have H' := primStep_addProph H p hp₂
    cases t₁ with
    | nil =>
      have H'' := EctxLanguage.fill_primStep K H'
      have := Language.Step.atomic H'' [] t₂
      simpa [liftPool] using this
    | cons e₀ t₁ =>
      have := Language.Step.atomic H' (EvContext.fill K e₀ :: t₁) t₂
      simpa [liftPool] using this

/-- A fresh prophecy id. -/
theorem exists_fresh_proph (U : GSet proph_id) : ∃ p, p ∉ U := by
  have hle : ∀ l : List Nat, ∀ x ∈ l, x ≤ l.foldr max 0 := by
    intro l; induction l with
    | nil => intro x hx; cases hx
    | cons a l ih =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih x hx) (Nat.le_max_right _ _)
  refine ⟨U.domList.foldr max 0 + 1, fun hm => ?_⟩
  have h1 : (U.domList.foldr max 0 + 1) ∈ U.domList := by
    rw [GMap.mem_dom_list]; rw [GSet.mem_iff_lookup] at hm; simp [hm]
  have := hle _ _ h1
  omega

/-- A bounded thread that is not stuck in a state with `p` used is not stuck in the real
semantics without it. -/
theorem realNotStuck_of_bounded_addProph {e : Expr} {σg : CfgState} {f : Fuel} (p : proph_id)
    (h : PrimStep.NotStuck (e, bAddProph p (σg, f))) : RealNotStuck e σg := by
  rcases h with h | ⟨κ, e', s', efs, H⟩
  · exact .inl h
  · right
    obtain ⟨hb⟩ := H
    rename_i e₁ e₂ K
    obtain ⟨κ', e'', σ'', efs', hr⟩ := BoundedBaseStep.delProph (s := (σg, f)) p hb
    exact ⟨κ', _, σ'', efs', letI := gooseRealEctxiLang; BaseStep.ContextStep.intro (K := K) hr⟩

end bounded

/-! ## The wrapper's steps -/

section steps
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

open EctxLanguage.Notation

/-! The wrapper's redexes do not unwind. -/

theorem not_unwinds_Rec (f x : Binder) (e : Expr) : ∀ q, ¬ Unwinds (Rec f x e) q := by
  intro q ⟨Ki, _, h⟩; cases Ki <;> simp_all [fillItem]

theorem not_unwinds_NewProph : ∀ q, ¬ Unwinds NewProph q := by
  intro q ⟨Ki, _, h⟩; cases Ki <;> simp_all [fillItem]

theorem not_unwinds_App_val {v1 v2 : val} (h1 : v1.isPanic = false) (h2 : v2.isPanic = false) :
    ∀ q, ¬ Unwinds (App (Val v1) (Val v2)) q := by
  intro q ⟨Ki, _, h⟩; cases Ki <;> simp_all [fillItem, val.isPanic]

theorem not_unwinds_Resolve_val {v1 v2 : val} (h1 : v1.isPanic = false)
    (h2 : v2.isPanic = false) : ∀ q, ¬ Unwinds (ResolveProph (Val v1) (Val v2)) q := by
  intro q ⟨Ki, _, h⟩; cases Ki <;> simp_all [fillItem, val.isPanic]

/-- A plain head step of a single redex in the context `Kc`, of thread `0`. -/
theorem step_plain (Kc : List EctxItem) {e1 e2 : Expr} {σg σg' : CfgState} {f : Fuel}
    {κ : List Observation} (t : List Expr) (hk : redexKind e1 = .plain)
    (hu : ∀ q, ¬ Unwinds e1 q) (hb : BaseStep e1 σg κ e2 σg' []) :
    Language.Step (EvContext.fill Kc e1 :: t, ((σg, f) : BcfgState)) κ
      (EvContext.fill Kc e2 :: t, ((σg', f) : BcfgState)) := by
  have hbb : BoundedBaseStep e1 (σg, f) κ e2 (σg', f) [] := .step hk (.base hu hb)
  have := Language.Step.atomic (BaseStep.ContextStep.intro (K := Kc) hbb) [] t
  simpa using this

/-- **The wrapper's start**: from `withProph e`, six plain steps create the prophecy `p` and
reach `e` in the context `prophCtx #p`. -/
theorem withProph_prefix (e : Expr) (σg : CfgState) (f : Fuel) (p : proph_id)
    (hp : p ∉ σg.2.usedProphId) :
    Language.NSteps 6 ([withProph e], ((σg, f) : BcfgState)) []
      ([EvContext.fill (prophCtx #p) e], bAddProph p (σg, f)) := by
  have hpv : (#p : val).isPanic = false := isPanic_intoVal p
  -- 1. the thunk
  have s1 := step_plain (σg := σg) (f := f) [.AppRCtx (Val prophWrapper)] []
    (e1 := Rec BAnon BAnon e) rfl (not_unwinds_Rec _ _ _) (BaseStep.RecS BAnon BAnon e σg)
  -- 2. the wrapper's application
  have s2 := step_plain (σg := σg) (f := f) [] []
    (e1 := App (Val prophWrapper) (Val (RecV BAnon BAnon e))) rfl (not_unwinds_App_val rfl rfl)
    (BaseStep.BetaS BAnon "t" _ (RecV BAnon BAnon e) σg)
  -- 3. the prophecy
  have s3 := step_plain (f := f)
    [.AppRCtx (Rec BAnon "p" (App (prophRet (Var "p"))
      (App (Val (RecV BAnon BAnon e)) (Val unitV))))] []
    (e1 := NewProph) rfl not_unwinds_NewProph (BaseStep.NewProphS p σg hp)
  -- 4. the binder of `p`
  have s4 := step_plain (σg := σg.addProph p) (f := f) [.AppLCtx #p hpv] []
    (e1 := Rec BAnon "p" (App (prophRet (Var "p")) (App (Val (RecV BAnon BAnon e)) (Val unitV))))
    rfl (not_unwinds_Rec _ _ _) (BaseStep.RecS _ _ _ _)
  -- 5. its application
  have s5 := step_plain (σg := σg.addProph p) (f := f) [] []
    (e1 := App (Val (RecV BAnon "p" (App (prophRet (Var "p"))
      (App (Val (RecV BAnon BAnon e)) (Val unitV))))) (Val #p))
    rfl (not_unwinds_App_val rfl hpv) (BaseStep.BetaS BAnon "p" _ #p _)
  -- 6. the thunk's call
  have s6 := step_plain (σg := σg.addProph p) (f := f) (prophCtx #p) []
    (e1 := App (Val (RecV BAnon BAnon e)) (Val unitV))
    rfl (not_unwinds_App_val rfl rfl) (BaseStep.BetaS BAnon BAnon e unitV _)
  simp only [EvContext.fill, EctxItemLanguage.fill, List.foldl, fillItem, subst', subst,
    prophRet, prophWrapper, prophCtx, id] at s1 s2 s3 s4 s5 s6 ⊢
  exact .cons s1 (.cons s2 (.cons s3 (.cons s4 (.cons s5 (.cons s6 (.refl _))))))

/-- **The wrapper's end**: from `v` (not a panic) in the context `prophCtx #p`, five plain
steps resolve `p` with `v` and return `v`. -/
theorem withProph_suffix (p : proph_id) (v : val) (hv : v.isPanic = false) (t : List Expr)
    (σg : CfgState) (f : Fuel) :
    ∃ κs, Language.NSteps 5 (EvContext.fill (prophCtx #p) (Val v) :: t, ((σg, f) : BcfgState))
      κs (Val v :: t, ((σg, f) : BcfgState)) := by
  have hpv : (#p : val).isPanic = false := isPanic_intoVal p
  have huv : (#() : val).isPanic = false := isPanic_intoVal ()
  have s1 := step_plain (σg := σg) (f := f) [.AppLCtx v hv] t
    (e1 := prophRet (Val #p)) rfl (not_unwinds_Rec _ _ _) (BaseStep.RecS _ _ _ _)
  have s2 := step_plain (σg := σg) (f := f) [] t
    (e1 := App (Val (RecV BAnon "r" (App (Rec BAnon BAnon (Var "r"))
      (ResolveProph (Val #p) (Var "r"))))) (Val v)) rfl (not_unwinds_App_val rfl hv)
    (BaseStep.BetaS BAnon "r" _ v σg)
  have s3 := step_plain (σg := σg) (f := f) [.AppRCtx (Rec BAnon BAnon (Val v))] t
    (e1 := ResolveProph (Val #p) (Val v)) rfl (not_unwinds_Resolve_val hpv hv)
    (BaseStep.ResolveProphS p v σg)
  have s4 := step_plain (σg := σg) (f := f) [.AppLCtx #() huv] t
    (e1 := Rec BAnon BAnon (Val v)) rfl (not_unwinds_Rec _ _ _) (BaseStep.RecS _ _ _ _)
  have s5 := step_plain (σg := σg) (f := f) [] t
    (e1 := App (Val (RecV BAnon BAnon (Val v))) (Val #())) rfl (not_unwinds_App_val rfl huv)
    (BaseStep.BetaS BAnon BAnon (Val v) #() σg)
  simp only [EvContext.fill, EctxItemLanguage.fill, List.foldl, fillItem, subst', subst,
    prophRet, prophCtx, id] at s1 s2 s3 s4 s5 ⊢
  exact ⟨_, .cons s1 (.cons s2 (.cons s3 (.cons s4 (.cons s5 (.refl _)))))⟩

/-- A panic in the context `prophCtx #p` unwinds it in one plain step. -/
theorem withProph_unwind (p : proph_id) (q : val) (t : List Expr) (σg : CfgState) (f : Fuel) :
    Language.NSteps 1 (EvContext.fill (prophCtx #p) (Val (PanicV q)) :: t,
      ((σg, f) : BcfgState)) [] (Val (PanicV q) :: t, ((σg, f) : BcfgState)) := by
  have hbb : BoundedBaseStep (EvContext.fill (prophCtx #p) (Val (PanicV q))) (σg, f) []
      (Val (PanicV q)) (σg, f) [] :=
    .step rfl (.unwind ⟨.AppRCtx (prophRet (Val #p)), rfl, rfl⟩)
  have := Language.Step.atomic (BaseStep.ContextStep.intro (K := []) hbb) [] t
  simp only [EvContext.fill, EctxItemLanguage.fill, List.foldl, List.nil_append,
    List.append_nil] at this
  exact .cons this (.refl _)

end steps

/-! ## The theorem -/

section adequacy
variable [GooseExts] [GooseInterp] [GooseSemantics] [GoGlobalContext] {GF : BundledGFunctors}

open EctxLanguage.Notation

/-- **Adequacy of a program from the WP of its instrumentation** (`withProph`): the
conclusions of `goose_adequacy` about the real executions of `e`, from a WP of
`withProph e`, with the same bounds `N` and `T`. Nothing is assumed about `e`. -/
theorem goose_adequacy_withProph [hPre : GooseGpreS GF] (N T : Nat) (e : Expr) (σ : state)
    (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP (withProph e) @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have hT : 1 < T := by have := Hlive.start; simp only at this; omega
  have Hadeq := goose_adequacy_blang N T (by omega) hT (withProph e) σ g φ Hinitg Hinit Hwp
  -- the erased execution in the bounded language
  obtain ⟨c, t, Hb⟩ := bounded_nsteps_of_real Hsteps (N - 1) (by omega) T (T - 2) Hlive
    (by simp only; omega)
  -- a prophecy id the execution never uses
  obtain ⟨p, hp⟩ := exists_fresh_proph σ2.2.usedProphId
  have hp0 : p ∉ g.usedProphId := fun hm => hp (nsteps_usedProph_mono Hb p hm)
  -- the instrumented execution: the prefix, then the erased one lifted
  have Hpre := withProph_prefix e (σ, g) ⟨N - 1, T - 2⟩ p hp0
  have Hlift := nsteps_lift (prophCtx #p) p Hb hp
  simp only [liftPool] at Hlift
  have Hreach := nsteps_append Hpre Hlift
  have Hrtc : ∀ {m κs' ρ}, Language.NSteps m (liftPool (prophCtx #p) t2,
      bAddProph p ((σ2, ⟨c, t⟩) : BcfgState)) κs' ρ →
      ([withProph e], (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState)) -·->ₜₚ* ρ := by
    intro m κs' ρ Hm
    exact (Language.erasedStep_nSteps _ _).mpr ⟨_, _, nsteps_append Hreach Hm⟩
  obtain ⟨σ2l, g2⟩ := σ2
  refine ⟨?_, ?_, ?_⟩
  · -- the result: the wrapper's end, then the instrumented program's result
    rintro v t2' rfl
    cases hv : v.isPanic
    · obtain ⟨κs', Hsuf⟩ := withProph_suffix p v hv t2' (σ2l, g2.addProph p) ⟨c, t⟩
      exact Hadeq.adequate_result t2' _ v (Hrtc Hsuf)
    · obtain ⟨q, rfl⟩ := val.isPanic_eq_true hv
      exact absurd (Hadeq.adequate_result t2' _ _
        (Hrtc (withProph_unwind p q t2' (σ2l, g2.addProph p) ⟨c, t⟩))) (hφ q)
  · -- progress: the lifted thread, out of the context, and without `p`
    intro e2 he2
    have Hr0 := Hrtc (.refl _)
    cases t2 with
    | nil => cases he2
    | cons e₀ rest =>
      simp only [liftPool] at Hr0
      rcases List.mem_cons.1 he2 with rfl | hrest
      · cases hval : toVal e2 with
        | some _ => exact .inl (by simp [hval])
        | none =>
          have hns := Hadeq.adequate_not_stuck _ _ _ rfl Hr0 List.mem_cons_self
          exact realNotStuck_of_bounded_addProph p
            (Language.Context.notStuck_fill_inv (K := EvContext.fill (prophCtx #p)) hns)
      · have hns := Hadeq.adequate_not_stuck _ _ _ rfl Hr0 (List.mem_cons_of_mem _ hrest)
        exact realNotStuck_of_bounded_addProph p hns
  · -- no unrecovered panic: the wrapper's frame unwinds one
    intro e2 he2 hu
    cases t2 with
    | nil => cases he2
    | cons e₀ rest =>
      simp only [liftPool] at Hreach
      have Hno := goose_no_unrecovered_panic_blang N T (by omega) hT (withProph e) σ g φ hφ
        Hinitg Hinit Hwp Hreach
      rcases List.mem_cons.1 he2 with rfl | hrest
      · exact Hno _ List.mem_cons_self (.frame (Ki := .AppRCtx (prophRet (Val #p))) rfl hu)
      · exact Hno _ (List.mem_cons_of_mem _ hrest) hu

end adequacy

end Perennial
