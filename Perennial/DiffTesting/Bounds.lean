module

public import Perennial.DiffTesting.Locality

/-!
# Bounds on the size of divergence witnesses

`Locality` shows that minimal divergent programs are footprint-connected and
that their prefix states are pairwise distinct. This file turns that into
statements about how long a test must be and where it may sit:

* `diverges_of_part`, `diverges_of_part_total`: no masking. A divergent
  subprogram of one component stays divergent when instructions of other
  components are interleaved with it, unless those block. A test that uses a
  feature among unrelated code (a function that uses `defer`/`recover` and
  also does arithmetic) exposes every bug its feature-projection exposes.
* `minimal_prefix_agree`, `minimal_reference_distinct`: before its last
  instruction a minimal witness is run identically by both semantics, and the
  *reference* semantics' state sets after its proper prefixes are pairwise
  distinct. The bound depends on the reference alone.
* `minimal_length_le`: if an abstraction `α` with `N` values is *adequate*
  (sets of states with the same abstraction admit the same divergent
  continuations), every minimal witness has length at most `N`. Concrete
  constants ("every bug of this feature shows within 7 instructions") are
  instances: they come from an adequate abstraction of the feature's state
  with that many values.
* `no_uniform_bound`: such an abstraction must depend on the semantics. For
  every `n` there are two semantics on a single location, both respecting
  footprints, whose minimal witness has `n + 1` instructions (a counter whose
  model wraps around at `n`). No bound holds independently of the
  semantics.
-/

@[expose] public section

namespace DiffTesting

open Classical

universe u v w x

/-! ## Pigeonhole -/

/-- `n` pairwise distinct values drawn from a list need a list of length at
least `n`. -/
theorem pigeonhole {A : Type x} (n : Nat) (f : Nat → A) (as : List A)
    (hmem : ∀ i, i < n → f i ∈ as) (hinj : ∀ i j, i < j → j < n → f i ≠ f j) :
    n ≤ as.length := by
  induction n generalizing as with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hn : f n ∈ as := hmem n (Nat.lt_succ_self n)
    have h := ih (as.erase (f n))
      (fun i hi => (List.mem_erase_of_ne (hinj i n hi (Nat.lt_succ_self n))).mpr
        (hmem i (Nat.lt_succ_of_lt hi)))
      (fun i j hij hj => hinj i j hij (Nat.lt_succ_of_lt hj))
    rw [List.length_erase_of_mem hn] at h
    have : 0 < as.length := List.length_pos_of_mem hn
    omega

section
variable {L : Type u} {V : Type v}

theorem patch_patch_left (C : L → Prop) (a b c : L → V) :
    patch C (patch C a b) c = patch C a c := by
  funext l; by_cases h : C l
  · rw [patch_pos h, patch_pos h, patch_pos h]
  · rw [patch_neg h, patch_neg h]

theorem patch_patch_right (C : L → Prop) (a b c : L → V) :
    patch C a (patch C b c) = patch C a c := by
  funext l; by_cases h : C l
  · rw [patch_pos h, patch_pos h]
  · rw [patch_neg h, patch_neg h, patch_neg h]

/-- `patch C a b = a` when `a` and `b` agree off `C`. -/
theorem patch_eq_left {C : L → Prop} {a b : L → V} (h : ∀ l, ¬C l → a l = b l) :
    patch C a b = a := by
  funext l; by_cases hc : C l
  · rw [patch_pos hc]
  · rw [patch_neg hc, h l hc]

/-- `patch C a b = b` when `a` and `b` agree on `C`. -/
theorem patch_eq_right {C : L → Prop} {a b : L → V} (h : ∀ l, C l → a l = b l) :
    patch C a b = b := by
  funext l; by_cases hc : C l
  · rw [patch_pos hc, h l hc]
  · rw [patch_neg hc]

end

section
variable {I : Type w} {L : Type u} {V : Type v}
variable {sem₁ sem₂ : Sem I L V} {F : I → L → Prop}

/-! ## No masking -/

/-- Runs of a separated program that combine a run `a` of the first group with
a run `b` of the second. -/
theorem run_patch {sem : Sem I L V} (h : Respects sem F) {p : List I} {P : I → Bool}
    {C : L → Prop} (hs : Separates F p P C) {s₀ a b : L → V}
    (ha : ∀ l, ¬C l → a l = s₀ l) (hb : ∀ l, C l → s₀ l = b l) :
    run sem p s₀ (patch C a b) ↔
      run sem (p.filter P) s₀ a ∧ run sem (p.filter (fun i => !P i)) s₀ b := by
  rw [run_product h hs, patch_patch_left, patch_patch_right, patch_eq_left ha,
    patch_eq_right hb]

/-- **No masking.** If the first group of a separated program diverges and the
second group has a run in each semantics, the program diverges. -/
theorem diverges_of_part (h₁ : Respects sem₁ F) (h₂ : Respects sem₂ F)
    {p : List I} {P : I → Bool} {C : L → Prop} (hs : Separates F p P C) {s₀ : L → V}
    (hd : Diverges sem₁ sem₂ (p.filter P) s₀)
    (hb₁ : ∃ b, run sem₁ (p.filter (fun i => !P i)) s₀ b)
    (hb₂ : ∃ b, run sem₂ (p.filter (fun i => !P i)) s₀ b) :
    Diverges sem₁ sem₂ p s₀ := by
  -- A final state of the first group reached by one semantics only.
  have : ∃ a, ¬(run sem₁ (p.filter P) s₀ a ↔ run sem₂ (p.filter P) s₀ a) := by
    apply Classical.byContradiction
    intro hn
    apply hd
    funext a
    exact propext (Classical.not_not.mp fun h => hn ⟨a, h⟩)
  obtain ⟨a, ha⟩ := this
  intro he
  by_cases hA : run sem₁ (p.filter P) s₀ a
  · have hA₂ : ¬run sem₂ (p.filter P) s₀ a := fun h => ha ⟨fun _ => h, fun _ => hA⟩
    obtain ⟨b, hb⟩ := hb₁
    have hoff := (hs.framed_pos h₁).frame hA
    have hon : ∀ l, C l → s₀ l = b l :=
      fun l hl => ((hs.framed_neg h₁).frame hb l (not_not.mpr hl)).symm
    have hr : run sem₁ p s₀ (patch C a b) := (run_patch h₁ hs hoff hon).mpr ⟨hA, hb⟩
    rw [he] at hr
    exact hA₂ ((run_patch h₂ hs hoff hon).mp hr).1
  · have hA₂ : run sem₂ (p.filter P) s₀ a :=
      Classical.byContradiction fun h => ha ⟨fun h' => absurd h' hA, fun h' => absurd h' h⟩
    obtain ⟨b, hb⟩ := hb₂
    have hoff := (hs.framed_pos h₂).frame hA₂
    have hon : ∀ l, C l → s₀ l = b l :=
      fun l hl => ((hs.framed_neg h₂).frame hb l (not_not.mpr hl)).symm
    have hr : run sem₂ p s₀ (patch C a b) := (run_patch h₂ hs hoff hon).mpr ⟨hA₂, hb⟩
    rw [← he] at hr
    exact hA ((run_patch h₁ hs hoff hon).mp hr).1

/-- Every instruction can take a step from every state. -/
def Total (sem : Sem I L V) : Prop := ∀ i s, ∃ s', sem i s s'

theorem Total.run {sem : Sem I L V} (h : Total sem) (p : List I) (s : L → V) :
    ∃ s', run sem p s s' := by
  induction p generalizing s with
  | nil => exact ⟨s, rfl⟩
  | cons i p ih =>
    obtain ⟨m, hm⟩ := h i s
    obtain ⟨s', hs'⟩ := ih m
    exact ⟨s', m, hm, hs'⟩

/-- For total semantics, a divergent group always shows through the rest of the
program. -/
theorem diverges_of_part_total (h₁ : Respects sem₁ F) (h₂ : Respects sem₂ F)
    (t₁ : Total sem₁) (t₂ : Total sem₂)
    {p : List I} {P : I → Bool} {C : L → Prop} (hs : Separates F p P C) {s₀ : L → V}
    (hd : Diverges sem₁ sem₂ (p.filter P) s₀) : Diverges sem₁ sem₂ p s₀ :=
  diverges_of_part h₁ h₂ hs hd (t₁.run _ _) (t₂.run _ _)

/-! ## Minimal witnesses -/

/-- Both semantics run the proper prefixes of a minimal witness alike. -/
theorem minimal_prefix_agree {p : List I} {s₀ : L → V} (hm : Minimal sem₁ sem₂ p s₀)
    {a : Nat} (ha : a < p.length) : run sem₁ (p.take a) s₀ = run sem₂ (p.take a) s₀ :=
  Classical.not_not.mp
    (hm.2 _ (List.take_sublist a p) (by rw [List.length_take]; omega))

/-- The reference semantics' state sets after distinct proper prefixes of a
minimal witness are distinct. -/
theorem minimal_reference_distinct {p : List I} {s₀ : L → V} (hm : Minimal sem₁ sem₂ p s₀)
    {a b : Nat} (hab : a < b) (hb : b < p.length) :
    run sem₁ (p.take a) s₀ ≠ run sem₁ (p.take b) s₀ := fun e =>
  minimal_prefixes_distinct hm hab (Nat.le_of_lt hb)
    ⟨e, by rw [← minimal_prefix_agree hm (Nat.lt_trans hab hb), ← minimal_prefix_agree hm hb, e]⟩

/-! ## Abstractions bound witnesses -/

/-- The states `sem` reaches by running `w` from some state of `X`. -/
def postSet (sem : Sem I L V) (X : (L → V) → Prop) (w : List I) : (L → V) → Prop :=
  fun s' => ∃ x, X x ∧ run sem w x s'

/-- Running `w` from the state set `X` tells the two semantics apart. -/
def DivergesFrom (sem₁ sem₂ : Sem I L V) (X : (L → V) → Prop) (w : List I) : Prop :=
  postSet sem₁ X w ≠ postSet sem₂ X w

theorem run_append_post (sem : Sem I L V) (u w : List I) (s₀ : L → V) :
    run sem (u ++ w) s₀ = postSet sem (run sem u s₀) w := by
  rw [run_append]; rfl

/-- An abstraction `α` of state sets is adequate for the two semantics if
state sets with the same abstraction admit the same divergent continuations.
The identity is adequate; a coarser one identifies the states that no test can
tell apart (for instance by symmetry or data independence of the
semantics). -/
def Adequate {A : Type x} (sem₁ sem₂ : Sem I L V) (α : ((L → V) → Prop) → A) : Prop :=
  ∀ X Y w, α X = α Y → DivergesFrom sem₁ sem₂ Y w → DivergesFrom sem₁ sem₂ X w

theorem adequate_id : Adequate sem₁ sem₂ (fun X : (L → V) → Prop => X) := by
  intro X Y w e h
  subst e
  exact h

/-- Under an adequate abstraction, the proper prefixes of a minimal witness
have pairwise distinct abstract states. -/
theorem minimal_abstract_distinct {A : Type x} {α : ((L → V) → Prop) → A}
    (hα : Adequate sem₁ sem₂ α) {p : List I} {s₀ : L → V} (hm : Minimal sem₁ sem₂ p s₀)
    {a b : Nat} (hab : a < b) (hb : b < p.length) :
    α (run sem₁ (p.take a) s₀) ≠ α (run sem₁ (p.take b) s₀) := by
  intro e
  have ea := minimal_prefix_agree hm (Nat.lt_trans hab hb)
  have eb := minimal_prefix_agree hm hb
  -- `p` diverges from the state set after `take b`, so `take a ++ drop b` does too.
  have hdb : DivergesFrom sem₁ sem₂ (run sem₁ (p.take b) s₀) (p.drop b) := by
    have h := hm.1
    rw [← List.take_append_drop b p] at h
    rw [Diverges, run_append_post sem₁, run_append_post sem₂, ← eb] at h
    exact h
  have hda : Diverges sem₁ sem₂ (p.take a ++ p.drop b) s₀ := by
    rw [Diverges, run_append_post sem₁, run_append_post sem₂, ← ea]
    exact hα _ _ _ e hdb
  apply hm.2 _ _ _ hda
  · conv => rhs; rw [← List.take_append_drop b p]
    exact (List.take_sublist_take_left (Nat.le_of_lt hab)).append_right _
  · simp only [List.length_append, List.length_take, List.length_drop]
    omega

/-- **Witness length bound.** If an adequate abstraction takes its values in a
list of `N` elements, every minimal witness has at most `N` instructions. -/
theorem minimal_length_le {A : Type x} {α : ((L → V) → Prop) → A}
    (hα : Adequate sem₁ sem₂ α) (as : List A) (has : ∀ X, α X ∈ as)
    {p : List I} {s₀ : L → V} (hm : Minimal sem₁ sem₂ p s₀) : p.length ≤ as.length :=
  pigeonhole p.length (fun a => α (run sem₁ (p.take a) s₀)) as (fun _ _ => has _)
    (fun _ _ hij hj => minimal_abstract_distinct hα hm hij hj)

/-- Every divergent program contains a divergent sublist of at most `N`
instructions, for an adequate abstraction with `N` values. -/
theorem short_witness {A : Type x} {α : ((L → V) → Prop) → A}
    (hα : Adequate sem₁ sem₂ α) (as : List A) (has : ∀ X, α X ∈ as)
    {p : List I} {s₀ : L → V} (hd : Diverges sem₁ sem₂ p s₀) :
    ∃ q, q.Sublist p ∧ q.length ≤ as.length ∧ Diverges sem₁ sem₂ q s₀ := by
  obtain ⟨q, hq, hm⟩ := exists_minimal hd
  exact ⟨q, hq, minimal_length_le hα as has hm, hm.1⟩

end

/-! ## No bound independent of the semantics

A single location holding a counter and a single instruction `inc`. The
reference increments; the model wraps around to `0` after `n`. Both respect
the (only) footprint, and the minimal witness is `n + 1` increments. -/

namespace Counter

def F : Unit → Unit → Prop := fun _ _ => True

def ref : Sem Unit Unit Nat := fun _ s s' => s' = fun _ => s () + 1

def model (n : Nat) : Sem Unit Unit Nat := fun _ s s' =>
  s' = fun _ => if s () = n then 0 else s () + 1

def s₀ : Unit → Nat := fun _ => 0

theorem respects_full {sem : Sem Unit Unit Nat} : Respects sem F := by
  intro i
  constructor
  · intro s s' _ l hl
    exact absurd trivial hl
  · intro s s' t h
    have e1 : patch (F i) s t = s := by funext l; exact patch_pos trivial
    have e2 : patch (F i) s' t = s' := by funext l; exact patch_pos trivial
    rw [e1, e2]
    exact h

theorem run_ref (k c : Nat) (s' : Unit → Nat) :
    run ref (List.replicate k ()) (fun _ => c) s' ↔ s' = fun _ => c + k := by
  induction k generalizing c with
  | zero => show (fun _ => c) = s' ↔ _; rw [Nat.add_zero]; exact eq_comm
  | succ k ih =>
    simp only [List.replicate_succ, run, Seq, ref]
    rw [show c + (k + 1) = (c + 1) + k by omega, ← ih (c + 1)]
    constructor
    · rintro ⟨m, hm, h⟩; rw [hm] at h; exact h
    · intro h; exact ⟨_, rfl, h⟩

theorem run_model (n k c : Nat) (hk : c + k ≤ n) (s' : Unit → Nat) :
    run (model n) (List.replicate k ()) (fun _ => c) s' ↔ s' = fun _ => c + k := by
  induction k generalizing c with
  | zero => show (fun _ => c) = s' ↔ _; rw [Nat.add_zero]; exact eq_comm
  | succ k ih =>
    have hc : c ≠ n := by omega
    simp only [List.replicate_succ, run, Seq, model, hc, ↓reduceIte]
    rw [show c + (k + 1) = (c + 1) + k by omega, ← ih (c + 1) (by omega)]
    constructor
    · rintro ⟨m, hm, h⟩; rw [hm] at h; exact h
    · intro h; exact ⟨_, rfl, h⟩

theorem list_unit (q : List Unit) : q = List.replicate q.length () :=
  List.eq_replicate_iff.mpr ⟨rfl, fun _ _ => rfl⟩

theorem agree (n k : Nat) (hk : k ≤ n) :
    ¬Diverges ref (model n) (List.replicate k ()) s₀ := by
  intro h
  apply h
  funext s'
  exact propext ((run_ref k 0 s').trans (run_model n k 0 (by omega) s').symm)

theorem diverges (n : Nat) : Diverges ref (model n) (List.replicate (n + 1) ()) s₀ := by
  intro h
  have hr : run ref (List.replicate (n + 1) ()) (fun _ => 0) (fun _ => n + 1) :=
    (run_ref (n + 1) 0 _).mpr (by funext _; omega)
  have hr' := congrFun h (fun _ => n + 1)
  change run ref _ (fun _ => 0) _ = run (model n) _ (fun _ => 0) _ at hr'
  rw [hr', List.replicate_succ', run_append] at hr
  obtain ⟨m, hm, m', hm', hl⟩ := hr
  have em := (run_model n n 0 (by omega) m).mp hm
  subst em
  simp [model] at hm'
  subst hm'
  have := congrFun hl ()
  simp at this

theorem minimal (n : Nat) : Minimal ref (model n) (List.replicate (n + 1) ()) s₀ := by
  refine ⟨diverges n, fun q _ hlen => ?_⟩
  rw [list_unit q]
  rw [List.length_replicate] at hlen
  exact agree n q.length (by omega)

end Counter

/-- No witness bound holds independently of the semantics: for every `n`, two
semantics on one location, both respecting footprints, whose minimal witness
has `n + 1` instructions. -/
theorem no_uniform_bound (n : Nat) :
    ∃ (sem₁ sem₂ : Sem Unit Unit Nat) (F : Unit → Unit → Prop) (p : List Unit)
      (s₀ : Unit → Nat),
      Respects sem₁ F ∧ Respects sem₂ F ∧ Minimal sem₁ sem₂ p s₀ ∧ p.length = n + 1 :=
  ⟨_, _, _, _, _, Counter.respects_full, Counter.respects_full, Counter.minimal n,
    List.length_replicate⟩

end DiffTesting
