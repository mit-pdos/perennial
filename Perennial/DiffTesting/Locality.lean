module

/-!
# Locality of semantic differences

A justification for differential testing of a semantics by short programs
that each exercise one feature.

Two operational semantics `sem₁` and `sem₂` share a state, a map from
locations to values (`L → V`), and give each instruction a transition
relation. A *test* runs a program (a list of instructions) from an initial
state `s₀` under both semantics and compares the sets of final states; the
program *diverges* if they differ.

Each instruction comes with a *footprint* `F i`, the locations it may read or
write (for Go: the defer stack, the panic state, a variable, the heap, ...).
A semantics *respects* `F` (`Respects`) if every step leaves the locations
outside the footprint unchanged and acts on the footprint independently of
the rest of the state (`Framed`). The results, under the hypothesis that both
semantics respect the same footprints:

* `run_product`: if a program's instructions split into two groups whose
  footprints lie on opposite sides of a set of locations `C`, its runs are
  exactly the products of the runs of the two subprograms (the program
  filtered to each group).
* `diverges_split`: so a divergence of the program is a divergence of one of
  the two subprograms. Instructions that do not touch the shared state of a
  bug can be deleted from a witness.
* `minimal_connected`: every minimal divergent program (no shorter sublist
  diverges) is *connected*: any two of its instructions are joined by a chain
  of instructions of the program with pairwise overlapping footprints.
* `connected_tests_suffice`, `connected_tests_complete`: hence two semantics
  that agree on every connected program agree on every program. A test suite
  need only contain programs whose instructions interact through shared
  state.
* `diverges_pump`, `minimal_prefixes_distinct`, `run_supported`: in a minimal
  divergent program the pairs of reachable-state sets after its prefixes are
  pairwise distinct, and all those states differ from `s₀` only on the
  program's footprint. So the length of a minimal witness is bounded by the
  number of such pairs over the *interacting* state alone (for deterministic
  semantics, about `(|V| ^ |C| + 1) ^ 2` for a footprint `C`), independent of
  the rest of the state: "short" in the sense of a small model.
* `frame_hypothesis_needed`: the hypothesis that *both* semantics respect the
  footprints cannot be weakened to the reference one alone. A model step that
  writes outside its declared footprint produces a minimal divergent program
  that is not connected.

So the locality of semantics bugs reduces to a single per-instruction
property, the footprint discipline of the two semantics, which for a model
can be proved once and for all, and for the reference semantics is the
specification's statement of what each construct touches.
-/

@[expose] public section

namespace DiffTesting

open Classical

universe u v w

/-! ## Relations -/

section Rel
variable {S : Type u}

/-- Sequential composition of transition relations. -/
def Seq (R Q : S → S → Prop) : S → S → Prop := fun s s' => ∃ m, R s m ∧ Q m s'

theorem seq_assoc (R Q T : S → S → Prop) : Seq (Seq R Q) T = Seq R (Seq Q T) := by
  funext s s'; apply propext; constructor
  · rintro ⟨m', ⟨m, h1, h2⟩, h3⟩; exact ⟨m, h1, m', h2, h3⟩
  · rintro ⟨m, h1, m', h2, h3⟩; exact ⟨m', ⟨m, h1, h2⟩, h3⟩

theorem eq_seq (R : S → S → Prop) : Seq Eq R = R := by
  funext s s'; apply propext; constructor
  · rintro ⟨m, rfl, h⟩; exact h
  · intro h; exact ⟨s, rfl, h⟩

end Rel

/-! ## States, patches and frames -/

section Frame
variable {L : Type u} {V : Type v}

/-- `patch C a b` takes the locations in `C` from `a` and the rest from `b`. -/
noncomputable def patch (C : L → Prop) (a b : L → V) : L → V :=
  fun l => if C l then a l else b l

theorem patch_pos {C : L → Prop} {a b : L → V} {l : L} (h : C l) : patch C a b l = a l := by
  simp [patch, h]

theorem patch_neg {C : L → Prop} {a b : L → V} {l : L} (h : ¬C l) : patch C a b l = b l := by
  simp [patch, h]

theorem patch_compl (C : L → Prop) (a b : L → V) : patch (fun l => ¬C l) a b = patch C b a := by
  funext l; by_cases h : C l
  · rw [patch_neg (C := fun l => ¬C l) (not_not.mpr h), patch_pos h]
  · rw [patch_pos (C := fun l => ¬C l) h, patch_neg h]

/-- A transition relation `R` is framed by the location set `D`: it leaves the
locations outside `D` unchanged, and its effect on `D` does not depend on the
rest of the state (replacing the rest of the state before and after a step
gives a step). -/
structure Framed (R : (L → V) → (L → V) → Prop) (D : L → Prop) : Prop where
  frame : ∀ {s s'}, R s s' → ∀ l, ¬D l → s' l = s l
  transfer : ∀ {s s'} (t : L → V), R s s' → R (patch D s t) (patch D s' t)

theorem framed_eq (D : L → Prop) : Framed (L := L) (V := V) Eq D where
  frame := by rintro s s' rfl l -; rfl
  transfer := by rintro s s' t rfl; rfl

theorem framed_seq {R Q : (L → V) → (L → V) → Prop} {D : L → Prop}
    (hR : Framed R D) (hQ : Framed Q D) : Framed (Seq R Q) D where
  frame := by
    rintro s s' ⟨m, h1, h2⟩ l hl
    rw [hQ.frame h2 l hl, hR.frame h1 l hl]
  transfer := by
    rintro s s' t ⟨m, h1, h2⟩
    exact ⟨_, hR.transfer t h1, hQ.transfer t h2⟩

/-- A relation framed by `D` is framed by any larger set. -/
theorem framed_mono {R : (L → V) → (L → V) → Prop} {D E : L → Prop}
    (hDE : ∀ l, D l → E l) (hR : Framed R D) : Framed R E where
  frame := fun h l hl => hR.frame h l (fun hd => hl (hDE l hd))
  transfer := by
    intro s s' t h
    have key := hR.transfer (patch E s t) h
    have e1 : patch D s (patch E s t) = patch E s t := by
      funext l; by_cases hd : D l
      · rw [patch_pos hd, patch_pos (hDE l hd)]
      · rw [patch_neg hd]
    have e2 : patch D s' (patch E s t) = patch E s' t := by
      funext l; by_cases hd : D l
      · rw [patch_pos hd, patch_pos (hDE l hd)]
      · rw [patch_neg hd]
        by_cases he : E l
        · rw [patch_pos he, patch_pos he, hR.frame h l hd]
        · rw [patch_neg he, patch_neg he]
    rw [e1, e2] at key
    exact key

/-- Composing relations framed by complementary sets: the runs of `R` then
`Q` are exactly the pairs of a run of `R` and a run of `Q` from the same
state, each contributing its own side of the final state. -/
theorem seq_product {R Q : (L → V) → (L → V) → Prop} {C : L → Prop}
    (hR : Framed R C) (hQ : Framed Q (fun l => ¬C l)) (s s' : L → V) :
    Seq R Q s s' ↔ R s (patch C s' s) ∧ Q s (patch C s s') := by
  constructor
  · rintro ⟨m, h1, h2⟩
    have em : patch C s' s = m := by
      funext l; by_cases hc : C l
      · rw [patch_pos hc, hQ.frame h2 l (not_not.mpr hc)]
      · rw [patch_neg hc, hR.frame h1 l hc]
    refine ⟨em ▸ h1, ?_⟩
    have key := hQ.transfer s h2
    have e1 : patch (fun l => ¬C l) m s = s := by
      funext l; by_cases hc : C l
      · rw [patch_neg (C := fun l => ¬C l) (not_not.mpr hc)]
      · rw [patch_pos (C := fun l => ¬C l) hc, hR.frame h1 l hc]
    rw [e1, patch_compl] at key
    exact key
  · rintro ⟨h1, h2⟩
    refine ⟨_, h1, ?_⟩
    have key := hQ.transfer (patch C s' s) h2
    have e1 : patch (fun l => ¬C l) s (patch C s' s) = patch C s' s := by
      funext l; by_cases hc : C l
      · rw [patch_neg (C := fun l => ¬C l) (not_not.mpr hc)]
      · rw [patch_pos (C := fun l => ¬C l) hc, patch_neg hc]
    have e2 : patch (fun l => ¬C l) (patch C s s') (patch C s' s) = s' := by
      funext l; by_cases hc : C l
      · rw [patch_neg (C := fun l => ¬C l) (not_not.mpr hc), patch_pos hc]
      · rw [patch_pos (C := fun l => ¬C l) hc, patch_neg hc]
    rw [e1, e2] at key
    exact key

/-- Relations framed by complementary sets commute. -/
theorem seq_comm {R Q : (L → V) → (L → V) → Prop} {C : L → Prop}
    (hR : Framed R C) (hQ : Framed Q (fun l => ¬C l)) : Seq R Q = Seq Q R := by
  have hR' : Framed R (fun l => ¬¬C l) := framed_mono (fun _ h => not_not.mpr h) hR
  funext s s'; apply propext
  rw [seq_product hR hQ, seq_product hQ hR', patch_compl, patch_compl]
  exact And.comm

end Frame

/-! ## Programs and footprints -/

section Programs
variable {I : Type w} {L : Type u} {V : Type v}

/-- A semantics gives each instruction a transition relation on states. -/
abbrev Sem (I : Type w) (L : Type u) (V : Type v) := I → (L → V) → (L → V) → Prop

/-- The runs of a program: the composition of its instructions' steps. -/
def run (sem : Sem I L V) : List I → (L → V) → (L → V) → Prop
  | [] => Eq
  | i :: p => Seq (sem i) (run sem p)

theorem run_append (sem : Sem I L V) (p q : List I) :
    run sem (p ++ q) = Seq (run sem p) (run sem q) := by
  induction p with
  | nil => exact (eq_seq _).symm
  | cons i p ih => simp only [List.cons_append, run, ih, seq_assoc]

/-- The semantics respects the footprints `F`: each instruction's step is
framed by its footprint. -/
def Respects (sem : Sem I L V) (F : I → L → Prop) : Prop := ∀ i, Framed (sem i) (F i)

/-- A program whose footprints lie in `D` is framed by `D`. -/
theorem framed_run {sem : Sem I L V} {F : I → L → Prop} (h : Respects sem F)
    {D : L → Prop} {p : List I} (hp : ∀ i ∈ p, ∀ l, F i l → D l) :
    Framed (run sem p) D := by
  induction p with
  | nil => exact framed_eq D
  | cons i p ih =>
    exact framed_seq (framed_mono (hp i List.mem_cons_self) (h i))
      (ih fun j hj => hp j (List.mem_cons_of_mem i hj))

/-- The states a program can reach from `s₀` differ from `s₀` only on the
program's footprint. -/
theorem run_supported {sem : Sem I L V} {F : I → L → Prop} (h : Respects sem F)
    {p : List I} {s₀ s : L → V} (hr : run sem p s₀ s) (l : L)
    (hl : ¬∃ i ∈ p, F i l) : s l = s₀ l :=
  (framed_run (D := fun l => ∃ i ∈ p, F i l) h (fun i hi _ hil => ⟨i, hi, hil⟩)).frame hr l hl

/-- The predicate `P` on instructions separates `p` along the location set `C`:
the instructions of `p` satisfying `P` have footprints inside `C`, the others
outside `C`. -/
def Separates (F : I → L → Prop) (p : List I) (P : I → Bool) (C : L → Prop) : Prop :=
  ∀ i ∈ p, ∀ l, F i l → (P i = true ↔ C l)

theorem Separates.tail {F : I → L → Prop} {i : I} {p : List I} {P : I → Bool}
    {C : L → Prop} (hs : Separates F (i :: p) P C) : Separates F p P C :=
  fun j hj => hs j (List.mem_cons_of_mem i hj)

theorem Separates.framed_pos {sem : Sem I L V} {F : I → L → Prop} (h : Respects sem F)
    {p : List I} {P : I → Bool} {C : L → Prop} (hs : Separates F p P C) :
    Framed (run sem (p.filter P)) C :=
  framed_run h fun i hi l hl => by
    rw [List.mem_filter] at hi
    exact (hs i hi.1 l hl).mp hi.2

theorem Separates.framed_neg {sem : Sem I L V} {F : I → L → Prop} (h : Respects sem F)
    {p : List I} {P : I → Bool} {C : L → Prop} (hs : Separates F p P C) :
    Framed (run sem (p.filter (fun i => !P i))) (fun l => ¬C l) :=
  framed_run h fun i hi l hl hc => by
    rw [List.mem_filter, Bool.not_eq_true'] at hi
    have := (hs i hi.1 l hl).mpr hc
    rw [hi.2] at this
    exact Bool.false_ne_true this

/-- A separated program runs as its first group followed by its second. -/
theorem run_split {sem : Sem I L V} {F : I → L → Prop} (h : Respects sem F)
    {p : List I} {P : I → Bool} {C : L → Prop} (hs : Separates F p P C) :
    run sem p = Seq (run sem (p.filter P)) (run sem (p.filter (fun i => !P i))) := by
  induction p with
  | nil => exact (eq_seq _).symm
  | cons i p ih =>
    have ih := ih hs.tail
    cases hP : P i
    · -- `i` is in the second group: it commutes past the first.
      have hi : Framed (sem i) (fun l => ¬C l) :=
        framed_mono (fun l hl hc => by
          have := (hs i List.mem_cons_self l hl).mpr hc
          rw [hP] at this
          exact Bool.false_ne_true this) (h i)
      simp only [List.filter_cons, hP, Bool.not_false, ite_true, ite_false, Bool.false_eq_true,
        run]
      rw [ih, ← seq_assoc, ← seq_comm (hs.tail.framed_pos h) hi, seq_assoc]
    · simp only [List.filter_cons, hP, Bool.not_true, ite_true, ite_false, Bool.false_eq_true,
        run]
      rw [ih, seq_assoc]

/-- The runs of a separated program are the products of the runs of its two
groups from the same initial state. -/
theorem run_product {sem : Sem I L V} {F : I → L → Prop} (h : Respects sem F)
    {p : List I} {P : I → Bool} {C : L → Prop} (hs : Separates F p P C) (s s' : L → V) :
    run sem p s s' ↔
      run sem (p.filter P) s (patch C s' s) ∧
        run sem (p.filter (fun i => !P i)) s (patch C s s') := by
  rw [run_split h hs]
  exact seq_product (hs.framed_pos h) (hs.framed_neg h) s s'

end Programs

/-! ## Divergence and its localization -/

section Divergence
variable {I : Type w} {L : Type u} {V : Type v}
variable {sem₁ sem₂ : Sem I L V} {F : I → L → Prop}

/-- The test running `p` from `s₀` tells the two semantics apart: they reach
different sets of final states. -/
def Diverges (sem₁ sem₂ : Sem I L V) (p : List I) (s₀ : L → V) : Prop :=
  run sem₁ p s₀ ≠ run sem₂ p s₀

/-- A divergence of a separated program is a divergence of one of its two
groups, run from the same initial state. -/
theorem diverges_split (h₁ : Respects sem₁ F) (h₂ : Respects sem₂ F)
    {p : List I} {P : I → Bool} {C : L → Prop} (hs : Separates F p P C) {s₀ : L → V}
    (hd : Diverges sem₁ sem₂ p s₀) :
    Diverges sem₁ sem₂ (p.filter P) s₀ ∨ Diverges sem₁ sem₂ (p.filter (fun i => !P i)) s₀ := by
  apply Classical.byContradiction
  intro hn
  rw [not_or] at hn
  obtain ⟨hA, hB⟩ := hn
  apply hd
  funext s'
  apply propext
  rw [run_product h₁ hs, run_product h₂ hs]
  rw [Diverges, Classical.not_not] at hA hB
  rw [hA, hB]

/-- `p` diverges and no shorter sublist of it does. -/
def Minimal (sem₁ sem₂ : Sem I L V) (p : List I) (s₀ : L → V) : Prop :=
  Diverges sem₁ sem₂ p s₀ ∧
    ∀ q, q.Sublist p → q.length < p.length → ¬Diverges sem₁ sem₂ q s₀

/-- Every divergent program has a minimal divergent sublist. -/
theorem exists_minimal {p : List I} {s₀ : L → V} (hd : Diverges sem₁ sem₂ p s₀) :
    ∃ q, q.Sublist p ∧ Minimal sem₁ sem₂ q s₀ := by
  suffices ∀ n, ∀ p : List I, p.length ≤ n → Diverges sem₁ sem₂ p s₀ →
      ∃ q, q.Sublist p ∧ Minimal sem₁ sem₂ q s₀ from this _ p (Nat.le_refl _) hd
  intro n
  induction n with
  | zero =>
    intro p hp hd
    refine ⟨p, List.Sublist.refl p, hd, fun q _ hq => ?_⟩
    omega
  | succ n ih =>
    intro p hp hd
    by_cases hm : ∀ q, q.Sublist p → q.length < p.length → ¬Diverges sem₁ sem₂ q s₀
    · exact ⟨p, List.Sublist.refl p, hd, hm⟩
    · obtain ⟨q, hq, hlen, hdq⟩ : ∃ q, q.Sublist p ∧ q.length < p.length ∧
          Diverges sem₁ sem₂ q s₀ := by
        apply Classical.byContradiction
        intro hn
        exact hm fun q hq hlen hdq => hn ⟨q, hq, hlen, hdq⟩
      obtain ⟨r, hr, hmin⟩ := ih q (by omega) hdq
      exact ⟨r, hr.trans hq, hmin⟩

/-- Two instructions' footprints overlap. -/
def Overlap (F : I → L → Prop) (i j : I) : Prop := ∃ l, F i l ∧ F j l

/-- `j` is reached from `i` by a chain of instructions of `p` whose consecutive
footprints overlap. -/
inductive Linked (F : I → L → Prop) (p : List I) : I → I → Prop
  | refl (i : I) : Linked F p i i
  | step {i j k : I} : Linked F p i j → k ∈ p → Overlap F j k → Linked F p i k

/-- The instructions of `p` all interact through shared state, possibly
indirectly. -/
def Connected (F : I → L → Prop) (p : List I) : Prop :=
  ∀ i ∈ p, ∀ j ∈ p, Linked F p i j

/-- **Minimal witnesses are local.** A minimal divergent program is connected:
any two of its instructions are joined by a chain of instructions of the
program with overlapping footprints. -/
theorem minimal_connected (h₁ : Respects sem₁ F) (h₂ : Respects sem₂ F)
    {p : List I} {s₀ : L → V} (hm : Minimal sem₁ sem₂ p s₀) : Connected F p := by
  intro i hi j hj
  -- Split `p` into the instructions linked to `i` and the rest, along the
  -- locations touched by the former.
  let P : I → Bool := fun k => decide (Linked F p i k)
  let C : L → Prop := fun l => ∃ k, Linked F p i k ∧ F k l
  have hs : Separates F p P C := by
    intro k hk l hl
    constructor
    · intro hP
      exact ⟨k, of_decide_eq_true hP, hl⟩
    · rintro ⟨k', hk', hl'⟩
      exact decide_eq_true (Linked.step hk' hk ⟨l, hl', hl⟩)
  have hPi : P i = true := decide_eq_true (Linked.refl i)
  rcases diverges_split h₁ h₂ hs hm.1 with hA | hB
  · -- The linked group diverges, so by minimality it is all of `p`.
    apply Classical.byContradiction
    intro hij
    apply hm.2 _ (List.filter_sublist) _ hA
    rw [List.length_filter_lt_length_iff_exists]
    exact ⟨j, hj, fun hPj => hij (of_decide_eq_true hPj)⟩
  · -- The rest misses `i`, so it is shorter and cannot diverge.
    exfalso
    apply hm.2 _ (List.filter_sublist) _ hB
    rw [List.length_filter_lt_length_iff_exists]
    exact ⟨i, hi, by simp [hPi]⟩

/-- **Connected tests suffice.** If the two semantics agree from `s₀` on every
connected sublist of `p`, they agree on `p`. -/
theorem connected_tests_suffice (h₁ : Respects sem₁ F) (h₂ : Respects sem₂ F)
    {p : List I} {s₀ : L → V}
    (hc : ∀ q, q.Sublist p → Connected F q → ¬Diverges sem₁ sem₂ q s₀) :
    ¬Diverges sem₁ sem₂ p s₀ := by
  intro hd
  obtain ⟨q, hq, hmin⟩ := exists_minimal hd
  exact hc q hq (minimal_connected h₁ h₂ hmin) hmin.1

/-- Agreement on all connected programs is agreement on all programs. -/
theorem connected_tests_complete (h₁ : Respects sem₁ F) (h₂ : Respects sem₂ F)
    {s₀ : L → V} (hc : ∀ q, Connected F q → ¬Diverges sem₁ sem₂ q s₀) (p : List I) :
    ¬Diverges sem₁ sem₂ p s₀ :=
  connected_tests_suffice h₁ h₂ fun q _ hq => hc q hq

/-! ## Short witnesses -/

/-- Cutting a segment `v` that returns both semantics to the sets of states
they had before it preserves divergence. -/
theorem diverges_pump {u v w : List I} {s₀ : L → V}
    (e₁ : run sem₁ (u ++ v) s₀ = run sem₁ u s₀) (e₂ : run sem₂ (u ++ v) s₀ = run sem₂ u s₀) :
    Diverges sem₁ sem₂ (u ++ v ++ w) s₀ ↔ Diverges sem₁ sem₂ (u ++ w) s₀ := by
  have key : ∀ sem : Sem I L V, run sem (u ++ v) s₀ = run sem u s₀ →
      run sem (u ++ v ++ w) s₀ = run sem (u ++ w) s₀ := by
    intro sem e
    rw [run_append sem (u ++ v) w, run_append sem u w]
    funext s'
    exact propext ⟨fun ⟨m, hm, hw⟩ => ⟨m, e ▸ hm, hw⟩, fun ⟨m, hm, hw⟩ => ⟨m, e ▸ hm, hw⟩⟩
  rw [Diverges, Diverges, key sem₁ e₁, key sem₂ e₂]

/-- **Minimal witnesses are short.** In a minimal divergent program, the pairs
of state sets reached by the two semantics after distinct prefixes are
distinct. By `run_supported`, those states differ from `s₀` only on the
program's footprint, so the length of a minimal witness is less than the
number of such pairs over the footprint. -/
theorem minimal_prefixes_distinct {p : List I} {s₀ : L → V}
    (hm : Minimal sem₁ sem₂ p s₀) {a b : Nat} (hab : a < b) (hb : b ≤ p.length) :
    ¬(run sem₁ (p.take a) s₀ = run sem₁ (p.take b) s₀ ∧
      run sem₂ (p.take a) s₀ = run sem₂ (p.take b) s₀) := by
  rintro ⟨e₁, e₂⟩
  let u := p.take a
  let v := (p.take b).drop a
  let w := p.drop b
  have huv : u ++ v = p.take b := by
    show p.take a ++ (p.take b).drop a = p.take b
    conv => rhs; rw [← List.take_append_drop a (p.take b)]
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hab)]
  have hp : u ++ v ++ w = p := by rw [huv, List.take_append_drop]
  have hd : Diverges sem₁ sem₂ (u ++ w) s₀ := by
    rw [← diverges_pump (v := v) (by rw [huv]; exact e₁.symm) (by rw [huv]; exact e₂.symm), hp]
    exact hm.1
  apply hm.2 (u ++ w) _ _ hd
  · conv => rhs; rw [← List.take_append_drop b p]
    exact (List.take_sublist_take_left (Nat.le_of_lt hab)).append_right _
  · simp only [u, w, List.length_append, List.length_take, List.length_drop]
    omega

end Divergence

/-! ## The frame hypothesis is needed for both semantics

A two-location example: instruction `recover` (footprint: the panic state)
sets the panic state to `1`; instruction `arith` (footprint: a variable)
increments the variable. In the faulty model, `arith` also clears the panic
state when it is `1`, writing outside its footprint. The reference semantics
respects the footprints, and `[recover, arith]` is a minimal divergent
program, but its two instructions share no location. -/

namespace Example

/-- Instructions: `true` is `arith`, `false` is `recover`. -/
abbrev arith : Bool := true
abbrev recover : Bool := false

/-- Locations: `true` is the variable, `false` is the panic state. -/
def F : Bool → Bool → Prop := fun i l => l = i

def ref : Sem Bool Bool Nat := fun i s s' =>
  s' = if i then (fun l => if l then s l + 1 else s l) else (fun l => if l then s l else 1)

def model : Sem Bool Bool Nat := fun i s s' =>
  s' = if i then (fun l => if l then s l + 1 else if s false = 1 then 0 else s l)
    else (fun l => if l then s l else 1)

theorem ref_respects : Respects ref F := by
  intro i
  constructor
  · intro s s' h l hl
    subst h
    cases i <;> cases l <;> simp_all [F]
  · intro s s' t h
    subst h
    show _ = _
    funext l
    cases i <;> cases l <;> simp [patch, F]

def s₀ : Bool → Nat := fun _ => 0

theorem not_connected : ¬Connected F [recover, arith] := by
  intro hc
  have key : ∀ k, Linked F [recover, arith] recover k → k = recover := by
    intro k hk
    induction hk with
    | refl => rfl
    | step _ _ hov ih =>
      subst ih
      obtain ⟨l, h1, h2⟩ := hov
      simp only [F] at h1 h2
      rw [← h2, h1]
  exact Bool.noConfusion (key arith (hc recover (by simp) arith (by simp)))

theorem run_pair (sem : Sem Bool Bool Nat) (i j : Bool) (s : Bool → Nat) :
    run sem [i, j] s = fun s' => ∃ m, sem i s m ∧ sem j m s' := by
  funext s'
  simp only [run, Seq]
  exact propext ⟨fun ⟨m, h1, m', h2, h3⟩ => ⟨m, h1, h3 ▸ h2⟩,
    fun ⟨m, h1, h2⟩ => ⟨m, h1, s', h2, rfl⟩⟩

theorem diverges : Diverges ref model [recover, arith] s₀ := by
  intro h
  have hr : run ref [recover, arith] s₀ (fun l => if l then 1 else 1) := by
    rw [run_pair]
    refine ⟨fun l => if l then 0 else 1, ?_, ?_⟩
    · simp only [ref]; funext l; cases l <;> rfl
    · simp only [ref]; funext l; cases l <;> rfl
  rw [h, run_pair] at hr
  obtain ⟨m, h1, h2⟩ := hr
  simp only [model] at h1 h2
  subst h1
  have := congrFun h2 false
  simp at this

theorem singles_agree (i : Bool) : ¬Diverges ref model [i] s₀ := by
  intro h
  apply h
  funext s'
  simp only [run, Seq, ref, model, s₀]
  cases i <;> simp

theorem minimal : Minimal ref model [recover, arith] s₀ := by
  refine ⟨diverges, fun q hq hlen => ?_⟩
  match q, hq, hlen with
  | [], _, _ => exact fun h => h rfl
  | [i], _, _ => exact singles_agree i
  | _ :: _ :: _, _, hlen => simp at hlen; omega

end Example

/-- Respecting footprints in the reference semantics alone does not make
minimal witnesses connected. -/
theorem frame_hypothesis_needed :
    ∃ (sem₁ sem₂ : Sem Bool Bool Nat) (F : Bool → Bool → Prop) (p : List Bool)
      (s₀ : Bool → Nat),
      Respects sem₁ F ∧ Minimal sem₁ sem₂ p s₀ ∧ ¬Connected F p :=
  ⟨_, _, _, _, _, Example.ref_respects, Example.minimal, Example.not_connected⟩

end DiffTesting
