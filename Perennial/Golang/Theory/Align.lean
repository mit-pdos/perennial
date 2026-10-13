/-
Alignment of struct fields: gc places each field at an offset rounded up to its alignment
(`go.structLayout`), and a struct is aligned to the largest alignment of its fields, so a
field of an aligned struct is aligned (`field_aligned`). With the alignment that an
allocation gives (`IntoValTyped.wp_alloc`), this is how a proof shows that the location of
an atomic operation is aligned (`Aligned`).
-/
module

public import Perennial.Golang.Defn.Layout

@[expose] public section

namespace Perennial

namespace go

theorem roundUp_dvd (off al : Int) : al ∣ roundUp off al := by
  unfold roundUp; exact Int.dvd_mul_left _ _

/-- The offsets of `structLayoutAux`, entry by entry: each a multiple of its field's
alignment. -/
theorem structLayoutAux_dvd (off ma : Int) (fs : List (GoString × Int × Int)) :
    List.Forall₂ (fun e p => e.1 = p.1 ∧ e.2.2 ∣ p.2) fs (structLayoutAux off ma fs).1 := by
  induction fs generalizing off ma with
  | nil => exact List.Forall₂.nil
  | cons e fs ih =>
    obtain ⟨n, sz, al⟩ := e
    simp only [structLayoutAux]
    exact List.Forall₂.cons ⟨rfl, roundUp_dvd _ _⟩ (ih _ _)

theorem lookup_forall₂_dvd : ∀ {fs : List (GoString × Int × Int)} {ps : List (GoString × Int)},
    List.Forall₂ (fun e p => e.1 = p.1 ∧ e.2.2 ∣ p.2) fs ps → ∀ {f : GoString} {o : Int},
    ps.lookup f = some o → ∃ e ∈ fs, e.1 = f ∧ e.2.2 ∣ o
  | _, _, .nil, _, _, ho => by simp at ho
  | e :: _, (pn, po) :: _, .cons hep hrest, f, o, ho => by
    simp only [List.lookup] at ho
    split at ho
    · rename_i heq
      cases ho
      have hpn : pn = f := (beq_iff_eq.1 heq).symm
      exact ⟨e, List.mem_cons_self .., hep.1.trans hpn, hep.2⟩
    · obtain ⟨e', he', h1, h2⟩ := lookup_forall₂_dvd hrest ho
      exact ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩

theorem nodup_map_inj {α β : Type} {g : α → β} : ∀ {l : List α}, (l.map g).Nodup →
    ∀ {a b : α}, a ∈ l → b ∈ l → g a = g b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: l, hnd, a, b, ha, hb, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have ha' := List.mem_cons.1 ha
    have hb' := List.mem_cons.1 hb
    rcases ha' with ha1 | ha2
    · rcases hb' with hb1 | hb2
      · rw [ha1, hb1]
      · subst ha1; exact absurd (h ▸ List.mem_map_of_mem hb2) hnd.1
    · rcases hb' with hb1 | hb2
      · subst hb1; exact absurd (h.symm ▸ List.mem_map_of_mem ha2) hnd.1
      · exact nodup_map_inj hnd.2 ha2 hb2 h

/-- A field's offset is a multiple of its alignment. -/
theorem structFieldOffset_dvd {fs : List (GoString × Int × Int)} {f : GoString} {sz al o : Int}
    (hmem : (f, sz, al) ∈ fs) (hnd : (fs.map Prod.fst).Nodup)
    (ho : structFieldOffset fs f = some o) : al ∣ o := by
  obtain ⟨e, he, hname, hdvd⟩ := lookup_forall₂_dvd (structLayoutAux_dvd 0 1 fs) ho
  have : e = (f, sz, al) := nodup_map_inj hnd he hmem hname
  subst this
  exact hdvd

theorem lookup_isSome_of_mem' {β : Type} (a : GoString) (l : List (GoString × β))
    (h : a ∈ l.map Prod.fst) : (l.lookup a).isSome := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : a = k
    · subst hk; simp [List.lookup]
    · simp only [List.lookup, beq_false_of_ne hk]
      apply ih
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h hk
      · exact h

/-- A field of `fs` has an offset. -/
theorem structFieldOffset_isSome {fs : List (GoString × Int × Int)} {f : GoString} {sz al : Int}
    (hmem : (f, sz, al) ∈ fs) : ∃ o, structFieldOffset fs f = some o := by
  have hmem' : f ∈ (structLayoutAux 0 1 fs).1.map Prod.fst := by
    rw [structLayoutAux_names]
    exact List.mem_map_of_mem (f := Prod.fst) hmem
  have := lookup_isSome_of_mem' f _ hmem'
  cases h : (structLayoutAux 0 1 fs).1.lookup f with
  | none => rw [h] at this; cases this
  | some o => exact ⟨o, by simp only [structFieldOffset, structLayout, h]⟩

theorem pow2_dvd_of_le {a m : Int} (ha : a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 8)
    (hm : m = 1 ∨ m = 2 ∨ m = 4 ∨ m = 8) (h : a ≤ m) : a ∣ m := by
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl | rfl <;>
    first | decide | omega

theorem structLayoutAux_align (off ma : Int) (fs : List (GoString × Int × Int))
    (hma : ma = 1 ∨ ma = 2 ∨ ma = 4 ∨ ma = 8)
    (hpow : ∀ e ∈ fs, e.2.2 = 1 ∨ e.2.2 = 2 ∨ e.2.2 = 4 ∨ e.2.2 = 8) :
    let m := (structLayoutAux off ma fs).2.2
    (m = 1 ∨ m = 2 ∨ m = 4 ∨ m = 8) ∧ ma ≤ m ∧ ∀ e ∈ fs, e.2.2 ≤ m := by
  induction fs generalizing off ma with
  | nil => simp only [structLayoutAux]; exact ⟨hma, Int.le_refl _, by simp⟩
  | cons e fs ih =>
    obtain ⟨n, sz, al⟩ := e
    simp only [structLayoutAux]
    have hal := hpow _ (List.mem_cons_self ..)
    simp only at hal
    have hmax : max ma al = 1 ∨ max ma al = 2 ∨ max ma al = 4 ∨ max ma al = 8 := by
      rcases hma with rfl | rfl | rfl | rfl <;> rcases hal with rfl | rfl | rfl | rfl <;> decide
    obtain ⟨h1, h2, h3⟩ := ih (roundUp off al + sz) (max ma al) hmax
      (fun e he => hpow e (List.mem_cons_of_mem _ he))
    refine ⟨h1, by omega, ?_⟩
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · simp only; omega
    · exact h3 e he

/-- A field's alignment divides its struct's (all alignments being powers of two). -/
theorem structLayout_align_dvd {fs : List (GoString × Int × Int)} {f : GoString} {sz al : Int}
    (hmem : (f, sz, al) ∈ fs)
    (hpow : ∀ e ∈ fs, e.2.2 = 1 ∨ e.2.2 = 2 ∨ e.2.2 = 4 ∨ e.2.2 = 8) :
    al ∣ (structLayout fs).2.2 := by
  obtain ⟨h1, -, h3⟩ := structLayoutAux_align 0 1 fs (by decide) hpow
  exact pow2_dvd_of_le (hpow _ hmem) h1 (h3 _ hmem)

variable [FfiSyntax] [GoSemanticsFunctions]

/-- A field of a struct aligned to its type's alignment is aligned to its own. -/
theorem field_aligned {V : Type} {fs : List (GoString × Int × Int)} [h : StructLayout V fs]
    {f : GoString} {sz al : Int} (hmem : (f, sz, al) ∈ fs) (hnd : (fs.map Prod.fst).Nodup)
    (hpow : ∀ e ∈ fs, e.2.2 = 1 ∨ e.2.2 = 2 ∨ e.2.2 = 4 ∨ e.2.2 = 8)
    {l : Loc} (hc : l.locCar ≠ 0) (hl : typeAlign V ∣ l.locOff) :
    al ∣ (structFieldRef V f l).locOff := by
  obtain ⟨o, ho⟩ := structFieldOffset_isSome hmem
  rw [h.field_ref f o l ho hc]
  show al ∣ l.locOff + o
  have h1 : al ∣ typeAlign V := by rw [h.align]; exact structLayout_align_dvd hmem hpow
  exact Int.dvd_add (Int.dvd_trans h1 hl) (structFieldOffset_dvd hmem hnd ho)

theorem structFieldRef_car' [GoLocalContext] [GoGlobalContext] [CoreSemantics] {V : Type}
    {f : GoString} {l : Loc} (hc : l.locCar ≠ 0) {fs : List (GoString × Int × Int)}
    [h : StructLayout V fs] {sz al : Int} (hmem : (f, sz, al) ∈ fs) :
    (structFieldRef V f l).locCar ≠ 0 := by
  obtain ⟨o, ho⟩ := structFieldOffset_isSome hmem
  rw [h.field_ref f o l ho hc]
  exact hc

end go

end Perennial

namespace Perennial

set_option hygiene false in
/-- The side conditions of `go.field_aligned` for a layout list `[(f, typeSize F, typeAlign F),
…]` (as goose emits it): the alignments are powers of two. -/
macro "solve_layout_pow2" : tactic => `(tactic| (
  intro e he
  simp only [List.mem_cons, List.mem_nil_iff, _root_.or_false] at he
  repeat (first
    | exact he.elim
    | (rcases he with rfl | he; · exact go.typeAlign_pow2 _)
    | (subst he; exact go.typeAlign_pow2 _))))

/-- The names of a layout list are distinct. -/
macro "solve_layout_nodup" : tactic => `(tactic| first | (simp; done) | (simp; decide) | decide)
/-- The field is in the layout list. -/
macro "solve_layout_mem" : tactic => `(tactic| first | (simp; done) | (simp; exact ⟨rfl, rfl⟩))

end Perennial
