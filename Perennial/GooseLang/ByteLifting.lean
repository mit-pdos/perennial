/-
Program logic for the byte memory (`ByteMem`, `Lang.lean`).

Resources:
* `a ↦∗{dq} bs`: the bytes `bs` at `a, a + 1, ...` (`bytesPointsto`), from the
  non-atomic heap `NaHeapGS w64 w8`; `a ↦∗□ bs` is persistent, and frozen bytes
  (string data, type descriptors) are only ever owned that way.
* `isBlock b sz`: `[b, b + sz)` is an allocation block (persistent), the
  provenance that `unsafe.Add` needs.
* `isFunc p v`: the func pointer `p` holds the closure `v` (persistent).

The WP lemmas cover every byte-memory primitive. Allocations loop when memory
is exhausted (`BAllocOomS`, ...), which the lemmas absorb by Löb induction, and
are not atomic for that reason; the other primitives are (`bload_atomic`, ...).
A range operation is one step on all of its bytes; its ghost update goes byte
by byte (`cells_write`, `cells_alloc`, `cells_read_lock`), which needs the
addresses of a range to be distinct (lengths below `2 ^ 64`).

The interpretation (`bmemCtx`, `Lifting.lean`) keeps persistent fragments of
every frozen byte and every interned type, so that a step may return frozen data
(`BAllocFrozenReuseS`) to a thread that never owned it.
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.ByteRange

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section resources
variable [FfiSyntax] {GF : BundledGFunctors} [AllG GF] [hB : ByteMemGS GF]

/-- The bytes `bs` at `a, a + 1, ...`. -/
def bytesPointsto (a : w64) (dq : DFrac) (bs : List w8) : IProp GF :=
  [∗list] i ↦ b ∈ bs, bytePointsto (byteAddr a i) dq b

/-- The bytes `bs` at `a`, being written (between `BPrepareWrite` and `BFinishWrite`). -/
def bytesWriting (a : w64) (bs : List w8) : IProp GF :=
  [∗list] i ↦ b ∈ bs, naHeapPointstoSt WSt (byteAddr a i) (.own 1) b

/-- The bytes `bs` at `a`, being read (between `BStartRead` and `BFinishRead`). -/
def bytesReading (a : w64) (dq : DFrac) (bs : List w8) : IProp GF :=
  [∗list] i ↦ b ∈ bs, naHeapPointstoSt (RSt 1) (byteAddr a i) dq b

/-- `[b, b + sz)` is an allocation block. -/
def isBlock (b : w64) (sz : Nat) : IProp GF :=
  ghostMapElem hB.bm_blocksName b .discard sz

/-- The func pointer `p` holds the closure `v`. -/
def isFunc (p : w64) (v : val) : IProp GF :=
  ghostMapElem hB.bm_funcsName p .discard v

end resources

scoped notation:50 a:50 " ↦∗{" dq "} " bs:50 => bytesPointsto a dq bs
scoped notation:50 a:50 " ↦∗ " bs:50 => bytesPointsto a (DFrac.own 1) bs
scoped notation:50 a:50 " ↦∗□ " bs:50 => bytesPointsto a DFrac.discard bs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

open ProofMode

theorem bytesPointsto_nil (a : w64) (dq : DFrac) :
    bytesPointsto (GF := GF) a dq [] ⊣⊢ emp := by
  unfold bytesPointsto; exact BigSepL.bigSepL_nil

theorem bytesPointsto_cons (a : w64) (dq : DFrac) (b : w8) (bs : List w8) :
    bytesPointsto (GF := GF) a dq (b :: bs) ⊣⊢
      bytePointsto a dq b ∗ bytesPointsto (a + 1) dq bs := by
  unfold bytesPointsto
  refine BigSepL.bigSepL_cons.trans ?_
  rw [byteAddr_zero]
  simp only [byteAddr_succ]
  exact .rfl

instance bytePointsto_persistent (a : w64) (b : w8) :
    Persistent (bytePointsto (GF := GF) a .discard b) := by
  unfold bytePointsto; infer_instance

instance bytesPointsto_persistent (a : w64) (bs : List w8) :
    Persistent (bytesPointsto (GF := GF) a .discard bs) := by
  unfold bytesPointsto; infer_instance

instance bytesPointsto_timeless (a : w64) (dq : DFrac) (bs : List w8) :
    Timeless (bytesPointsto (GF := GF) a dq bs) := by
  unfold bytesPointsto bytePointsto; infer_instance

instance isBlock_persistent (b : w64) (sz : Nat) : Persistent (isBlock (GF := GF) b sz) := by
  unfold isBlock; infer_instance

instance isFunc_persistent (p : w64) (v : val) : Persistent (isFunc (GF := GF) p v) := by
  unfold isFunc; infer_instance

theorem isFunc_agree (p : w64) (v1 v2 : val) :
    isFunc (GF := GF) p v1 ∗ isFunc p v2 ⊢ ⌜v1 = v2⌝ := by
  unfold isFunc
  iintro ⟨H1, H2⟩
  iapply ghostMapElem_agree $$ H1 H2

theorem bytesPointsto_agree' (a : w64) (dq1 dq2 : DFrac) (bs1 bs2 : List w8)
    (hlen : bs1.length = bs2.length) :
    ⊢ bytesPointsto (GF := GF) a dq1 bs1 -∗ bytesPointsto a dq2 bs2 -∗ ⌜bs1 = bs2⌝ := by
  induction bs1 generalizing a bs2 with
  | nil =>
    cases bs2 with
    | nil => iintro _ _; ipureintro; rfl
    | cons => simp at hlen
  | cons b bs1 ih =>
    cases bs2 with
    | nil => simp at hlen
    | cons b' bs2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      iintro H1 H2
      icases (bytesPointsto_cons a dq1 b bs1).1 $$ H1 with ⟨Hb1, H1⟩
      icases (bytesPointsto_cons a dq2 b' bs2).1 $$ H2 with ⟨Hb2, H2⟩
      unfold bytePointsto
      icombine Hb1 Hb2 gives %Hb
      icases ih (a + 1) bs2 hlen $$ H1 H2 with %Hbs
      ipureintro; rw [Hb.2, Hbs]

theorem bytesPointsto_agree (a : w64) (dq1 dq2 : DFrac) (bs1 bs2 : List w8)
    (hlen : bs1.length = bs2.length) :
    bytesPointsto (GF := GF) a dq1 bs1 ∗ bytesPointsto a dq2 bs2 ⊢ ⌜bs1 = bs2⌝ := by
  iintro ⟨H1, H2⟩
  iapply bytesPointsto_agree' a dq1 dq2 bs1 bs2 hlen $$ H1 H2

theorem bytesPointsto_persist (a : w64) (dq : DFrac) (bs : List w8) :
    bytesPointsto (GF := GF) a dq bs ⊢ |==> bytesPointsto a .discard bs := by
  induction bs generalizing a with
  | nil =>
    iintro H; imodintro; iapply (bytesPointsto_nil a _).2; itrivial
  | cons b bs ih =>
    iintro H
    icases (bytesPointsto_cons a dq b bs).1 $$ H with ⟨Hb, H⟩
    unfold bytePointsto
    imod naHeapPointsto_persist a dq b $$ Hb with Hb
    imod ih (a + 1) $$ H with H
    imodintro
    iapply (bytesPointsto_cons a _ b bs).2
    isplitl [Hb]
    · unfold bytePointsto; iexact Hb
    · iexact H

theorem bytesPointsto_app (a : w64) (dq : DFrac) (bs1 bs2 : List w8) :
    bytesPointsto (GF := GF) a dq (bs1 ++ bs2) ⊣⊢
      bytesPointsto a dq bs1 ∗ bytesPointsto (byteAddr a bs1.length) dq bs2 := by
  unfold bytesPointsto
  refine BigSepL.bigSepL_append.trans ?_
  have : ∀ k, byteAddr a (k + bs1.length) = byteAddr (byteAddr a bs1.length) k := by
    intro k; apply BitVec.eq_of_toNat_eq
    simp only [byteAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [this]
  exact .rfl

/-! ### Atomicity

The byte-memory primitives other than the allocations (which may loop when
memory is exhausted) are atomic. -/

instance bload_atomic (a : Language.Atomicity) (v : val) :
    Language.Atomic a (BLoad (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h <;> rfl)
    (by intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl)

instance bprepare_write_atomic (a : Language.Atomicity) (v : val) :
    Language.Atomic a (BPrepareWrite (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h <;> rfl)
    (by intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl)

instance bfreeze_atomic (a : Language.Atomicity) (v : val) :
    Language.Atomic a (BFreeze (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h <;> rfl)
    (by intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl)

instance func_load_atomic (a : Language.Atomicity) (v : val) :
    Language.Atomic a (FuncLoad (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h <;> rfl)
    (by intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl)

instance bfinish_write_atomic (a : Language.Atomicity) (v1 v2 : val) :
    Language.Atomic a (BFinishWrite (Val v1) (Val v2)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h <;> rfl)
    (by intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl)

instance bswap_atomic (a : Language.Atomicity) (v1 v2 : val) :
    Language.Atomic a (BSwap (Val v1) (Val v2)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h <;> rfl)
    (by intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl)

instance unsafe_add_atomic (a : Language.Atomicity) (v1 v2 : val) :
    Language.Atomic a (UnsafeAdd (Val v1) (Val v2)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h <;> rfl)
    (by intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl)

/-! ### Cells and ranges -/

/-- Full ownership of the cells `cs` at `a, a + 1, ...`, with their lock states. -/
def cellsOwn (a : w64) : List ByteCell → IProp GF
  | [] => emp
  | c :: cs => iprop(naHeapPointstoSt (btls c.1) a (.own 1) c.2 ∗ cellsOwn (a + 1) cs)

theorem bytesPointsto_cellsOwn (a : w64) (bs : List w8) :
    bytesPointsto (GF := GF) a (.own 1) bs ⊣⊢ cellsOwn a (bs.map (.Rd 0, ·)) := by
  induction bs generalizing a with
  | nil => exact bytesPointsto_nil a _
  | cons b bs ih =>
    refine (bytesPointsto_cons a _ b bs).trans ?_
    simp only [List.map_cons, cellsOwn]
    exact sep_congr .rfl (ih (a + 1))

theorem bytesPointsto_cellsOwn' (md : ByteMode) (hmd : btls md = RSt 0) (a : w64)
    (bs : List w8) :
    bytesPointsto (GF := GF) a (.own 1) bs ⊣⊢ cellsOwn a (bs.map (md, ·)) := by
  induction bs generalizing a with
  | nil => exact bytesPointsto_nil a _
  | cons b bs ih =>
    refine (bytesPointsto_cons a _ b bs).trans ?_
    simp only [List.map_cons, cellsOwn, hmd]
    exact sep_congr .rfl (ih (a + 1))

theorem bytesWriting_cons (a : w64) (b : w8) (bs : List w8) :
    bytesWriting (GF := GF) a (b :: bs) ⊣⊢
      naHeapPointstoSt WSt a (.own 1) b ∗ bytesWriting (a + 1) bs := by
  unfold bytesWriting
  refine BigSepL.bigSepL_cons.trans ?_
  rw [byteAddr_zero]
  simp only [byteAddr_succ]
  exact .rfl

theorem bytesWriting_cellsOwn (a : w64) (bs : List w8) :
    bytesWriting (GF := GF) a bs ⊣⊢ cellsOwn a (bs.map (.Wr, ·)) := by
  induction bs generalizing a with
  | nil => unfold bytesWriting; exact BigSepL.bigSepL_nil
  | cons b bs ih =>
    refine (bytesWriting_cons a b bs).trans ?_
    simp only [List.map_cons, cellsOwn]
    exact sep_congr .rfl (ih (a + 1))

instance bytesWriting_timeless (a : w64) (bs : List w8) :
    Timeless (bytesWriting (GF := GF) a bs) := by
  unfold bytesWriting; infer_instance

theorem writing_lookup (m : GMap w64 ByteCell) (a : w64) (bs : List w8) :
    ⊢ naHeapCtx btls m -∗ bytesWriting (GF := GF) a bs -∗
      ⌜LookupRange m a (bs.map (.Wr, ·))⌝ := by
  induction bs generalizing a with
  | nil => iintro _ _; ipureintro; trivial
  | cons b bs ih =>
    iintro Hσ H
    icases (bytesWriting_cons a b bs).1 $$ H with ⟨Hb, H⟩
    icases naHeapPointsto_lookup_1 btls m a WSt b $$ Hσ Hb with %⟨lk, Hlk, Hst⟩
    icases ih (a + 1) $$ Hσ H with %Hcs
    ipureintro
    cases lk <;> simp_all [btls, LookupRange]

/-- The fragments of fractional ownership give a readable range. -/
theorem bytes_lookup (m : GMap w64 ByteCell) (a : w64) (dq : DFrac) (bs : List w8) :
    ⊢ naHeapCtx btls m -∗ bytesPointsto (GF := GF) a dq bs -∗
      ⌜∃ cs, LookupRange m a cs ∧ cs.map Prod.snd = bs ∧ ∀ c ∈ cs, c.1.Readable⌝ := by
  induction bs generalizing a with
  | nil => iintro _ _; ipureintro; exact ⟨[], trivial, rfl, by simp⟩
  | cons b bs ih =>
    iintro Hσ H
    icases (bytesPointsto_cons a dq b bs).1 $$ H with ⟨Hb, H⟩
    unfold bytePointsto naHeapPointsto
    icases naHeapPointsto_lookup btls m a (RSt 0) dq b $$ Hσ Hb with %⟨lk, n, Hlk, Hst⟩
    icases ih (a + 1) $$ Hσ H with %⟨cs, Hcs, Hmap, Hrd⟩
    ipureintro
    refine ⟨(lk, b) :: cs, ⟨Hlk, Hcs⟩, by simp [Hmap], ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · cases lk <;> simp_all [btls, ByteMode.Readable]
    · exact Hrd c hc

/-- Full ownership gives a range of unfrozen cells with no readers: a frozen
byte has a persistent fragment in the interpretation. -/
theorem bytes_lookup_1 (m : GMap w64 ByteCell) (a : w64) (bs : List w8) :
    ⊢ naHeapCtx btls m -∗
      (□ ∀ a b n, ⌜m !! a = some (.Frozen n, b)⌝ → bytePointsto (GF := GF) a .discard b) -∗
      bytesPointsto a (.own 1) bs -∗
      ⌜∃ cs, LookupRange m a cs ∧ cs.map Prod.snd = bs ∧ ∀ c ∈ cs, c.1 = .Rd 0⌝ := by
  induction bs generalizing a with
  | nil => iintro _ _ _; ipureintro; exact ⟨[], trivial, rfl, by simp⟩
  | cons b bs ih =>
    iintro Hσ #Hfr H
    icases (bytesPointsto_cons a _ b bs).1 $$ H with ⟨Hb, H⟩
    icases ih (a + 1) $$ Hσ Hfr H with %⟨cs, Hcs, Hmap, Hrd⟩
    unfold bytePointsto naHeapPointsto
    icases naHeapPointsto_lookup_1 btls m a (RSt 0) b $$ Hσ Hb with %⟨lk, Hlk, Hst⟩
    cases lk with
    | Wr => simp [btls] at Hst
    | Rd n =>
      simp only [btls_Rd, LockState.RSt.injEq] at Hst; subst Hst
      ipureintro
      refine ⟨(.Rd 0, b) :: cs, ⟨Hlk, Hcs⟩, by simp [Hmap], ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rfl
      · exact Hrd c hc
    | Frozen n =>
      simp only [btls_Frozen, LockState.RSt.injEq] at Hst; subst Hst
      ihave Hp := Hfr $$ %a %b %0 %Hlk
      have Hw : naHeapPointstoSt (GF := GF) (RSt 0) a (.own 1) b ⊢
          naHeapPointstoSt (RSt 0) a .discard b -∗ ⌜False⌝ :=
        wand_intro ((naHeapPointstoSt_valid_2 _ _ a _ _ b b).trans (pure_mono fun h => by
          have := h.1; rw [DFrac.valid_own_op_discard] at this; simp at this))
      icases Hw $$ Hb Hp with %Hf
      exact Hf.elim

/-- Writing a range of fully owned cells. -/
theorem cells_write (m : GMap w64 ByteCell) (a : w64) (cs cs' : List ByteCell)
    (hlen : cs'.length = cs.length) :
    ⊢ naHeapCtx (GF := GF) btls m -∗ cellsOwn a cs ==∗
      naHeapCtx btls (insertRange m a cs') ∗ cellsOwn a cs' := by
  induction cs generalizing a cs' with
  | nil =>
    cases cs' with
    | nil => iintro Hσ _; imodintro; simp only [insertRange, cellsOwn]; iframe
    | cons => simp at hlen
  | cons c cs ih =>
    cases cs' with
    | nil => simp at hlen
    | cons c' cs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [cellsOwn]
      iintro Hσ ⟨Hc, H⟩
      imod ih (a + 1) cs' hlen $$ Hσ H with ⟨Hσ, H⟩
      imod na_heap_write_vs btls (insertRange m (a + 1) cs') c.1 c'.1 a c.2 c'.2 $$ Hσ Hc
        with ⟨Hσ, Hc⟩
      imodintro
      simp only [insertRange, cellsOwn]
      iframe

/-- Allocating a fresh range. -/
theorem cells_alloc (m : GMap w64 ByteCell) (a : w64) (cs : List ByteCell)
    (hfree : ∀ i < cs.length, m !! byteAddr a i = none) (hlen : cs.length ≤ 2 ^ 64)
    (hrd : ∀ c ∈ cs, btls c.1 = RSt 0) :
    ⊢ naHeapCtx (GF := GF) btls m ==∗
      naHeapCtx btls (insertRange m a cs) ∗ bytesPointsto a (.own 1) (cs.map Prod.snd) := by
  induction cs generalizing a with
  | nil =>
    iintro Hσ; imodintro; simp only [insertRange, List.map_nil]; iframe
    iapply (bytesPointsto_nil a _).2; itrivial
  | cons c cs ih =>
    simp only [List.length_cons] at hlen
    have hfree' : ∀ i < cs.length, m !! byteAddr (a + 1) i = none := by
      intro i hi; rw [byteAddr_succ]; exact hfree (i + 1) (by simp; omega)
    have hnone : insertRange m (a + 1) cs !! a = none := by
      rw [lookup_insertRange_of_ne]
      · simpa [byteAddr_zero] using hfree 0 (by simp)
      · intro i hi h
        have h' : byteAddr a (i + 1) = byteAddr a 0 := by rw [byteAddr_zero, ← byteAddr_succ]; exact h
        have := byteAddr_inj (by omega) (by omega) h'
        omega
    iintro Hσ
    imod ih (a + 1) hfree' (by omega) (fun c' hc' => hrd c' (by simp [hc'])) $$ Hσ
      with ⟨Hσ, H⟩
    imod na_heap_alloc btls (insertRange m (a + 1) cs) a c.2 c.1 hnone (hrd c (by simp)) $$ Hσ
      with ⟨Hσ, Hc⟩
    imodintro
    simp only [insertRange, List.map_cons]
    iframe Hσ
    iapply (bytesPointsto_cons a _ c.2 (cs.map Prod.snd)).2
    unfold bytePointsto
    iframe

/-- A cell frozen after writing `cs` was frozen before, or is one of `cs`. -/
theorem frozen_insertRange_cases {m : GMap w64 ByteCell} {a x : w64} {cs : List ByteCell}
    {n : Nat} {b : w8} (hlen : cs.length ≤ 2 ^ 64)
    (h : insertRange m a cs !! x = some (.Frozen n, b)) :
    m !! x = some (.Frozen n, b) ∨
      ∃ i, ∃ hi : i < cs.length, x = byteAddr a i ∧ cs[i] = (.Frozen n, b) := by
  by_cases hin : ∃ i < cs.length, x = byteAddr a i
  · obtain ⟨i, hi, rfl⟩ := hin
    rw [lookup_insertRange_getElem m a cs hlen i hi] at h
    exact .inr ⟨i, hi, rfl, Option.some.inj h⟩
  · rw [lookup_insertRange_of_ne m a cs x (fun i hi he => hin ⟨i, hi, he.symm⟩)] at h
    exact .inl h

/-- The frozen bytes after writing cells none of which is frozen. -/
theorem frozen_insertRange_unfrozen (m : GMap w64 ByteCell) (a : w64) (cs : List ByteCell)
    (hlen : cs.length ≤ 2 ^ 64) (hcs : ∀ c ∈ cs, ¬ c.1.IsFrozen) :
    (□ ∀ a b n, ⌜m !! a = some (.Frozen n, b)⌝ → bytePointsto (GF := GF) a .discard b) ⊢
    (□ ∀ x b n, ⌜insertRange m a cs !! x = some (.Frozen n, b)⌝ →
      bytePointsto (GF := GF) x .discard b) := by
  iintro #H
  imodintro
  iintro %x %b %n %Hx
  rcases frozen_insertRange_cases hlen Hx with Hx | ⟨i, hi, _, hc⟩
  · iapply H $$ %x %b %n %Hx
  · exact absurd (hcs _ (List.getElem_mem hi)) (by rw [hc]; simp [ByteMode.IsFrozen])

/-- The frozen bytes after writing frozen cells that we own persistently. -/
theorem frozen_insertRange_frozen (m : GMap w64 ByteCell) (a : w64) (bs : List w8) (k : Nat)
    (hlen : bs.length ≤ 2 ^ 64) :
    (□ ∀ a b n, ⌜m !! a = some (.Frozen n, b)⌝ → bytePointsto (GF := GF) a .discard b) ⊢
    bytesPointsto a .discard bs -∗
    (□ ∀ x b n, ⌜insertRange m a (bs.map (.Frozen k, ·)) !! x = some (.Frozen n, b)⌝ →
      bytePointsto (GF := GF) x .discard b) := by
  iintro #H #Hbs
  imodintro
  iintro %x %b %n %Hx
  rcases frozen_insertRange_cases (by simpa using hlen) Hx with Hx | ⟨i, hi, rfl, hc⟩
  · iapply H $$ %x %b %n %Hx
  · simp only [List.getElem_map, Prod.mk.injEq] at hc
    unfold bytesPointsto
    have hi' : i < bs.length := by simpa using hi
    iapply (BigSepL.bigSepL_lookup (Φ := fun i b => bytePointsto (byteAddr a i) .discard b)
      (i := i) (x := b) (by rw [List.getElem?_eq_getElem hi', hc.2])) $$ Hbs

/-- Rewriting a range keeps the static bytes when no frozen cell of it changes
its byte or stops being frozen. -/
theorem staticAgree_insertRange {m : ByteMem} {a : w64} {old new : List ByteCell}
    (h : StaticAgree m) (hcs : LookupRange m.bytes a old) (hlen : old.length < 2 ^ 64)
    (hnew : new.length = old.length)
    (hf : ∀ i (hi : i < old.length) (hi' : i < new.length), old[i].1.IsFrozen →
      ∃ n, new[i] = (.Frozen n, old[i].2)) :
    StaticAgree (m.writeRange a new) := by
  intro x b hx
  obtain ⟨n, hn⟩ := h x b hx
  show ∃ n, insertRange m.bytes a new !! x = some (.Frozen n, b)
  by_cases hin : ∃ i < new.length, x = byteAddr a i
  · obtain ⟨i, hi, rfl⟩ := hin
    have hi0 : i < old.length := hnew ▸ hi
    have hold := (lookupRange_iff _ _ _).1 hcs i hi0
    rw [hn] at hold
    have hold' : old[i] = (.Frozen n, b) := (Option.some.inj hold).symm
    obtain ⟨n', hn'⟩ := hf i hi0 hi (by rw [hold']; trivial)
    refine ⟨n', ?_⟩
    rw [lookup_insertRange_getElem _ _ _ (by omega) i hi, hn', hold']
  · refine ⟨n, ?_⟩
    rw [lookup_insertRange_of_ne _ _ _ _ (fun i hi he => hin ⟨i, hi, he.symm⟩)]; exact hn

/-- `staticAgree_insertRange`'s side condition when no old cell is frozen. -/
theorem frozenKept_of_notFrozen {old new : List ByteCell} (hnf : ∀ c ∈ old, ¬ c.1.IsFrozen) :
    ∀ i (hi : i < old.length) (hi' : i < new.length), old[i].1.IsFrozen →
      ∃ n, new[i] = (.Frozen n, old[i].2) :=
  fun i hi _ hfz => absurd hfz (hnf _ (List.getElem_mem hi))

/-- `staticAgree_insertRange`'s side condition for a cellwise update. -/
theorem frozenKept_of_map {old : List ByteCell} (f : ByteCell → ByteCell)
    (hf : ∀ c, c.1.IsFrozen → ∃ n, f c = (.Frozen n, c.2)) :
    ∀ i (hi : i < old.length) (hi' : i < (old.map f).length), old[i].1.IsFrozen →
      ∃ n, (old.map f)[i] = (.Frozen n, old[i].2) := by
  intro i hi hi' hfz; simp only [List.getElem_map]; exact hf _ hfz

/-- Allocating a fresh range keeps the static bytes. -/
theorem staticAgree_allocRange {m : ByteMem} {a : w64} {cs : List ByteCell} (h : StaticAgree m)
    (hfree : ∀ i < cs.length, m.bytes !! byteAddr a i = none) :
    StaticAgree (m.allocRange a cs) := by
  intro x b hx
  obtain ⟨n, hn⟩ := h x b hx
  refine ⟨n, ?_⟩
  show insertRange m.bytes a cs !! x = _
  rw [lookup_insertRange_of_ne]
  · exact hn
  · intro i hi he; rw [← he, hfree i hi] at hn; cases hn

theorem bmemWf_writeRange {m : ByteMem} (a : w64) (cs : List ByteCell) (h : BmemWf m)
    (hs : StaticAgree (m.writeRange a cs)) : BmemWf (m.writeRange a cs) :=
  ⟨fun b sz hb => ⟨(h.1 b sz hb).1, fun i hi =>
      insertRange_isSome _ _ _ _ ((h.1 b sz hb).2 i hi)⟩, hs⟩

theorem bmemWf_allocRange {m : ByteMem} (a : w64) (cs : List ByteCell) (h : BmemWf m)
    (hlen : cs.length ≤ 2 ^ 64) (hfree : ∀ i < cs.length, m.bytes !! byteAddr a i = none) :
    BmemWf (m.allocRange a cs) := by
  refine ⟨fun b sz hb => ?_, staticAgree_allocRange h.2 hfree⟩
  simp only [addBlock] at hb ⊢
  split at hb
  · exact ⟨(h.1 b sz hb).1, fun i hi => insertRange_isSome _ _ _ _ ((h.1 b sz hb).2 i hi)⟩
  · rename_i hn
    rw [GMap.lookup_insert_eq_iff] at hb
    split at hb
    · subst_vars; cases hb
      refine ⟨by omega, fun i hi => ?_⟩
      rw [lookup_insertRange_getElem _ _ _ hlen i hi]; rfl
    · exact ⟨(h.1 b sz hb).1, fun i hi => insertRange_isSome _ _ _ _ ((h.1 b sz hb).2 i hi)⟩

/-- A fresh range does not start at a block or a type descriptor. -/
theorem freshRange_blocks_none {m : ByteMem} {a : w64} {n : Nat} (h : BmemWf m)
    (hf : FreshRange m.bytes a n) (hn : n ≠ 0) : m.blocks !! a = none := by
  cases hb : m.blocks !! a with
  | none => rfl
  | some sz =>
    have := (h.1 a sz hb).2 0 (h.1 a sz hb).1
    have hfr := freshRange_lookup hf (i := 0) (by omega)
    rw [byteAddr_zero] at this hfr
    rw [hfr] at this; cases this

theorem lookupRange_unique {m : GMap w64 ByteCell} {a : w64} {cs cs' : List ByteCell}
    (h : LookupRange m a cs) (h' : LookupRange m a cs') (hlen : cs.length = cs'.length) :
    cs = cs' := by
  induction cs generalizing a cs' with
  | nil => cases cs' <;> simp_all
  | cons c cs ih =>
    cases cs' with
    | nil => simp at hlen
    | cons c' cs' =>
      obtain ⟨h1, h2⟩ := h; obtain ⟨h1', h2'⟩ := h'
      rw [h1] at h1'; cases h1'
      rw [ih h2 h2' (by simpa using hlen)]

theorem notFrozen_map {α : Type} (l : List α) (f : α → ByteCell)
    (hf : ∀ x, ¬ (f x).1.IsFrozen) : ∀ c ∈ l.map f, ¬ c.1.IsFrozen := by
  intro c hc; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hc; exact hf x

theorem bmemCtx_eq (m : ByteMem) :
    bmemCtx (GF := GF) m ⊣⊢ iprop(naHeapCtx btls m.bytes ∗
      (□ ∀ a b n, ⌜m.bytes !! a = some (.Frozen n, b)⌝ → bytePointsto a .discard b) ∗
      ghostMapAuth L.goose_bmemGS.bm_blocksName 1 m.blocks ∗
      ghostMapAuth L.goose_bmemGS.bm_funcsName 1 m.funcs ∗
      ⌜BmemWf m⌝) := .rfl

theorem intoVal_w64_inj {a b : w64} (h : (#a : val) = #b) : a = b :=
  GoGlobalContext.intoVal_inj_w64 h

/-! ### Non-atomic reads -/

instance bytesReading_timeless (a : w64) (dq : DFrac) (bs : List w8) :
    Timeless (bytesReading (GF := GF) a dq bs) := by
  unfold bytesReading; infer_instance

theorem bytesReading_cons (a : w64) (dq : DFrac) (b : w8) (bs : List w8) :
    bytesReading (GF := GF) a dq (b :: bs) ⊣⊢
      naHeapPointstoSt (RSt 1) a dq b ∗ bytesReading (a + 1) dq bs := by
  unfold bytesReading
  refine BigSepL.bigSepL_cons.trans ?_
  rw [byteAddr_zero]
  simp only [byteAddr_succ]
  exact .rfl

theorem bytesReading_nil (a : w64) (dq : DFrac) :
    bytesReading (GF := GF) a dq [] ⊣⊢ emp := by
  unfold bytesReading; exact BigSepL.bigSepL_nil

/-- `a` is not among `a + 1, ..., a + n`. -/
theorem lookup_insertRange_succ_self (m : GMap w64 ByteCell) (a : w64) (cs : List ByteCell)
    (hlen : cs.length < 2 ^ 64) : insertRange m (a + 1) cs !! a = m !! a := by
  apply lookup_insertRange_of_ne
  intro i hi h
  have h' : byteAddr a (i + 1) = byteAddr a 0 := by rw [byteAddr_zero, ← byteAddr_succ]; exact h
  have := byteAddr_inj (by omega) (by omega) h'
  omega

theorem readable_btls {md : ByteMode} (h : md.Readable) : ∃ k, btls md = RSt k ∧ btls md.rl = RSt (k + 1) := by
  cases md <;> simp_all [ByteMode.Readable, ByteMode.rl, btls]

theorem hasReader_btls {md : ByteMode} (h : md.HasReader) :
    ∃ k, btls md = RSt (k + 1) ∧ btls md.url = RSt k := by
  cases md with
  | Rd n => cases n <;> simp_all [ByteMode.HasReader, ByteMode.url, btls]
  | Wr => simp [ByteMode.HasReader] at h
  | Frozen n => cases n <;> simp_all [ByteMode.HasReader, ByteMode.url, btls]

/-- Read-locking a range. -/
theorem cells_read_lock (m : GMap w64 ByteCell) (a : w64) (dq : DFrac) (cs : List ByteCell)
    (hcs : LookupRange m a cs) (hlen : cs.length < 2 ^ 64) (hrd : ∀ c ∈ cs, c.1.Readable) :
    ⊢ naHeapCtx (GF := GF) btls m -∗ bytesPointsto a dq (cs.map Prod.snd) ==∗
      naHeapCtx btls (insertRange m a (cs.map fun c => (c.1.rl, c.2))) ∗
      bytesReading a dq (cs.map Prod.snd) := by
  induction cs generalizing a with
  | nil =>
    iintro Hσ _; imodintro; simp only [List.map_nil, insertRange]; iframe
    iapply (bytesReading_nil a dq).2; itrivial
  | cons c cs ih =>
    obtain ⟨h1, h2⟩ := hcs
    simp only [List.length_cons] at hlen
    simp only [List.map_cons]
    iintro Hσ H
    icases (bytesPointsto_cons a dq c.2 _).1 $$ H with ⟨Hc, H⟩
    imod ih (a + 1) h2 (by omega) (fun c' hc' => hrd c' (by simp [hc'])) $$ Hσ H with ⟨Hσ, H⟩
    obtain ⟨k, hk, hk'⟩ := readable_btls (hrd c (by simp))
    have hlk : insertRange m (a + 1) (cs.map fun c => (c.1.rl, c.2)) !! a = some (c.1, c.2) := by
      rw [lookup_insertRange_succ_self _ _ _ (by simp; omega)]; exact h1
    unfold bytePointsto naHeapPointsto
    imod na_heap_read_vs btls _ 0 1 k a dq c.2 c.1 c.1.rl hlk (by simpa using hk)
      (by rw [hk']; congr 1; omega) $$ Hσ Hc with ⟨Hσ, Hc⟩
    imodintro
    simp only [insertRange]
    iframe Hσ
    iapply (bytesReading_cons a dq c.2 _).2
    iframe

/-- The fragments of a read give a range with readers. -/
theorem reading_lookup (m : GMap w64 ByteCell) (a : w64) (dq : DFrac) (bs : List w8) :
    ⊢ naHeapCtx btls m -∗ bytesReading (GF := GF) a dq bs -∗
      ⌜∃ cs, LookupRange m a cs ∧ cs.map Prod.snd = bs ∧ ∀ c ∈ cs, c.1.HasReader⌝ := by
  induction bs generalizing a with
  | nil => iintro _ _; ipureintro; exact ⟨[], trivial, rfl, by simp⟩
  | cons b bs ih =>
    iintro Hσ H
    icases (bytesReading_cons a dq b bs).1 $$ H with ⟨Hb, H⟩
    icases naHeapPointsto_lookup btls m a (RSt 1) dq b $$ Hσ Hb with %⟨lk, n, Hlk, Hst⟩
    icases ih (a + 1) $$ Hσ H with %⟨cs, Hcs, Hmap, Hrd⟩
    ipureintro
    refine ⟨(lk, b) :: cs, ⟨Hlk, Hcs⟩, by simp [Hmap], ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · cases lk with
      | Rd k =>
        cases k with
        | zero => simp [btls] at Hst; omega
        | succ => simp [ByteMode.HasReader]
      | Wr => simp [btls] at Hst
      | Frozen k =>
        cases k with
        | zero => simp [btls] at Hst; omega
        | succ => simp [ByteMode.HasReader]
    · exact Hrd c hc

/-- Read-unlocking a range. -/
theorem cells_read_unlock (m : GMap w64 ByteCell) (a : w64) (dq : DFrac) (cs : List ByteCell)
    (hcs : LookupRange m a cs) (hlen : cs.length < 2 ^ 64) (hrd : ∀ c ∈ cs, c.1.HasReader) :
    ⊢ naHeapCtx (GF := GF) btls m -∗ bytesReading a dq (cs.map Prod.snd) ==∗
      naHeapCtx btls (insertRange m a (cs.map fun c => (c.1.url, c.2))) ∗
      bytesPointsto a dq (cs.map Prod.snd) := by
  induction cs generalizing a with
  | nil =>
    iintro Hσ _; imodintro; simp only [List.map_nil, insertRange]; iframe
    iapply (bytesPointsto_nil a dq).2; itrivial
  | cons c cs ih =>
    obtain ⟨h1, h2⟩ := hcs
    simp only [List.length_cons] at hlen
    simp only [List.map_cons]
    iintro Hσ H
    icases (bytesReading_cons a dq c.2 _).1 $$ H with ⟨Hc, H⟩
    imod ih (a + 1) h2 (by omega) (fun c' hc' => hrd c' (by simp [hc'])) $$ Hσ H with ⟨Hσ, H⟩
    obtain ⟨k, hk, hk'⟩ := hasReader_btls (hrd c (by simp))
    have hlk : insertRange m (a + 1) (cs.map fun c => (c.1.url, c.2)) !! a = some (c.1, c.2) := by
      rw [lookup_insertRange_succ_self _ _ _ (by simp; omega)]; exact h1
    imod na_heap_read_vs btls _ 1 0 k a dq c.2 c.1 c.1.url hlk (by rw [hk]; congr 1; omega)
      (by simpa using hk') $$ Hσ Hc with ⟨Hσ, Hc⟩
    imodintro
    simp only [insertRange]
    iframe Hσ
    iapply (bytesPointsto_cons a dq c.2 _).2
    unfold bytePointsto naHeapPointsto
    iframe

/-- The frozen bytes after changing the reader counts of a range. -/
theorem frozen_insertRange_preserve (m : GMap w64 ByteCell) (a : w64) (cs : List ByteCell)
    (f : ByteCell → ByteCell) (hcs : LookupRange m a cs) (hlen : cs.length ≤ 2 ^ 64)
    (hf : ∀ c, (f c).1.IsFrozen → ∃ n, c.1 = .Frozen n ∧ (f c).2 = c.2) :
    (□ ∀ a b n, ⌜m !! a = some (.Frozen n, b)⌝ → bytePointsto (GF := GF) a .discard b) ⊢
    (□ ∀ x b n, ⌜insertRange m a (cs.map f) !! x = some (.Frozen n, b)⌝ →
      bytePointsto (GF := GF) x .discard b) := by
  iintro #H
  imodintro
  iintro %x %b %n %Hx
  rcases frozen_insertRange_cases (by simpa using hlen) Hx with Hx | ⟨i, hi, rfl, hc⟩
  · iapply H $$ %x %b %n %Hx
  · have hi' : i < cs.length := by simpa using hi
    simp only [List.getElem_map] at hc
    obtain ⟨n', hn', hb⟩ := hf cs[i] (by rw [hc]; trivial)
    rw [hc] at hb
    have hlk := (lookupRange_iff m a cs).1 hcs i hi'
    have hci : cs[i] = (.Frozen n', b) := Prod.ext hn' hb.symm
    rw [hci] at hlk
    iapply H $$ %(byteAddr a i) %b %n' %hlk

/-! ### Lifting -/

/-- A lifting lemma for atomic steps that only change the byte memory. -/
theorem wp_lift_atomic_bmem_step {e₁ : Expr} {Φ : val → IProp GF} (h : toVal e₁ = none)
    (hnc : redexKind e₁ = .plain) (hnu : ∀ p, ¬ Unwinds e₁ p) :
    (∀ σ₁ : CfgState, bmemCtx σ₁.1.bmem ={E}=∗
      ⌜GooseBaseReducible e₁ σ₁⌝ ∗
      ▷ ∀ κ e₂ σ₂ eₜ, ⌜BaseStep e₁ σ₁ κ e₂ σ₂ eₜ⌝ -∗ £ 1 ={E}=∗
        ⌜κ = [] ∧ eₜ = []⌝ ∗
        (∃ m', ⌜σ₂ = setBmem (fun _ => m') σ₁⌝ ∗ bmemCtx m') ∗
        (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v))
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply goose_wp_lift_atomic_base_step_no_fork h hnc hnu
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph, Hbm⟩
  imod H $$ %σ₁ Hbm with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact Hred
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  imod H $$ %obs %e₂ %σ₂ %eₜ %Hstep Hcred with ⟨%⟨rfl, rfl⟩, ⟨%m', %rfl, Hbm⟩, HΦ⟩
  imodintro
  isplitr
  · ipureintro; rfl
  iframe HΦ
  iapply (goose_stateInterp_eq _ (ns + 1) obs' nt).mpr
  dsimp only [setBmem, List.nil_append]
  iframe
  ipureintro; exact Hlctx

/-- A lifting lemma for (possibly looping) steps that only change the byte memory. -/
theorem wp_lift_bmem_step {e₁ : Expr} {Φ : val → IProp GF} (h : toVal e₁ = none)
    (hnc : redexKind e₁ = .plain) (hnu : ∀ p, ¬ Unwinds e₁ p) :
    (∀ σ₁ : CfgState, bmemCtx σ₁.1.bmem ={E,∅}=∗
      ⌜GooseBaseReducible e₁ σ₁⌝ ∗
      ▷ ∀ κ e₂ σ₂ eₜ, ⌜BaseStep e₁ σ₁ κ e₂ σ₂ eₜ⌝ -∗ £ 1 ={∅,E}=∗
        ⌜κ = [] ∧ eₜ = []⌝ ∗
        (∃ m', ⌜σ₂ = setBmem (fun _ => m') σ₁⌝ ∗ bmemCtx m') ∗
        WP e₂ @ s; E {{ Φ }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply goose_wp_lift_base_step h hnc hnu
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph, Hbm⟩
  imod H $$ %σ₁ Hbm with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact Hred
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  imod H $$ %obs %e₂ %σ₂ %eₜ %Hstep Hcred with ⟨%⟨rfl, rfl⟩, ⟨%m', %rfl, Hbm⟩, Hwp⟩
  imodintro
  iframe Hwp
  isplitl
  · iapply (goose_stateInterp_eq _ (ns + 1) obs' nt).mpr
    dsimp only [setBmem, List.nil_append]
    iframe
    ipureintro; exact Hlctx
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-! ### Static bytes

The static bytes (`staticBytes`, the program image's read-only data) are frozen
bytes of the memory from the start (`staticImage`, `Adequacy.lean`), and the
interpretation keeps persistent fragments of all frozen bytes, so a proof can
take `a ↦∗□ bs` for any static range at any step (`wp_static_bytes`). -/

/-- Persistent ownership of a static range, from the interpretation's frozen bytes. -/
theorem static_bytes_of (m : ByteMem) (a : w64) (bs : List w8) (hagree : StaticAgree m)
    (hs : ∀ i (hi : i < bs.length), staticBytes !! byteAddr a i = some bs[i]) :
    (□ ∀ a b n, ⌜m.bytes !! a = some (.Frozen n, b)⌝ → bytePointsto (GF := GF) a .discard b) ⊢
      bytesPointsto a .discard bs := by
  induction bs generalizing a with
  | nil => iintro _; iapply (bytesPointsto_nil a _).2; itrivial
  | cons b bs ih =>
    have h0 : staticBytes !! a = some b := by
      have := hs 0 (by simp); rwa [byteAddr_zero, List.getElem_cons_zero] at this
    obtain ⟨n, hn⟩ := hagree a b h0
    iintro #Hfr
    iapply (bytesPointsto_cons a _ b bs).2
    isplitl
    · iapply Hfr $$ %a %b %n %hn
    · iapply ih (a + 1) (fun i hi => by
        have := hs (i + 1) (by simp; omega)
        rwa [byteAddr_succ, ← List.getElem_cons_succ (a := b)]) $$ Hfr

/-- The interpretation gives the frozen bytes persistently, and its invariants. -/
theorem stateInterp_frozen_acc (σ : BcfgState) (ns : Nat) (κs : List Observation) (nt : Nat) :
    stateInterp (GF := GF) σ ns κs nt ⊢ stateInterp σ ns κs nt ∗
      (□ ∀ a b n, ⌜σ.1.1.bmem.bytes !! a = some (.Frozen n, b)⌝ →
        bytePointsto (GF := GF) a .discard b) ∗ ⌜BmemWf σ.1.1.bmem⌝ := by
  rcases σ with ⟨σ, c⟩
  iintro Hσ
  icases (goose_bstateInterp_eq σ c ns κs nt).1 $$ Hσ with ⟨Hσ, Hc, Ht⟩
  icases (goose_stateInterp_eq σ ns κs nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph, Hbm⟩
  icases (bmemCtx_eq _).1 $$ Hbm with ⟨Hbytes, #Hfr, Hbl, Hfn, %Hwf⟩
  isplitl
  · iapply (goose_bstateInterp_eq σ c ns κs nt).2
    iframe Hc Ht
    iapply (goose_stateInterp_eq σ ns κs nt).mpr
    iframe
    isplitr
    · ipureintro; exact Hlctx
    iapply (bmemCtx_eq _).2
    iframe
    isplitr
    · iexact Hfr
    ipureintro; exact Hwf
  isplitr
  · iexact Hfr
  · ipureintro; exact Hwf

/-- A static range, persistently, before any step. -/
theorem wp_static_bytes {e : Expr} {Φ : val → IProp GF} (a : w64) (bs : List w8)
    (hs : ∀ i (hi : i < bs.length), staticBytes !! byteAddr a i = some bs[i])
    (he : toVal e = none) :
    (bytesPointsto (GF := GF) a .discard bs -∗ WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} := by
  have h1 := wp_unfold (s := s) (E := E) (e := e) (Φ := Φ)
  simp only [wp.pre] at h1
  rw [show ToVal.toVal e = none from he] at h1
  iintro H
  iapply h1.2
  iintro %σ %ns %obs %obs' %nt Hσ
  icases stateInterp_frozen_acc σ ns (obs ++ obs') nt $$ Hσ with ⟨Hσ, #Hfr, %Hwf⟩
  ihave #Hl := static_bytes_of σ.1.1.bmem a bs Hwf.2 hs $$ Hfr
  ihave H := H $$ Hl
  icases h1.1 $$ H with H
  iapply H $$ Hσ

/-! ### Allocation -/

/-- Persistent ownership of a frozen range, from the interpretation. -/
theorem frozen_bytes_of_lookup (m : GMap w64 ByteCell) (a : w64) (cs : List ByteCell)
    (h : LookupRange m a cs) (hfz : ∀ c ∈ cs, c.1.IsFrozen) :
    (□ ∀ a b n, ⌜m !! a = some (.Frozen n, b)⌝ → bytePointsto (GF := GF) a .discard b) ⊢
      bytesPointsto a .discard (cs.map Prod.snd) := by
  induction cs generalizing a with
  | nil => iintro _; simp only [List.map_nil]; iapply (bytesPointsto_nil a _).2; itrivial
  | cons c cs ih =>
    obtain ⟨h1, h2⟩ := h
    iintro #Hfr
    simp only [List.map_cons]
    iapply (bytesPointsto_cons a _ c.2 (cs.map Prod.snd)).2
    isplitl
    · obtain ⟨md, b⟩ := c
      cases md with
      | Frozen n => iapply Hfr $$ %a %b %n %h1
      | _ => exact absurd (hfz _ List.mem_cons_self) (by simp [ByteMode.IsFrozen])
    · iapply ih (a + 1) h2 (fun c hc => hfz c (by simp [hc])) $$ Hfr

/-- The ghost part of allocating the cells `cs` as a block at a fresh `a`. -/
theorem bmem_alloc_block (m : ByteMem) (a : w64) (cs : List ByteCell)
    (hf : FreshRange m.bytes a cs.length) (hrd : ∀ c ∈ cs, btls c.1 = RSt 0) (hwf : BmemWf m) :
    ⊢ naHeapCtx (GF := GF) btls m.bytes -∗
      ghostMapAuth L.goose_bmemGS.bm_blocksName 1 m.blocks ==∗
      naHeapCtx btls (m.allocRange a cs).bytes ∗
      ghostMapAuth L.goose_bmemGS.bm_blocksName 1 (m.allocRange a cs).blocks ∗
      bytesPointsto a (.own 1) (cs.map Prod.snd) ∗ (⌜cs = []⌝ ∨ isBlock a cs.length) := by
  iintro Hbytes Hbl
  imod cells_alloc m.bytes a cs (fun i hi => hf.2.2 i hi) (by have := hf.2.1; omega) hrd $$ Hbytes
    with ⟨Hbytes, Hl⟩
  by_cases hn : cs.length = 0
  · have hb : (m.allocRange a cs).blocks = m.blocks := by simp [addBlock, hn]
    rw [hb]
    imodintro
    iframe
    ileft; ipureintro; exact List.eq_nil_of_length_eq_zero hn
  · have hb : (m.allocRange a cs).blocks = <[a := cs.length]> m.blocks := by
      simp [addBlock, hn]
    rw [hb]
    imod ghost_map_insert_persist a cs.length (freshRange_blocks_none hwf hf hn) $$ Hbl
      with ⟨Hbl, #Hb⟩
    imodintro
    iframe
    iright; unfold isBlock; iexact Hb

theorem wp_balloc (al : w64) (bs : List w8) :
    {{ (True : IProp GF) }} (BAlloc (Val (PairV #al (blobV bs)))) @ s; E
    {{ (a : w64), RET #a; bytesPointsto a (.own 1) bs ∗
        ⌜a ≠ 0 ∧ Aligned a al ∧ a.toNat + bs.length ≤ 2 ^ 64⌝ ∗
        (⌜bs = []⌝ ∨ isBlock a bs.length) }} := by
  iintro %Φ _ HΦ
  iapply (show ⊢ ▷ (∀ a : w64, bytesPointsto (GF := GF) a (.own 1) bs ∗
        ⌜a ≠ 0 ∧ Aligned a al ∧ a.toNat + bs.length ≤ 2 ^ 64⌝ ∗
        (⌜bs = []⌝ ∨ isBlock a bs.length) -∗ Φ #a) -∗
      WP (BAlloc (Val (PairV #al (blobV bs)))) @ s; E {{ Φ }} from ?_) $$ HΦ
  iloeb as IH
  iintro HΦ
  iapply wp_lift_bmem_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    by_cases ha : ∃ a, FreshRange σ₁.1.bmem.bytes a bs.length ∧ Aligned a al
    · obtain ⟨a, hf, hal⟩ := ha
      exact ⟨[], _, _, [], BaseStep.BAllocS al bs a σ₁ hf hal⟩
    · exact ⟨[], _, _, [], BaseStep.BAllocOomS al bs σ₁ ha⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  imod Hclose
  generalize hv : PairV #al (blobV bs) = v at Hstep
  cases Hstep with
  | BAllocS al' bs' a _ hf hal =>
    simp only [val.PairV.injEq, val.LitV.injEq, BaseLit.LitString.injEq] at hv
    obtain ⟨hal', rfl⟩ := hv
    cases intoVal_w64_inj hal'
    icases (bmemCtx_eq _).1 $$ Hσ with ⟨Hbytes, #Hfr, Hbl, Hfn, %Hwf⟩
    have hlen : (bs.map (ByteMode.Rd 0, ·)).length ≤ 2 ^ 64 := by
      have := hf.2.1; simp; omega
    imod bmem_alloc_block σ₁.1.bmem a (bs.map (ByteMode.Rd 0, ·)) (by simpa using hf)
      (by simp) Hwf $$ Hbytes Hbl with ⟨Hbytes, Hbl, Hl, Hb⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hbytes Hbl Hfn]
    · iexists σ₁.1.bmem.allocRange a (bs.map (ByteMode.Rd 0, ·))
      isplitr
      · ipureintro; rfl
      iapply (bmemCtx_eq _).2
      iframe
      isplitr
      · iapply frozen_insertRange_unfrozen _ a _ hlen
          (notFrozen_map _ _ fun _ => by simp [ByteMode.IsFrozen]) $$ Hfr
      ipureintro
      exact bmemWf_allocRange a _ Hwf hlen (fun i hi => hf.2.2 i (by simpa using hi))
    iapply wp_value'
    iapply HΦ
    simp only [List.map_map, Function.comp_def, List.map_id', List.length_map,
      List.map_eq_nil_iff]
    iframe
    ipureintro; exact ⟨hf.1, hal, hf.2.1⟩
  | BAllocOomS al' bs' _ hno =>
    simp only [val.PairV.injEq, val.LitV.injEq, BaseLit.LitString.injEq] at hv
    obtain ⟨hal', rfl⟩ := hv
    cases intoVal_w64_inj hal'
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists σ₁.1.bmem
      isplitr
      · ipureintro; rfl
      iexact Hσ
    iapply IH
    inext
    iexact HΦ

theorem wp_balloc_frozen (bs : List w8) :
    {{ (True : IProp GF) }} (BAllocFrozen (Val (blobV bs))) @ s; E
    {{ (a : w64), RET #a; bytesPointsto a .discard bs }} := by
  iintro %Φ _ HΦ
  iapply (show ⊢ ▷ (∀ a : w64, bytesPointsto (GF := GF) a .discard bs -∗ Φ #a) -∗
      WP (BAllocFrozen (Val (blobV bs))) @ s; E {{ Φ }} from ?_) $$ HΦ
  iloeb as IH
  iintro HΦ
  iapply wp_lift_bmem_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    by_cases ha : ∃ a, FreshRange σ₁.1.bmem.bytes a bs.length
    · obtain ⟨a, hf⟩ := ha
      exact ⟨[], _, _, [], BaseStep.BAllocFrozenS bs a σ₁ hf⟩
    · exact ⟨[], _, _, [], BaseStep.BAllocFrozenOomS bs σ₁ ha⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  imod Hclose
  generalize hv : blobV bs = v at Hstep
  cases Hstep with
  | BAllocFrozenS bs' a _ hf =>
    simp only [val.LitV.injEq, BaseLit.LitString.injEq] at hv; subst hv
    icases (bmemCtx_eq _).1 $$ Hσ with ⟨Hbytes, #Hfr, Hbl, Hfn, %Hwf⟩
    have hlen : bs.length ≤ 2 ^ 64 := by have := hf.2.1; omega
    imod bmem_alloc_block σ₁.1.bmem a (bs.map (ByteMode.Frozen 0, ·)) (by simpa using hf)
      (by simp) Hwf $$ Hbytes Hbl with ⟨Hbytes, Hbl, Hl, -⟩
    simp only [List.map_map, Function.comp_def, List.map_id']
    imod bytesPointsto_persist a _ bs $$ Hl with #Hl
    imodintro
    isplitr
    · ipureintro; simp
    isplitl [Hbytes Hbl Hfn]
    · iexists σ₁.1.bmem.allocRange a (bs.map (ByteMode.Frozen 0, ·))
      isplitr
      · ipureintro; rfl
      iapply (bmemCtx_eq _).2
      iframe
      isplitr
      · iapply frozen_insertRange_frozen _ a bs 0 hlen $$ Hfr Hl
      ipureintro
      exact bmemWf_allocRange a _ Hwf (by simpa using hlen)
        (fun i hi => hf.2.2 i (by simpa using hi))
    iapply wp_value'
    iapply HΦ $$ Hl
  | BAllocFrozenReuseS bs' a cs _ hcs hfz hmap =>
    simp only [val.LitV.injEq, BaseLit.LitString.injEq] at hv; subst hv
    icases (bmemCtx_eq _).1 $$ Hσ with ⟨Hbytes, #Hfr, Hrest⟩
    ihave #Hl := frozen_bytes_of_lookup _ a cs hcs hfz $$ Hfr
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hbytes Hrest]
    · iexists σ₁.1.bmem
      isplitr
      · ipureintro; rfl
      iapply (bmemCtx_eq _).2
      iframe
      iexact Hfr
    iapply wp_value'
    iapply HΦ
    rw [← hmap]
    iexact Hl
  | BAllocFrozenOomS bs' _ hno =>
    simp only [val.LitV.injEq, BaseLit.LitString.injEq] at hv; subst hv
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists σ₁.1.bmem
      isplitr
      · ipureintro; rfl
      iexact Hσ
    iapply IH
    inext
    iexact HΦ

/-! ### Reads and writes -/

theorem wp_bload (a n : w64) (dq : DFrac) (bs : List w8) (hn : bs.length = n.toNat) :
    {{ ▷ bytesPointsto (GF := GF) a dq bs }} (BLoad (Val (PairV #a #n))) @ s; E
    {{ RET blobV bs; bytesPointsto a dq bs }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_bmem_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases (bmemCtx_eq _).1 $$ Hσ with ⟨Hbytes, Hrest⟩
  icases bytes_lookup _ a dq bs $$ Hbytes Hl with %⟨cs, Hcs, Hmap, Hrd⟩
  have Hlen : cs.length = n.toNat := by rw [← hn, ← Hmap, List.length_map]
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.BLoadS a n cs σ₁ Hcs Hlen Hrd⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  generalize hv : PairV #a #n = v at Hstep
  cases Hstep with
  | BLoadS a' n' cs' _ Hcs' Hlen' _ =>
    simp only [val.PairV.injEq] at hv
    obtain ⟨ha, hn'⟩ := hv
    cases intoVal_w64_inj ha; cases intoVal_w64_inj hn'
    cases lookupRange_unique Hcs Hcs' (by rw [Hlen, Hlen'])
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hbytes Hrest]
    · iexists σ₁.1.bmem
      isplitr
      · ipureintro; rfl
      iapply (bmemCtx_eq _).2
      iframe
    iexists blobV bs
    isplit
    · ipureintro; rw [Hmap]; rfl
    iapply HΦ $$ Hl

theorem wp_bstart_read (a n : w64) (dq : DFrac) (bs : List w8) (hn : bs.length = n.toNat) :
    {{ ▷ bytesPointsto (GF := GF) a dq bs }} (BStartRead (Val (PairV #a #n))) @ s; E
    {{ RET blobV bs; bytesReading a dq bs }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_bmem_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases (bmemCtx_eq _).1 $$ Hσ with ⟨Hbytes, #Hfr, Hrest⟩
  icases bytes_lookup _ a dq bs $$ Hbytes Hl with %⟨cs, Hcs, Hmap, Hrd⟩
  have Hlen : cs.length = n.toNat := by rw [← hn, ← Hmap, List.length_map]
  have Hlt : cs.length < 2 ^ 64 := by have := n.isLt; omega
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.BStartReadS a n cs σ₁ Hcs Hlen Hrd⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  generalize hv : PairV #a #n = v at Hstep
  cases Hstep with
  | BStartReadS a' n' cs' _ Hcs' Hlen' _ =>
    simp only [val.PairV.injEq] at hv
    obtain ⟨ha, hn'⟩ := hv
    cases intoVal_w64_inj ha; cases intoVal_w64_inj hn'
    cases lookupRange_unique Hcs Hcs' (by rw [Hlen, Hlen'])
    subst Hmap
    imod cells_read_lock _ a dq cs Hcs Hlt Hrd $$ Hbytes Hl with ⟨Hbytes, Hl⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hbytes Hrest]
    · iexists σ₁.1.bmem.writeRange a (cs.map fun c => (c.1.rl, c.2))
      isplitr
      · ipureintro; rfl
      icases Hrest with ⟨Hbl, Hfn, %Hwf⟩
      iapply (bmemCtx_eq _).2
      iframe
      isplitr
      · iapply frozen_insertRange_preserve _ a cs _ Hcs (by omega)
          (fun c h => by
            obtain ⟨md, b⟩ := c
            cases md <;> simp_all [ByteMode.rl, ByteMode.IsFrozen]) $$ Hfr
      ipureintro
      exact bmemWf_writeRange a _ Hwf
        (staticAgree_insertRange Hwf.2 Hcs Hlt (by simp) (frozenKept_of_map _ fun c h => by
          obtain ⟨md, b⟩ := c; cases md <;> simp_all [ByteMode.rl, ByteMode.IsFrozen]))
    iexists blobV (cs.map Prod.snd)
    isplit
    · ipureintro; rfl
    iapply HΦ $$ Hl

theorem wp_bfinish_read (a n : w64) (dq : DFrac) (bs : List w8) (hn : bs.length = n.toNat) :
    {{ ▷ bytesReading (GF := GF) a dq bs }} (BFinishRead (Val (PairV #a #n))) @ s; E
    {{ RET #(); bytesPointsto a dq bs }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_bmem_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases (bmemCtx_eq _).1 $$ Hσ with ⟨Hbytes, #Hfr, Hrest⟩
  icases reading_lookup _ a dq bs $$ Hbytes Hl with %⟨cs, Hcs, Hmap, Hrd⟩
  have Hlen : cs.length = n.toNat := by rw [← hn, ← Hmap, List.length_map]
  have Hlt : cs.length < 2 ^ 64 := by have := n.isLt; omega
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.BFinishReadS a n cs σ₁ Hcs Hlen Hrd⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  generalize hv : PairV #a #n = v at Hstep
  cases Hstep with
  | BFinishReadS a' n' cs' _ Hcs' Hlen' _ =>
    simp only [val.PairV.injEq] at hv
    obtain ⟨ha, hn'⟩ := hv
    cases intoVal_w64_inj ha; cases intoVal_w64_inj hn'
    cases lookupRange_unique Hcs Hcs' (by rw [Hlen, Hlen'])
    subst Hmap
    imod cells_read_unlock _ a dq cs Hcs Hlt Hrd $$ Hbytes Hl with ⟨Hbytes, Hl⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hbytes Hrest]
    · iexists σ₁.1.bmem.writeRange a (cs.map fun c => (c.1.url, c.2))
      isplitr
      · ipureintro; rfl
      icases Hrest with ⟨Hbl, Hfn, %Hwf⟩
      iapply (bmemCtx_eq _).2
      iframe
      isplitr
      · iapply frozen_insertRange_preserve _ a cs _ Hcs (by omega)
          (fun c h => by
            obtain ⟨md, b⟩ := c
            cases md with
            | Rd k => cases k <;> simp_all [ByteMode.url, ByteMode.IsFrozen]
            | Wr => simp_all [ByteMode.url, ByteMode.IsFrozen]
            | Frozen k => cases k <;> simp_all [ByteMode.url, ByteMode.IsFrozen]) $$ Hfr
      ipureintro
      exact bmemWf_writeRange a _ Hwf
        (staticAgree_insertRange Hwf.2 Hcs Hlt (by simp) (frozenKept_of_map _ fun c h => by
          obtain ⟨md, b⟩ := c
          cases md with
          | Rd k => simp_all [ByteMode.IsFrozen]
          | Wr => simp_all [ByteMode.IsFrozen]
          | Frozen k => cases k <;> simp_all [ByteMode.url]))
    iexists #()
    isplit
    · ipureintro; rfl
    iapply HΦ $$ Hl

theorem wp_bprepare_write (a n : w64) (bs : List w8) (hn : bs.length = n.toNat) :
    {{ ▷ bytesPointsto (GF := GF) a (.own 1) bs }} (BPrepareWrite (Val (PairV #a #n))) @ s; E
    {{ RET #(); bytesWriting a bs }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_bmem_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases (bmemCtx_eq _).1 $$ Hσ with ⟨Hbytes, #Hfr, Hrest⟩
  icases bytes_lookup_1 _ a bs $$ Hbytes Hfr Hl with %⟨cs, Hcs, Hmap, Hrd⟩
  have Hlen : cs.length = n.toNat := by rw [← hn, ← Hmap, List.length_map]
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.BPrepareWriteS a n cs σ₁ Hcs Hlen Hrd⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  generalize hv : PairV #a #n = v at Hstep
  cases Hstep with
  | BPrepareWriteS a' n' cs' _ Hcs' Hlen' _ =>
    simp only [val.PairV.injEq] at hv
    obtain ⟨ha, hn'⟩ := hv
    cases intoVal_w64_inj ha; cases intoVal_w64_inj hn'
    cases lookupRange_unique Hcs Hcs' (by rw [Hlen, Hlen'])
    have Hcells : cs.map (fun c => (ByteMode.Wr, c.2)) = bs.map (.Wr, ·) := by
      rw [← Hmap, List.map_map]; rfl
    have Hcl : (cs.map (fun c => (ByteMode.Wr, c.2))).length ≤ 2 ^ 64 := by
      simp only [List.length_map, Hlen]; have := n.isLt; omega
    icases (bytesPointsto_cellsOwn a bs).1 $$ Hl with Hl
    imod cells_write _ a _ (cs.map (fun c => (ByteMode.Wr, c.2))) (by subst Hmap; simp) $$ Hbytes Hl
      with ⟨Hbytes, Hl⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hbytes Hrest]
    · iexists σ₁.1.bmem.writeRange a (cs.map (fun c => (ByteMode.Wr, c.2)))
      isplitr
      · ipureintro; rfl
      icases Hrest with ⟨Hbl, Hfn, %Hwf⟩
      iapply (bmemCtx_eq _).2
      iframe
      isplitr
      · iapply frozen_insertRange_unfrozen _ a _ Hcl
          (notFrozen_map _ _ fun _ => by simp [ByteMode.IsFrozen]) $$ Hfr
      ipureintro
      exact bmemWf_writeRange a _ Hwf
        (staticAgree_insertRange Hwf.2 Hcs (by have := n.isLt; omega) (by simp)
          (frozenKept_of_notFrozen fun c hc => by rw [Hrd c hc]; simp [ByteMode.IsFrozen]))
    iexists #()
    isplit
    · ipureintro; rfl
    iapply HΦ
    iapply (bytesWriting_cellsOwn a bs).2
    rw [← Hcells]
    iexact Hl

theorem wp_bfinish_write (a : w64) (bs bs' : List w8) (hlen : bs'.length = bs.length)
    (hlt : bs.length < 2 ^ 64) :
    {{ ▷ bytesWriting (GF := GF) a bs }} (BFinishWrite (Val #a) (Val (blobV bs'))) @ s; E
    {{ RET #(); bytesPointsto a (.own 1) bs' }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_bmem_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases (bmemCtx_eq _).1 $$ Hσ with ⟨Hbytes, #Hfr, Hrest⟩
  icases writing_lookup _ a bs $$ Hbytes Hl with %Hcs
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.BFinishWriteS a bs' _ σ₁ Hcs (by simp [hlen]) (by omega)
      (by simp)⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  generalize hv : (#a : val) = v at Hstep
  generalize hb : blobV bs' = vb at Hstep
  cases Hstep with
  | BFinishWriteS a' bs'' cs' _ Hcs' Hlen' _ _ =>
    cases intoVal_w64_inj hv
    simp only [val.LitV.injEq, BaseLit.LitString.injEq] at hb; subst hb
    have Hcl : (bs'.map (ByteMode.Rd 0, ·)).length ≤ 2 ^ 64 := by simp; omega
    icases (bytesWriting_cellsOwn a bs).1 $$ Hl with Hl
    imod cells_write _ a _ (bs'.map (ByteMode.Rd 0, ·)) (by simp [hlen]) $$ Hbytes Hl
      with ⟨Hbytes, Hl⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hbytes Hrest]
    · iexists σ₁.1.bmem.writeRange a (bs'.map (ByteMode.Rd 0, ·))
      isplitr
      · ipureintro; rfl
      icases Hrest with ⟨Hbl, Hfn, %Hwf⟩
      iapply (bmemCtx_eq _).2
      iframe
      isplitr
      · iapply frozen_insertRange_unfrozen _ a _ Hcl
          (notFrozen_map _ _ fun _ => by simp [ByteMode.IsFrozen]) $$ Hfr
      ipureintro
      exact bmemWf_writeRange a _ Hwf
        (staticAgree_insertRange Hwf.2 Hcs (by simpa using hlt) (by simp [hlen])
          (frozenKept_of_notFrozen fun c hc => by
            obtain ⟨_, _, rfl⟩ := List.mem_map.mp hc; simp [ByteMode.IsFrozen]))
    iexists #()
    isplit
    · ipureintro; rfl
    iapply HΦ
    iapply (bytesPointsto_cellsOwn a bs').2
    iexact Hl

theorem wp_bswap (a : w64) (bs bs' : List w8) (hlen : bs'.length = bs.length)
    (hlt : bs.length < 2 ^ 64) :
    {{ ▷ bytesPointsto (GF := GF) a (.own 1) bs }} (BSwap (Val #a) (Val (blobV bs'))) @ s; E
    {{ RET blobV bs; bytesPointsto a (.own 1) bs' }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_bmem_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases (bmemCtx_eq _).1 $$ Hσ with ⟨Hbytes, #Hfr, Hrest⟩
  icases bytes_lookup_1 _ a bs $$ Hbytes Hfr Hl with %⟨cs, Hcs, Hmap, Hrd⟩
  have Hlen : cs.length = bs.length := by rw [← Hmap, List.length_map]
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.BSwapS a bs' cs σ₁ Hcs (by omega) (by omega) Hrd⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  generalize hv : (#a : val) = v at Hstep
  generalize hb : blobV bs' = vb at Hstep
  cases Hstep with
  | BSwapS a' bs'' cs' _ Hcs' Hlen' _ _ =>
    cases intoVal_w64_inj hv
    simp only [val.LitV.injEq, BaseLit.LitString.injEq] at hb; subst hb
    cases lookupRange_unique Hcs Hcs' (by omega)
    have Hcl : (bs'.map (ByteMode.Rd 0, ·)).length ≤ 2 ^ 64 := by simp; omega
    icases (bytesPointsto_cellsOwn a bs).1 $$ Hl with Hl
    imod cells_write _ a _ (bs'.map (ByteMode.Rd 0, ·)) (by simp [hlen]) $$ Hbytes Hl
      with ⟨Hbytes, Hl⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hbytes Hrest]
    · iexists σ₁.1.bmem.writeRange a (bs'.map (ByteMode.Rd 0, ·))
      isplitr
      · ipureintro; rfl
      icases Hrest with ⟨Hbl, Hfn, %Hwf⟩
      iapply (bmemCtx_eq _).2
      iframe
      isplitr
      · iapply frozen_insertRange_unfrozen _ a _ Hcl
          (notFrozen_map _ _ fun _ => by simp [ByteMode.IsFrozen]) $$ Hfr
      ipureintro
      exact bmemWf_writeRange a _ Hwf
        (staticAgree_insertRange Hwf.2 Hcs (by omega) (by simp; omega)
          (frozenKept_of_notFrozen fun c hc => by rw [Hrd c hc]; simp [ByteMode.IsFrozen]))
    iexists blobV bs
    isplit
    · ipureintro; rw [Hmap]; rfl
    iapply HΦ
    iapply (bytesPointsto_cellsOwn a bs').2
    iexact Hl

theorem wp_bfreeze (a n : w64) (bs : List w8) (hn : bs.length = n.toNat) :
    {{ ▷ bytesPointsto (GF := GF) a (.own 1) bs }} (BFreeze (Val (PairV #a #n))) @ s; E
    {{ RET #(); bytesPointsto a .discard bs }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_bmem_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases (bmemCtx_eq _).1 $$ Hσ with ⟨Hbytes, #Hfr, Hrest⟩
  icases bytes_lookup_1 _ a bs $$ Hbytes Hfr Hl with %⟨cs, Hcs, Hmap, Hrd⟩
  have Hlen : cs.length = n.toNat := by rw [← hn, ← Hmap, List.length_map]
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.BFreezeS a n cs σ₁ Hcs Hlen Hrd⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  generalize hv : PairV #a #n = v at Hstep
  cases Hstep with
  | BFreezeS a' n' cs' _ Hcs' Hlen' _ =>
    simp only [val.PairV.injEq] at hv
    obtain ⟨ha, hn'⟩ := hv
    cases intoVal_w64_inj ha; cases intoVal_w64_inj hn'
    cases lookupRange_unique Hcs Hcs' (by rw [Hlen, Hlen'])
    have Hcells : cs.map (fun c => (ByteMode.Frozen 0, c.2)) = bs.map (.Frozen 0, ·) := by
      rw [← Hmap, List.map_map]; rfl
    have Hbl : bs.length ≤ 2 ^ 64 := by have := n.isLt; omega
    icases (bytesPointsto_cellsOwn a bs).1 $$ Hl with Hl
    imod cells_write _ a _ (bs.map (ByteMode.Frozen 0, ·)) (by simp) $$ Hbytes Hl
      with ⟨Hbytes, Hl⟩
    icases (bytesPointsto_cellsOwn' (.Frozen 0) rfl a bs).2 $$ Hl with Hl
    imod bytesPointsto_persist a _ bs $$ Hl with #Hl
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hbytes Hrest]
    · iexists σ₁.1.bmem.writeRange a (cs.map (fun c => (ByteMode.Frozen 0, c.2)))
      isplitr
      · ipureintro; rfl
      icases Hrest with ⟨Hbk, Hfn, %Hwf⟩
      iapply (bmemCtx_eq _).2
      rw [Hcells]
      iframe
      isplitr
      · iapply frozen_insertRange_frozen _ a bs 0 Hbl $$ Hfr Hl
      ipureintro
      exact bmemWf_writeRange a _ Hwf
        (staticAgree_insertRange Hwf.2 Hcs (by have := n.isLt; omega) (by rw [← Hmap]; simp)
          (frozenKept_of_notFrozen fun c hc => by rw [Hrd c hc]; simp [ByteMode.IsFrozen]))
    iexists #()
    isplit
    · ipureintro; rfl
    iapply HΦ $$ Hl

/-! ### Pointer arithmetic -/

theorem wp_unsafe_add (p off b : w64) (sz : Nat) (hp : InBlock b sz p)
    (hoff : InBlock b sz (p + off)) :
    {{ isBlock (GF := GF) b sz }} (UnsafeAdd (Val #p) (Val #off)) @ s; E
    {{ RET #(p + off); True }} := by
  unfold isBlock
  iintro %Φ #Hb HΦ
  iapply wp_lift_atomic_bmem_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases (bmemCtx_eq _).1 $$ Hσ with ⟨Hbytes, Hfr, Hbl, Hrest⟩
  icases ghost_map_lookup $$ Hbl Hb with %Hlk
  ihave Hσ : bmemCtx σ₁.1.bmem $$ [Hbytes Hfr Hbl Hrest]
  · iapply (bmemCtx_eq _).2; iframe
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.UnsafeAddS p off b sz σ₁ Hlk hp hoff⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  generalize hv : (#p : val) = v at Hstep
  generalize hv' : (#off : val) = v' at Hstep
  cases Hstep with
  | UnsafeAddS p' off' =>
    cases intoVal_w64_inj hv; cases intoVal_w64_inj hv'
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists σ₁.1.bmem
      isplitr
      · ipureintro; rfl
      iexact Hσ
    iexists #(p + off)
    isplit
    · ipureintro; rfl
    iapply HΦ; itrivial
  | UnsafeAddZeroS p' =>
    cases intoVal_w64_inj hv; cases intoVal_w64_inj hv'
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists σ₁.1.bmem
      isplitr
      · ipureintro; rfl
      iexact Hσ
    iexists #p
    isplit
    · ipureintro; rfl
    rw [show p + (0 : w64) = p by simp]
    iapply HΦ; itrivial

theorem wp_unsafe_add_zero (p : w64) :
    {{ (True : IProp GF) }} (UnsafeAdd (Val #p) (Val #(0 : w64))) @ s; E
    {{ RET #p; True }} := by
  iintro %Φ _ HΦ
  iapply wp_lift_atomic_bmem_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.UnsafeAddZeroS p σ₁⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  generalize hv : (#p : val) = v at Hstep
  generalize hv' : (#(0 : w64) : val) = v' at Hstep
  cases Hstep with
  | UnsafeAddS p' off' =>
    cases intoVal_w64_inj hv; cases intoVal_w64_inj hv'
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists σ₁.1.bmem
      isplitr
      · ipureintro; rfl
      iexact Hσ
    iexists #(p + 0)
    isplit
    · ipureintro; rfl
    rw [show p + (0 : w64) = p by simp]
    iapply HΦ; itrivial
  | UnsafeAddZeroS p' =>
    cases intoVal_w64_inj hv
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists σ₁.1.bmem
      isplitr
      · ipureintro; rfl
      iexact Hσ
    iexists #p
    isplit
    · ipureintro; rfl
    iapply HΦ; itrivial

/-! ### Func pointers -/

theorem wp_func_alloc (v : val) (Hv : v.isPanic = false := by simp) :
    {{ (True : IProp GF) }} (FuncAlloc (Val v)) @ s; E
    {{ (p : w64), RET #p; isFunc p v ∗ ⌜p ≠ 0⌝ }} := by
  iintro %Φ _ HΦ
  iapply (show ⊢ ▷ (∀ p : w64, isFunc (GF := GF) p v ∗ ⌜p ≠ 0⌝ -∗ Φ #p) -∗
      WP (FuncAlloc (Val v)) @ s; E {{ Φ }} from ?_) $$ HΦ
  iloeb as IH
  iintro HΦ
  iapply wp_lift_bmem_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    by_cases hp : ∃ p : w64, p ≠ 0 ∧ σ₁.1.bmem.funcs !! p = none
    · obtain ⟨p, hp0, hpn⟩ := hp
      exact ⟨[], _, _, [], BaseStep.FuncAllocS v p σ₁ hp0 hpn⟩
    · exact ⟨[], _, _, [], BaseStep.FuncAllocOomS v σ₁ (fun p hp0 hpn => hp ⟨p, hp0, hpn⟩)⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  imod Hclose
  cases Hstep with
  | FuncAllocS _ p _ hp0 hpn =>
    icases (bmemCtx_eq _).1 $$ Hσ with ⟨Hbytes, Hfr, Hbl, Hfn, %Hwf⟩
    imod ghost_map_insert_persist p v hpn $$ Hfn with ⟨Hfn, #Hp⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hbytes Hfr Hbl Hfn]
    · iexists { σ₁.1.bmem with funcs := <[p := v]> σ₁.1.bmem.funcs }
      isplitr
      · ipureintro; rfl
      iapply (bmemCtx_eq _).2
      iframe
      ipureintro; exact Hwf
    iapply wp_value'
    iapply HΦ
    isplitr
    · unfold isFunc; iexact Hp
    · ipureintro; exact hp0
  | FuncAllocOomS =>
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists σ₁.1.bmem
      isplitr
      · ipureintro; rfl
      iexact Hσ
    iapply IH
    inext
    iexact HΦ

theorem wp_func_load (p : w64) (v : val) :
    {{ isFunc (GF := GF) p v }} (FuncLoad (Val #p)) @ s; E {{ RET v; True }} := by
  unfold isFunc
  iintro %Φ #Hf HΦ
  iapply wp_lift_atomic_bmem_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases (bmemCtx_eq _).1 $$ Hσ with ⟨Hbytes, Hfr, Hbl, Hfn, Hwf⟩
  icases ghost_map_lookup $$ Hfn Hf with %Hlk
  ihave Hσ : bmemCtx σ₁.1.bmem $$ [Hbytes Hfr Hbl Hfn Hwf]
  · iapply (bmemCtx_eq _).2; iframe
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.FuncLoadS p v σ₁ Hlk⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  generalize hv : (#p : val) = v' at Hstep
  cases Hstep with
  | FuncLoadS p' w _ Hlk' =>
    cases intoVal_w64_inj hv
    rw [Hlk] at Hlk'; cases Hlk'
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists σ₁.1.bmem
      isplitr
      · ipureintro; rfl
      iexact Hσ
    iexists v
    isplit
    · ipureintro; rfl
    iapply HΦ; itrivial

end lemmas

end Perennial
