/-
WPs of the byte primitives: `AllocBytes`, and the byte atomics `LoadBytes`, `SwapBytes`,
`AddBytes` and `CmpXchgBytes`, over `bytesPointsto l dq bs`, the heap points-tos of the bytes
`bs` from `l` on.
-/
module

public import Perennial.GooseLang.Lifting

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open goose_heap

/-! ## The encoding -/

section encoding
variable [GooseExts]

theorem natBytes_length (w m : Nat) : (natBytes w m).length = w := by
  induction w generalizing m <;> simp_all [natBytes]

theorem bytesNat_natBytes (w m : Nat) : bytesNat (natBytes w m) = m % 256 ^ w := by
  induction w generalizing m with
  | zero => simp [natBytes, bytesNat, Nat.mod_one]
  | succ w ih =>
    simp only [natBytes, bytesNat, ih]
    rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from rfl, Nat.pow_succ,
      Nat.mul_comm (256 ^ w) 256, Nat.mod_mul]

theorem valBytes_length {w : Nat} {v : val} {bs : List w8} (h : valBytes w v = some bs) :
    bs.length = w := by
  unfold valBytes at h
  split at h <;> (try cases h) <;> simp [natBytes_length]

theorem bytesVal_length {w : Nat} {bs : List w8} {v : val} (h : bytesVal w bs = some v) :
    bs.length = w := by
  unfold bytesVal at h
  split at h
  · assumption
  · cases h

theorem bytesVal_not_panic {w : Nat} {bs : List w8} {v : val} (h : bytesVal w bs = some v) :
    v.isPanic = false := by
  unfold bytesVal at h
  split at h
  · split at h <;> first | (cases h; rfl) | cases h
  · cases h

/-- Decoding the bytes of a value gives the value back. -/
theorem bytesVal_valBytes {w : Nat} {v : val} {bs : List w8} (h : valBytes w v = some bs) :
    bytesVal w bs = some v := by
  unfold valBytes at h
  split at h <;> cases h <;>
    simp [bytesVal, natBytes_length, bytesNat_natBytes, BitVec.toNat_lt_twoPow_of_le,
      show (256 : Nat) ^ 1 = 2 ^ 8 from rfl, show (256 : Nat) ^ 2 = 2 ^ 16 from rfl,
      show (256 : Nat) ^ 4 = 2 ^ 32 from rfl, show (256 : Nat) ^ 8 = 2 ^ 64 from rfl,
      Nat.mod_eq_of_lt (BitVec.isLt _)]

end encoding

/-! ## Inversion of the byte steps -/

section inversion
variable [GooseExts] [GooseSemantics] [GoGlobalContext]
variable {σ σ' : CfgState} {κ : List Observation} {e' : Expr} {efs : List Expr}

theorem baseStep_AllocBytes_inv {w : Nat} {v : val}
    (h : BaseStep (AllocBytes w (Val v)) σ κ e' σ' efs) :
    ∃ bs l, valBytes w v = some bs ∧ 0 < l.addr ∧ (w : Int) ∣ l.addr ∧
      (∀ k < w, σ.1.heap !! (l +ₗ (k : Int)) = none) ∧
      κ = [] ∧ e' = Val #l ∧ σ' = setHeap (setBytes l bs) σ ∧ efs = [] := by
  cases h; exact ⟨_, _, ‹_›, ‹_›, ‹_›, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_LoadBytes_inv {w : Nat} {v : val}
    (h : BaseStep (LoadBytes w (Val v)) σ κ e' σ' efs) :
    ∃ l bs v', v = #l ∧ (w : Int) ∣ l.addr ∧ BytesAt σ l bs true ∧ bytesVal w bs = some v' ∧
      κ = [] ∧ e' = Val v' ∧ σ' = σ ∧ efs = [] := by
  cases h; exact ⟨_, _, _, rfl, ‹_›, ‹_›, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_SwapBytes_inv {w : Nat} {v1 v2 : val}
    (h : BaseStep (SwapBytes w (Val v1) (Val v2)) σ κ e' σ' efs) :
    ∃ l bs v0 bs', v1 = #l ∧ (w : Int) ∣ l.addr ∧ BytesAt σ l bs false ∧
      bytesVal w bs = some v0 ∧ valBytes w v2 = some bs' ∧
      κ = [] ∧ e' = Val v0 ∧ σ' = setHeap (setBytes l bs') σ ∧ efs = [] := by
  cases h; exact ⟨_, _, _, _, rfl, ‹_›, ‹_›, ‹_›, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_AddBytes_inv {w : Nat} {v1 v2 : val}
    (h : BaseStep (AddBytes w (Val v1) (Val v2)) σ κ e' σ' efs) :
    ∃ l bs v0 v' bs', v1 = #l ∧ (w : Int) ∣ l.addr ∧ BytesAt σ l bs false ∧
      bytesVal w bs = some v0 ∧ atomicAddEval v0 v2 = some v' ∧ valBytes w v' = some bs' ∧
      κ = [] ∧ e' = Val v' ∧ σ' = setHeap (setBytes l bs') σ ∧ efs = [] := by
  cases h; exact ⟨_, _, _, _, _, rfl, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_CmpXchgBytes_inv {w : Nat} {v0 v12 : val}
    (h : BaseStep (CmpXchgBytes w (Val v0) (Val v12)) σ κ e' σ' efs) :
    ∃ l bs vl v1 v2, v0 = #l ∧ v12 = PairV v1 v2 ∧ (w : Int) ∣ l.addr ∧
      bytesVal w bs = some vl ∧ κ = [] ∧ efs = [] ∧
      ((vl ≠ v1 ∧ BytesAt σ l bs true ∧ e' = Val (PairV vl #false) ∧ σ' = σ) ∨
       (vl = v1 ∧ BytesAt σ l bs false ∧ e' = Val (PairV vl #true) ∧
        ∃ bs', valBytes w v2 = some bs' ∧ σ' = setHeap (setBytes l bs') σ)) := by
  cases h with
  | CmpXchgBytesFailS =>
    exact ⟨_, _, _, _, _, rfl, rfl, ‹_›, ‹_›, rfl, rfl, .inl ⟨‹_›, ‹_›, rfl, rfl⟩⟩
  | CmpXchgBytesSucS =>
    exact ⟨_, _, _, _, _, rfl, rfl, ‹_›, ‹_›, rfl, rfl, .inr ⟨‹_›, ‹_›, rfl, _, ‹_›, rfl⟩⟩

/-- Two byte lists at the same cells, of the same length, are equal. -/
theorem BytesAt_unique {l : Loc} {bs bs' : List w8} {r r' : Bool} (h : BytesAt σ l bs r)
    (h' : BytesAt σ l bs' r') (hlen : bs.length = bs'.length) : bs = bs' := by
  induction bs generalizing l bs' with
  | nil => cases bs' <;> simp_all
  | cons b bs ih =>
    cases bs' with
    | nil => simp at hlen
    | cons b' bs' =>
      obtain ⟨⟨n, hb, _⟩, hrest⟩ := h
      obtain ⟨⟨n', hb', _⟩, hrest'⟩ := h'
      rw [hb] at hb'; cases hb'
      rw [ih hrest hrest' (by simpa using hlen)]

/-- An address `w` divides, above every allocated cell. -/
theorem exists_fresh_aligned (σ : CfgState) (w : Nat) (hw : 0 < w) :
    ∃ l : Loc, 0 < l.addr ∧ (w : Int) ∣ l.addr ∧
      ∀ k : Nat, σ.1.heap !! (l +ₗ (k : Int)) = none := by
  have hpos := freshLoc_pos σ.1.heap.domList
  have hgt := freshLoc_gt σ.1.heap.domList
  generalize freshLoc σ.1.heap.domList = f at hpos hgt
  have hle : f.addr ≤ (w : Int) * f.addr := by
    have h1 : (1 : Int) ≤ w := by omega
    have := Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt hpos)
    omega
  refine ⟨⟨w * f.addr⟩, show (0 : Int) < w * f.addr by omega, ⟨f.addr, rfl⟩, ?_⟩
  intro k
  cases h : σ.1.heap !! (⟨w * f.addr⟩ +ₗ (k : Int)) with
  | none => rfl
  | some _ =>
    have hm := (GMap.mem_dom_list σ.1.heap _).mpr (by rw [h]; rfl)
    have := hgt _ hm
    simp only [Loc.add] at this
    omega

end inversion

/-! ## Atomicity of the byte primitives -/

section atomic
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

local macro "solve_sub_redexes" : tactic =>
  `(tactic| (intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl))

instance alloc_bytes_atomic (a : Language.Atomicity) (w : Nat) (v : val) :
    Language.Atomic a (AllocBytes w (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

instance load_bytes_atomic (a : Language.Atomicity) (w : Nat) (v : val) :
    Language.Atomic a (LoadBytes w (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

instance swap_bytes_atomic (a : Language.Atomicity) (w : Nat) (v1 v2 : val) :
    Language.Atomic a (SwapBytes w (Val v1) (Val v2)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

instance add_bytes_atomic (a : Language.Atomicity) (w : Nat) (v1 v2 : val) :
    Language.Atomic a (AddBytes w (Val v1) (Val v2)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

instance cmpxchg_bytes_atomic (a : Language.Atomicity) (w : Nat) (v1 v2 : val) :
    Language.Atomic a (CmpXchgBytes w (Val v1) (Val v2)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h <;> rfl) (by solve_sub_redexes)

end atomic

/-! ## Byte points-tos -/

section bytes
variable [GooseExts] {GF : BundledGFunctors} [hG : NaHeapGS Loc val GF]
open ProofMode

/-- The heap points-tos of the bytes `bs`, from `l` on. -/
noncomputable def bytesPointsto (l : Loc) (dq : DFrac) : List w8 → IProp GF
  | [] => iprop(True)
  | b :: bs => iprop(heapPointsto l dq (LitV (LitByte b)) ∗ bytesPointsto (l +ₗ 1) dq bs)

instance bytesPointsto_timeless (l : Loc) (dq : DFrac) (bs : List w8) :
    Timeless (bytesPointsto (hG := hG) l dq bs) := by
  induction bs generalizing l <;> unfold bytesPointsto <;> infer_instance

end bytes

/-! ## Lifting -/

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

open EctxLanguage ProofMode

theorem valBytes_pos {w : Nat} {v : val} {bs : List w8} (h : valBytes w v = some bs) : 0 < w := by
  unfold valBytes at h
  split at h <;> first | omega | cases h

theorem valBytes_not_panic {w : Nat} {v : val} {bs : List w8} (h : valBytes w v = some bs) :
    v.isPanic = false := by
  unfold valBytes at h
  split at h <;> first | rfl | cases h

theorem bytesPointsto_lookup (σ : CfgState) (l : Loc) (dq : DFrac) (bs : List w8) :
    naHeapCtx tls σ.1.heap ⊢ bytesPointsto (GF := GF) l dq bs -∗ ⌜BytesAt σ l bs true⌝ := by
  induction bs generalizing l with
  | nil => iintro _ _; ipureintro; trivial
  | cons b bs ih =>
    unfold bytesPointsto
    iintro Hσ ⟨Hb, Hbs⟩
    icases heapPointsto_na_acc l dq _ $$ Hb with ⟨Hb, _⟩
    icases na_heap_read tls σ.1.heap l dq _ $$ Hσ Hb with %⟨lk, n, Heq, Hlock⟩
    icases ih (l +ₗ 1) $$ Hσ Hbs with %Hrest
    ipureintro
    cases lk with
    | Writing => cases Hlock
    | Reading n' => exact ⟨⟨n', Heq, .inl rfl⟩, Hrest⟩

theorem bytesPointsto_lookup_1 (σ : CfgState) (l : Loc) (bs : List w8) :
    naHeapCtx tls σ.1.heap ⊢ bytesPointsto (GF := GF) l (.own 1) bs -∗ ⌜BytesAt σ l bs false⌝ := by
  induction bs generalizing l with
  | nil => iintro _ _; ipureintro; trivial
  | cons b bs ih =>
    unfold bytesPointsto
    iintro Hσ ⟨Hb, Hbs⟩
    icases heapPointsto_na_acc l (.own 1) _ $$ Hb with ⟨Hb, _⟩
    icases na_heap_read_1 tls σ.1.heap l _ $$ Hσ Hb with %⟨lk, Heq, Hlock⟩
    icases ih (l +ₗ 1) $$ Hσ Hbs with %Hrest
    ipureintro
    cases lk with
    | Writing => cases Hlock
    | Reading n' =>
      simp only [tls_Reading, LockState.RSt.injEq] at Hlock; subst Hlock
      exact ⟨⟨0, Heq, .inr rfl⟩, Hrest⟩

theorem bytesPointsto_write (h : GMap Loc (NonAtomic val)) (l : Loc) (bs bs' : List w8)
    (hlen : bs'.length = bs.length) :
    naHeapCtx tls h ⊢ bytesPointsto (GF := GF) l (.own 1) bs -∗
      |==> (naHeapCtx tls (setBytes l bs' h) ∗ bytesPointsto l (.own 1) bs') := by
  induction bs generalizing l bs' h with
  | nil =>
    cases bs' with
    | nil => simp only [setBytes, bytesPointsto]; iintro Hσ _; imodintro; iframe Hσ
    | cons => simp at hlen
  | cons b bs ih =>
    cases bs' with
    | nil => simp at hlen
    | cons b' bs' =>
      simp only [setBytes, Free]
      unfold bytesPointsto
      iintro Hσ ⟨Hb, Hbs⟩
      icases heapPointsto_na_acc l (.own 1) _ $$ Hb with ⟨Hb, Hb_rest⟩
      imod na_heap_write tls h l (Reading 0) _ (LitV (LitByte b')) rfl $$ Hσ Hb with ⟨Hσ, Hb⟩
      imod ih _ (l +ₗ 1) bs' (by simpa using hlen) $$ Hσ Hbs with ⟨Hσ, Hbs⟩
      imodintro
      iframe Hσ Hbs
      iapply Hb_rest $$ Hb

theorem bytesPointsto_alloc (h : GMap Loc (NonAtomic val)) (l : Loc) (bs : List w8)
    (hpos : 0 < l.addr) (hfresh : ∀ k < bs.length, h !! (l +ₗ (k : Int)) = none) :
    naHeapCtx tls h ⊢
      |==> (naHeapCtx tls (setBytes l bs h) ∗ bytesPointsto (GF := GF) l (.own 1) bs) := by
  induction bs generalizing l h with
  | nil => simp only [setBytes, bytesPointsto]; iintro Hσ; imodintro; iframe Hσ
  | cons b bs ih =>
    have h0 : h !! l = none := by simpa using hfresh 0 (by simp)
    have hnn : l ≠ null := fun e => by rw [e] at hpos; simp [null] at hpos
    have hfresh' : ∀ k < bs.length,
        (<[l := (Reading 0, LitV (LitByte b))]> h) !! (l +ₗ 1 +ₗ (k : Int)) = none := by
      intro k hk
      rw [GMap.lookup_insert_ne _ _ (by intro e; cases l; simp [Loc.add] at e; omega)]
      have := hfresh (k + 1) (by simp; omega)
      simpa [Int.add_comm, Int.add_assoc] using this
    simp only [setBytes, Free]
    unfold bytesPointsto
    iintro Hσ
    imod na_heap_alloc tls h l (LitV (LitByte b)) (Reading 0) h0 rfl $$ Hσ with ⟨Hσ, Hb⟩
    imod ih _ (l +ₗ 1) (by simp [Loc.add]; omega) hfresh' $$ Hσ with ⟨Hσ, Hbs⟩
    imodintro
    iframe Hσ Hbs
    iapply na_pointsto_to_heap l _ _ hnn $$ Hb

theorem wp_alloc_bytes (w : Nat) (v : val) (bs : List w8) (Hv : valBytes w v = some bs) :
    {{ (True : IProp GF) }} (AllocBytes w (Val v)) @ s; E
    {{ l, RET #l; ⌜(w : Int) ∣ l.addr⌝ ∗ bytesPointsto l (.own 1) bs }} := by
  have Hvp := valBytes_not_panic Hv
  iintro %Φ _ HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipureintro
    obtain ⟨l, hpos, hal, hfr⟩ := exists_fresh_aligned σ₁ w (valBytes_pos Hv)
    exact ⟨[], _, _, [], BaseStep.AllocBytesS w v bs l σ₁ Hv hpos hal (fun k _ => hfr k)⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨bs', l, Hv', hpos, hal, hfr, rfl, rfl, rfl, rfl⟩ := baseStep_AllocBytes_inv Hstep
  rw [Hv] at Hv'; cases Hv'
  imod bytesPointsto_alloc σ₁.1.heap l bs hpos
    (fun k hk => hfr k (by rw [valBytes_length Hv] at hk; exact hk)) $$ Hσ with ⟨Hσ, Hbs⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists #l
  isplit
  · ipureintro; rfl
  iapply HΦ
  iframe Hbs
  ipureintro; exact hal

theorem wp_load_bytes (w : Nat) (l : Loc) (dq : DFrac) (bs : List w8) (v : val)
    (Hv : bytesVal w bs = some v) (Hal : (w : Int) ∣ l.addr) :
    {{ ▷ bytesPointsto (GF := GF) l dq bs }} (LoadBytes w (Val #l)) @ s; E
    {{ RET v; bytesPointsto l dq bs }} := by
  iintro %Φ >Hbs HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases bytesPointsto_lookup σ₁ l dq bs $$ Hσ Hbs with %Hat
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.LoadBytesS w l bs v σ₁ Hal Hat Hv⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', bs', v', Hl', _, Hat', Hv', rfl, rfl, rfl, rfl⟩ := baseStep_LoadBytes_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases BytesAt_unique Hat Hat' (by rw [bytesVal_length Hv, bytesVal_length Hv'])
  rw [Hv] at Hv'; cases Hv'
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists v
  isplit
  · ipureintro; rfl
  iapply HΦ $$ Hbs

theorem wp_swap_bytes (w : Nat) (l : Loc) (bs bs' : List w8) (v0 v : val)
    (Hv0 : bytesVal w bs = some v0) (Hv : valBytes w v = some bs') (Hal : (w : Int) ∣ l.addr) :
    {{ ▷ bytesPointsto (GF := GF) l (.own 1) bs }} (SwapBytes w (Val #l) (Val v)) @ s; E
    {{ RET v0; bytesPointsto l (.own 1) bs' }} := by
  have Hvp := valBytes_not_panic Hv
  iintro %Φ >Hbs HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases bytesPointsto_lookup_1 σ₁ l bs $$ Hσ Hbs with %Hat
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.SwapBytesS w l bs v0 v bs' σ₁ Hal Hat Hv0 Hv⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', b1, v0', b2, Hl', _, Hat', Hv0', Hv', rfl, rfl, rfl, rfl⟩ :=
    baseStep_SwapBytes_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases BytesAt_unique Hat Hat' (by rw [bytesVal_length Hv0, bytesVal_length Hv0'])
  rw [Hv0] at Hv0'; cases Hv0'
  rw [Hv] at Hv'; cases Hv'
  imod bytesPointsto_write σ₁.1.heap l bs bs'
    (by rw [valBytes_length Hv, bytesVal_length Hv0]) $$ Hσ Hbs with ⟨Hσ, Hbs⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists v0
  isplit
  · ipureintro; rfl
  iapply HΦ $$ Hbs

theorem wp_add_bytes (w : Nat) (l : Loc) (bs bs' : List w8) (v0 v v' : val)
    (Hv0 : bytesVal w bs = some v0) (Hev : atomicAddEval v0 v = some v')
    (Hv' : valBytes w v' = some bs') (Hal : (w : Int) ∣ l.addr) :
    {{ ▷ bytesPointsto (GF := GF) l (.own 1) bs }} (AddBytes w (Val #l) (Val v)) @ s; E
    {{ RET v'; bytesPointsto l (.own 1) bs' }} := by
  have Hvp := atomicAddEval_not_panic Hev
  iintro %Φ >Hbs HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases bytesPointsto_lookup_1 σ₁ l bs $$ Hσ Hbs with %Hat
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.AddBytesS w l bs v0 v v' bs' σ₁ Hal Hat Hv0 Hev Hv'⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', b1, v0', v'', b2, Hl', _, Hat', Hv0', Hev', Hv'', rfl, rfl, rfl, rfl⟩ :=
    baseStep_AddBytes_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases BytesAt_unique Hat Hat' (by rw [bytesVal_length Hv0, bytesVal_length Hv0'])
  rw [Hv0] at Hv0'; cases Hv0'
  rw [Hev] at Hev'; cases Hev'
  rw [Hv'] at Hv''; cases Hv''
  imod bytesPointsto_write σ₁.1.heap l bs bs'
    (by rw [valBytes_length Hv', bytesVal_length Hv0]) $$ Hσ Hbs with ⟨Hσ, Hbs⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists v'
  isplit
  · ipureintro; rfl
  iapply HΦ $$ Hbs

theorem wp_cmpxchg_bytes_fail (w : Nat) (l : Loc) (dq : DFrac) (bs : List w8) (vl v1 v2 : val)
    (Hvl : bytesVal w bs = some vl) (Hne : vl ≠ v1) (Hal : (w : Int) ∣ l.addr) :
    {{ ▷ bytesPointsto (GF := GF) l dq bs }}
      (CmpXchgBytes w (Val #l) (Val (PairV v1 v2))) @ s; E
    {{ RET (PairV vl #false); bytesPointsto l dq bs }} := by
  iintro %Φ >Hbs HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases bytesPointsto_lookup σ₁ l dq bs $$ Hσ Hbs with %Hat
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.CmpXchgBytesFailS w l bs vl v1 v2 σ₁ Hal Hat Hvl Hne⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', bs', vl', v1', v2', Hl', Hp, _, Hvl', rfl, rfl, Hcase⟩ :=
    baseStep_CmpXchgBytes_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases Hp
  rcases Hcase with ⟨_, Hat', rfl, rfl⟩ | ⟨Heq, Hat', _, _⟩
  · cases BytesAt_unique Hat Hat' (by rw [bytesVal_length Hvl, bytesVal_length Hvl'])
    rw [Hvl] at Hvl'; cases Hvl'
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists _; iframe Hσ; ipureintro; rfl
    iexists (PairV vl #false)
    isplit
    · ipureintro; rfl
    iapply HΦ $$ Hbs
  · cases BytesAt_unique Hat Hat' (by rw [bytesVal_length Hvl, bytesVal_length Hvl'])
    rw [Hvl] at Hvl'; cases Hvl'
    exact absurd Heq Hne

theorem wp_cmpxchg_bytes_suc (w : Nat) (l : Loc) (bs bs' : List w8) (vl v1 v2 : val)
    (Hvl : bytesVal w bs = some vl) (Heq : vl = v1) (Hv2 : valBytes w v2 = some bs')
    (Hal : (w : Int) ∣ l.addr) :
    {{ ▷ bytesPointsto (GF := GF) l (.own 1) bs }}
      (CmpXchgBytes w (Val #l) (Val (PairV v1 v2))) @ s; E
    {{ RET (PairV vl #true); bytesPointsto l (.own 1) bs' }} := by
  iintro %Φ >Hbs HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
  iintro %σ₁ Hσ
  icases bytesPointsto_lookup_1 σ₁ l bs $$ Hσ Hbs with %Hat
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.CmpXchgBytesSucS w l bs vl v1 v2 bs' σ₁ Hal Hat Hvl Heq Hv2⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', bs'', vl', v1', v2', Hl', Hp, _, Hvl', rfl, rfl, Hcase⟩ :=
    baseStep_CmpXchgBytes_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases Hp
  rcases Hcase with ⟨Hne, Hat', _, _⟩ | ⟨_, Hat', rfl, bs3, Hv2', rfl⟩
  · cases BytesAt_unique Hat Hat' (by rw [bytesVal_length Hvl, bytesVal_length Hvl'])
    rw [Hvl] at Hvl'; cases Hvl'
    exact absurd Heq Hne
  · cases BytesAt_unique Hat Hat' (by rw [bytesVal_length Hvl, bytesVal_length Hvl'])
    rw [Hvl] at Hvl'; cases Hvl'
    rw [Hv2] at Hv2'; cases Hv2'
    imod bytesPointsto_write σ₁.1.heap l bs bs'
      (by rw [valBytes_length Hv2, bytesVal_length Hvl]) $$ Hσ Hbs with ⟨Hσ, Hbs⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists _; iframe Hσ; ipureintro; rfl
    iexists (PairV vl #true)
    isplit
    · ipureintro; rfl
    iapply HΦ $$ Hbs

end lifting

end Perennial
