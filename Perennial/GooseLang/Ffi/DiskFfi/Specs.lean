/-
Iris reasoning principles for the disk FFI. Port of the non-crash parts of
`src/goose_lang/ffi/disk_ffi/specs.v`.

Differences from the Rocq version:
* No crash reasoning (`ffi_crash_rel`, `ffi_restart`, `disk_array_acc_disc`,
  which uses Perennial's `<bdisc>` modality, is omitted).
* The ghost state uses iris-lean's `genHeapGS` with `gmap Int` as the map type.
* `pointsto_block l q b` is a big separating conjunction over the list
  `Block_to_vals b` (`[∗list] i ↦ v ∈ Block_to_vals b, (l +ₗ i) ↦{q} v`)
  instead of a big separating conjunction over the map `heap_array l ...`.
  Consequently `bindex_of_Z`/`block_byte_index` are not needed and omitted.
* Argument values are `#a` (`into_val`) instead of `LitV (LitInt a)`.
* `ffi_local_start` and the adequacy instance are in
  `Perennial/GooseLang/Ffi/DiskFfi/Adequacy.lean`.
-/
import Iris.BI.Lib.GenHeap
import Perennial.GooseLang.Lifting
import Perennial.GooseLang.Countable
import Perennial.GooseLang.Ffi.DiskFfi.Impl
import Perennial.GooseLang.Ffi.GenHeap

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

class diskGS (GF : BundledGFunctors) where
  diskG_gen_heapG : genHeapGS Int Block GF (gmap Int)

class disk_preG (GF : BundledGFunctors) where
  disk_preG_gen_heapG : genHeapPreS Int Block GF (gmap Int)

/-- The GooseLang `ffi_interp` for the disk. -/
@[reducible] def disk_interp : ffi_interp disk_model where
  ffiLocalGS := diskGS
  ffiGlobalGS _ := Unit
  ffi_local_ctx hL d := genHeapInterp (G := hL.diskG_gen_heapG) (d : disk_state)
  ffi_global_ctx _ _ := iprop(True)

/-- Rocq `l d↦{dq} b`. -/
def disk_pointsto {GF : BundledGFunctors} (hL : diskGS GF) (a : Int) (dq : DFrac) (b : Block) :
    IProp GF :=
  pointsTo (G := hL.diskG_gen_heapG) a dq b

instance disk_pointsto_timeless {GF : BundledGFunctors} (hL : diskGS GF) (a : Int) (dq : DFrac)
    (b : Block) : Timeless (disk_pointsto hL a dq b) := by
  unfold disk_pointsto; infer_instance

/-! ## `heap_array` -/

section heap_array
variable {V : Type}

theorem heap_array_lookup_lt (l : loc) (vs : List V) (i : Int) (h : i < 0) :
    heap_array l vs !! (l +ₗ i) = none := by
  induction vs generalizing l i with
  | nil => rfl
  | cons v vs ih =>
    show (<[l := v]> (heap_array (l +ₗ 1) vs)) !! (l +ₗ i) = none
    rw [gmap.lookup_insert_ne _ _ (fun e => by have := loc_add_eq_inv l i e.symm; omega)]
    have := ih (l +ₗ 1) (i - 1) (by omega)
    rwa [loc_add_assoc, show 1 + (i - 1) = i by omega] at this

end heap_array

section na_heap_alloc
variable [ext : ffi_syntax] {GF : BundledGFunctors} [hG : na_heapGS loc val GF]

theorem na_heap_alloc_list (σ : gmap loc (nonAtomic val)) (l : loc) (vs : List val)
    (Hfresh : ∀ i : Int, σ !! (l +ₗ i) = none) :
    ⊢@{IProp GF} na_heap_ctx tls σ ==∗ na_heap_ctx tls (heap_array l (vs.map Free) ∪ σ) ∗
      [∗list] i ↦ v ∈ vs, na_heap_pointsto (l +ₗ (i : Int)) (.own 1) v := by
  induction vs generalizing l with
  | nil =>
    iintro H
    imodintro
    have : heap_array l (([] : List val).map Free) ∪ σ = σ := by
      apply gmap.ext; intro k; rfl
    rw [this]
    iframe H
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | cons v vs ih =>
    iintro H
    imod ih (l +ₗ 1) (fun i => by rw [loc_add_assoc]; exact Hfresh _) $$ H with ⟨H, Hpts⟩
    have Hnone : (heap_array (l +ₗ 1) (vs.map Free) ∪ σ) !! l = none := by
      refine (gmap.lookup_union_None _ _ _).mpr ⟨?_, ?_⟩
      · have := heap_array_lookup_lt (l +ₗ 1) (vs.map Free) (-1) (by omega)
        rwa [loc_add_assoc, show (1 : Int) + -1 = 0 by omega, loc_add_0] at this
      · have := Hfresh 0; rwa [loc_add_0] at this
    imod na_heap_alloc tls _ l v (Reading 0) Hnone rfl $$ H with ⟨H, Hl⟩
    imodintro
    have Heq : heap_array l ((v :: vs).map Free) ∪ σ =
        <[l := (Reading 0, v)]> (heap_array (l +ₗ 1) (vs.map Free) ∪ σ) :=
      (gmap.insert_union_l _ _ _ _).symm
    rw [Heq]
    iframe H
    iapply BigSepL.bigSepL_cons.2
    have Hk : ∀ k : Nat, l +ₗ ((k + 1 : Nat) : Int) = l +ₗ 1 +ₗ (k : Int) := by
      intro k; rw [loc_add_assoc]; congr 1; omega
    simp only [Int.natCast_zero, loc_add_0, Hk]
    iframe

end na_heap_alloc

/-! ## Disk lifting lemmas -/

section disk
attribute [local instance] disk_op disk_model disk_semantics disk_interp
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : gooseGlobalGS hlc GF] [L : gooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

abbrev goose_diskGS : diskGS GF := L.goose_ffiLocalGS

/- Rocq notations `l d↦{dq} v` and `l d↦ v`. -/
namespace disk_ffi
scoped notation:50 l:51 " d↦{" dq "} " v:50 => disk_pointsto goose_diskGS l dq v
scoped notation:50 l:51 " d↦ " v:50 => disk_pointsto goose_diskGS l (DFrac.own 1) v
end disk_ffi
open disk_ffi

theorem disk_local_ctx_eq (d : disk_state) :
    ffi_local_ctx L.goose_ffiLocalGS d ⊣⊢
      genHeapInterp (G := (goose_diskGS (L := L)).diskG_gen_heapG) d := .rfl

/-- Rocq `pointsto_block` (see the file header for the representation). -/
def pointsto_block (l : loc) (q : DFrac) (b : Block) : IProp GF :=
  iprop([∗list] i ↦ v ∈ Block_to_vals b, heap_pointsto (l +ₗ (i : Int)) q v)

instance pointsto_block_timeless (l : loc) (q : DFrac) (b : Block) :
    Timeless (pointsto_block (GF := GF) l q b) := by
  unfold pointsto_block; infer_instance

theorem pointsto_block_extract (i : Int) (l : loc) (q : DFrac) (b : Block)
    (Hlow : 0 ≤ i) (Hhi : i < 4096) :
    ⊢ pointsto_block (GF := GF) l q b -∗
      ∃ v, heap_pointsto (l +ₗ i) q v ∗ ⌜(Block_to_vals b)[i.toNat]? = some v⌝ := by
  have hlen : i.toNat < (Block_to_vals b).length := by
    rw [length_Block_to_vals]; unfold block_bytes; omega
  have hlk := List.getElem?_eq_getElem hlen
  unfold pointsto_block
  iintro Hm
  icases BigSepL.bigSepL_lookup hlk $$ Hm with Hi
  iexists _
  rw [show ((i.toNat : Nat) : Int) = i by omega]
  iframe Hi
  ipureintro; exact hlk

/-- The bytes of a block are in the heap. -/
def block_in_heap (h : gmap loc (nonAtomic val)) (l : loc) (b : Block) : Prop :=
  ∀ i : Int, 0 ≤ i → i < 4096 →
    match h !! (l +ₗ i) with
    | some (Reading _, v) => (Block_to_vals b)[i.toNat]? = some v
    | _ => False

theorem heap_valid_block (l : loc) (b : Block) (q : DFrac) (σ : gmap loc (nonAtomic val)) :
    ⊢ na_heap_ctx (hG := L.goose_na_heapGS) tls σ -∗ pointsto_block (GF := GF) l q b -∗
      ⌜block_in_heap σ l b⌝ := by
  iintro Hσ Hm
  unfold block_in_heap
  iapply pure_forall.mpr
  iintro %i
  by_cases hi : 0 ≤ i ∧ i < 4096
  · icases pointsto_block_extract i l q b hi.1 hi.2 $$ Hm with ⟨%v, Hi, %Hv⟩
    icases heap_pointsto_na_acc _ _ _ $$ Hi with ⟨Hi, -⟩
    icases na_heap_read tls σ _ q _ $$ Hσ Hi with %⟨lk, n, Heq, Hlock⟩
    ipureintro
    intro _ _
    rw [Heq]
    cases lk with
    | Writing => cases Hlock
    | Reading _ => exact Hv
  · ipureintro
    intro h0 h1
    exact absurd ⟨h0, h1⟩ hi

theorem Block_to_vals_ext_eq (b1 b2 : Block)
    (H : ∀ i : Int, 0 ≤ i → i < 4096 →
      (Block_to_vals b1)[i.toNat]? = (Block_to_vals b2)[i.toNat]?) :
    b1 = b2 := by
  have Hl : Block_to_vals b1 = Block_to_vals b2 := by
    apply List.ext_getElem?
    intro n
    by_cases hn : n < 4096
    · have := H n (by omega) (by omega)
      simpa using this
    · rw [List.getElem?_eq_none (by rw [length_Block_to_vals]; unfold block_bytes; omega),
        List.getElem?_eq_none (by rw [length_Block_to_vals]; unfold block_bytes; omega)]
  have Hinj : Function.Injective (fun b : w8 => (#b : val)) := GoGlobalContext.into_val_inj_w8
  have := (List.map_inj_right (fun x y h => Hinj h)).mp Hl
  exact Vector.toList_inj.mp this

theorem block_in_heap_inj {h : gmap loc (nonAtomic val)} {l : loc} {b1 b2 : Block}
    (H1 : block_in_heap h l b1) (H2 : block_in_heap h l b2) : b1 = b2 := by
  apply Block_to_vals_ext_eq
  intro i h0 h1
  have e1 := H1 i h0 h1
  have e2 := H2 i h0 h1
  revert e1 e2
  rcases h !! (l +ₗ i) with _ | ⟨m, v⟩
  · simp
  · cases m with
    | Writing => simp
    | Reading _ => intro e1 e2; rw [e1, e2]

theorem disk_ffi_step_ReadOp_inv {v : val} {σg σg' : cfg_state} {e' : expr}
    (h : disk_ffi_step .ReadOp v σg e' σg') :
    ∃ (a : w64) (b : Block) (l : loc), v = #a ∧ disk_world σg.1 !! uint.Z a = some b ∧
      isFresh σg l ∧ e' = Val (#l) ∧
      σg' = (state_insert_list l (Block_to_vals b) σg.1, σg.2) := by
  cases h with
  | ReadS a b l _ h1 h2 => exact ⟨a, b, l, rfl, h1, h2, rfl, rfl⟩

theorem disk_ffi_step_WriteOp_inv {v : val} {σg σg' : cfg_state} {e' : expr}
    (h : disk_ffi_step .WriteOp v σg e' σg') :
    ∃ (a : w64) (l : loc) (b0 b : Block), v = PairV (#a) (#l) ∧
      disk_world σg.1 !! uint.Z a = some b0 ∧ block_in_heap σg.1.heap l b ∧ e' = Val (#()) ∧
      σg' = ({ σg.1 with world := <[uint.Z a := b]> (disk_world σg.1) }, σg.2) := by
  cases h with
  | WriteS a l b0 b _ h1 h2 => exact ⟨a, l, b0, b, rfl, h1, h2, rfl, rfl⟩

open EctxLanguage

theorem wp_ReadOp (a : w64) (q : DFrac) (b : Block) :
    {{ ▷ disk_pointsto (goose_diskGS (L := L)) (uint.Z a) q b }} (ExternalOp DiskOp.ReadOp (Val (#a))) @ s; E
    {{ (l : loc), RET #l; uint.Z a d↦{q} b ∗ pointsto_block l (.own 1) b }} := by
  iintro %Φ >Ha HΦ
  iapply goose_wp_lift_atomic_base_step_no_fork rfl rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  icases (disk_local_ctx_eq _).mp $$ Hffi with Hffi
  unfold disk_pointsto
  icases genHeap_lookup (G := (goose_diskGS (L := L)).diskG_gen_heapG) $$ Hffi Ha with %Hd
  have Hd' : disk_world σ₁.1 !! uint.Z a = some b := Hd
  imodintro
  isplitr
  · ipureintro
    obtain ⟨l, hl⟩ := exists_isFresh σ₁
    exact ⟨[], _, _, [], base_step.ExternalOpS _ _ _ σ₁ _ (disk_ffi_step.ReadS a b l σ₁ Hd' hl)⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  have Hbs : base_step _ _ _ _ _ _ := Hstep
  cases Hbs with
  | ExternalOpS _ _ _ _ _ Hffi_step =>
  obtain ⟨a', b', l, Ha', Hd'', Hfresh, rfl, rfl⟩ := disk_ffi_step_ReadOp_inv Hffi_step
  cases GoGlobalContext.into_val_inj_w64 Ha'
  rw [Hd'] at Hd''
  cases Hd''
  imod na_heap_alloc_list _ l (Block_to_vals b) (fun i => (Hfresh.1 i).2) $$ Hheap
    with ⟨Hheap, Hpts⟩
  imodintro
  isplitr
  · ipureintro; rfl
  isplitl [Hheap Hffi Hgs Hgffi Hproph]
  · iapply (goose_stateInterp_eq _ _ _ _).mpr
    simp only [List.nil_append]
    dsimp only [state_insert_list]
    isplitl [Hheap]
    · iexact Hheap
    isplitl [Hffi]
    · iapply (disk_local_ctx_eq _).mpr; iexact Hffi
    isplitl [Hgs]
    · iexact Hgs
    isplitr
    · ipureintro; exact Hlctx
    isplitl [Hgffi]
    · iexact Hgffi
    iexact Hproph
  iexists #l
  isplit
  · ipureintro; rfl
  iapply HΦ $$ %l
  iframe Ha
  unfold pointsto_block
  iapply BigSepL.bigSepL_mono ?_ $$ Hpts
  intro k x _
  exact na_pointsto_to_heap _ _ _ (Hfresh.1 _).1

theorem wp_WriteOp (a : w64) (b : Block) (q : DFrac) (l : loc) :
    {{ ▷ ((∃ b0, disk_pointsto (goose_diskGS (L := L)) (uint.Z a) (.own 1) b0) ∗
        pointsto_block l q b) }}
      (ExternalOp DiskOp.WriteOp (Val (PairV (#a) (#l)))) @ s; E
    {{ RET #(); uint.Z a d↦ b ∗ pointsto_block l q b }} := by
  iintro %Φ >⟨⟨%b0, Ha⟩, Hl⟩ HΦ
  iapply goose_wp_lift_atomic_base_step_no_fork rfl rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  icases (disk_local_ctx_eq _).mp $$ Hffi with Hffi
  unfold disk_pointsto
  icases genHeap_lookup (G := (goose_diskGS (L := L)).diskG_gen_heapG) $$ Hffi Ha with %Hd
  have Hd' : disk_world σ₁.1 !! uint.Z a = some b0 := Hd
  icases heap_valid_block l b q σ₁.1.heap $$ Hheap Hl with %Hvalid
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], base_step.ExternalOpS _ _ _ σ₁ _
      (disk_ffi_step.WriteS a l b0 b σ₁ Hd' Hvalid)⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  have Hbs : base_step _ _ _ _ _ _ := Hstep
  cases Hbs with
  | ExternalOpS _ _ _ _ _ Hffi_step =>
  obtain ⟨a', l', b0', b', Hv, -, Hvalid', rfl, rfl⟩ := disk_ffi_step_WriteOp_inv Hffi_step
  simp only [val.PairV.injEq] at Hv
  obtain ⟨Ha', Hl'⟩ := Hv
  cases GoGlobalContext.into_val_inj_w64 Ha'
  cases GoGlobalContext.into_val_inj_loc Hl'
  cases block_in_heap_inj Hvalid Hvalid'
  imod genHeap_update' (G := (goose_diskGS (L := L)).diskG_gen_heapG) (v₂ := b)
    $$ [Hffi Ha] with ⟨Hffi, Ha⟩
  · iframe
  imodintro
  isplitr
  · ipureintro; rfl
  isplitl [Hheap Hffi Hgs Hgffi Hproph]
  · iapply (goose_stateInterp_eq _ _ _ _).mpr
    simp only [List.nil_append]
    try dsimp only
    isplitl [Hheap]
    · iexact Hheap
    isplitl [Hffi]
    · iapply (disk_local_ctx_eq _).mpr; iexact Hffi
    isplitl [Hgs]
    · iexact Hgs
    isplitr
    · ipureintro; exact Hlctx
    isplitl [Hgffi]
    · iexact Hgffi
    iexact Hproph
  iexists #()
  isplit
  · ipureintro; rfl
  iapply HΦ
  iframe

/-! ## Disk arrays -/

def disk_array (l : Int) (q : DFrac) (vs : List Block) : IProp GF :=
  iprop([∗list] i ↦ b ∈ vs, (l + (i : Int)) d↦{q} b)

theorem disk_array_cons (l : Int) (q : DFrac) (b : Block) (vs : List Block) :
    disk_array (GF := GF) l q (b :: vs) ⊣⊢ (l d↦{q} b) ∗ disk_array (l + 1) q vs := by
  unfold disk_array
  refine BigSepL.bigSepL_cons.trans ?_
  have Hk : ∀ k : Nat, l + ((k + 1 : Nat) : Int) = l + 1 + (k : Int) := by intro k; omega
  simp only [Int.natCast_zero, Int.add_zero, Hk]
  exact .rfl

theorem disk_array_app (l : Int) (q : DFrac) (vs1 vs2 : List Block) :
    disk_array (GF := GF) l q (vs1 ++ vs2) ⊣⊢
      disk_array l q vs1 ∗ disk_array (l + vs1.length) q vs2 := by
  unfold disk_array
  refine BigSepL.bigSepL_append.trans ?_
  have Hk : ∀ k : Nat, l + ((k + vs1.length : Nat) : Int) = l + vs1.length + (k : Int) := by
    intro k; omega
  simp only [Hk]
  exact .rfl

theorem disk_array_emp (l : Int) (q : DFrac) : disk_array (GF := GF) l q [] ⊣⊢ emp := .rfl

theorem disk_array_split (l : Int) (q : DFrac) (z : Int) (vs : List Block)
    (H : 0 ≤ z ∧ z < vs.length) :
    disk_array (GF := GF) l q vs ⊣⊢
      disk_array l q (vs.take z.toNat) ∗ disk_array (l + z) q (vs.drop z.toNat) := by
  conv => lhs; rw [← List.take_append_drop z.toNat vs]
  refine (disk_array_app l q _ _).trans ?_
  rw [List.length_take, show ((min z.toNat vs.length : Nat) : Int) = z by omega]
  exact .rfl

theorem disk_array_acc (l : Int) (bs : List Block) (z : Int) (b : Block) (q : DFrac)
    (Hpos : 0 ≤ z) (Hlookup : bs[z.toNat]? = some b) :
    ⊢ disk_array (GF := GF) l q bs -∗
      ((l + z) d↦{q} b ∗ ∀ b', (l + z) d↦{q} b' -∗ disk_array l q (bs.set z.toNat b')) := by
  unfold disk_array
  iintro Hl
  icases BigSepL.bigSepL_insert_acc Hlookup $$ Hl with ⟨Hb, Hrest⟩
  rw [show ((z.toNat : Nat) : Int) = z by omega]
  iframe Hb
  iexact Hrest

theorem disk_array_acc_read (l : Int) (bs : List Block) (z : Int) (b : Block) (q : DFrac)
    (Hpos : 0 ≤ z) (Hlookup : bs[z.toNat]? = some b) :
    ⊢ disk_array (GF := GF) l q bs -∗
      ((l + z) d↦{q} b ∗ ((l + z) d↦{q} b -∗ disk_array l q bs)) := by
  iintro Hl
  icases disk_array_acc l bs z b q Hpos Hlookup $$ Hl with ⟨Hb, Hrest⟩
  iframe Hb
  iintro Hb
  have Hset : bs.set z.toNat b = bs := by
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp Hlookup
    exact List.set_getElem_self hlt
  ihave H := Hrest $$ %b Hb
  rw [Hset]
  iexact H

theorem init_disk_sz_lookup_ge (sz : Nat) (z : Int) (Hle : (sz : Int) ≤ z) :
    init_disk ∅ sz !! z = none := by
  induction sz with
  | zero => rfl
  | succ n ih =>
    show (<[(n : Int) := block0]> (init_disk ∅ n)) !! z = none
    rw [gmap.lookup_insert_ne _ _ (by omega)]
    exact ih (by omega)

theorem disk_array_init_disk (sz : Nat) :
    ([∗map] i ↦ b ∈ init_disk ∅ sz, (i d↦ b : IProp GF)) ⊢
      disk_array 0 (.own 1) (List.replicate sz block0) := by
  induction sz with
  | zero =>
    iintro _
    unfold disk_array
    rw [List.replicate_zero]
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | succ n ih =>
    have Hnone : PartialMap.get? (init_disk ∅ n) (n : Int) = none :=
      init_disk_sz_lookup_ge n n (Int.le_refl _)
    refine (BigSepM.bigSepM_insert (Φ := fun i b => (i d↦ b : IProp GF)) Hnone).1.trans ?_
    rw [List.replicate_succ']
    refine (sep_mono_right ih).trans ?_
    refine Entails.trans ?_ (disk_array_app 0 _ _ _).2
    refine sep_comm.1.trans (sep_mono_right ?_)
    rw [List.length_replicate]
    unfold disk_array
    refine Entails.trans ?_ BigSepL.bigSepL_singleton.2
    simp only [Int.natCast_zero, Int.add_zero, Int.zero_add]
    exact .rfl

end disk

end Perennial
