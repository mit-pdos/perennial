/-
Iris reasoning principles for the disk FFI (non-crash parts only).

* No crash reasoning: there is no crash relation or restart rule for the
  disk.
* The ghost state uses iris-lean's `genHeapGS` with `gmap Int` as the map type.
* `pointstoBlock l q b` is a big separating conjunction over the list
  `BlockToVals b` (`[∗list] i ↦ v ∈ BlockToVals b, (l +ₗ i) ↦{q} v`).
* Argument values are written `#a` (`intoVal`).
* `ffiLocalStart` and the adequacy instance are in
  `Perennial/GooseLang/Ffi/DiskFfi/Adequacy.lean`.
-/
module

public import Iris.BI.Lib.GenHeap
public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.Countable
public import Perennial.GooseLang.Ffi.DiskFfi.Impl
public import Perennial.GooseLang.Ffi.GenHeap

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

class DiskGS (GF : BundledGFunctors) where
  diskGGenHeapG : genHeapGS Int Block GF (GMap Int)

class DiskPreG (GF : BundledGFunctors) where
  diskPreGGenHeapG : genHeapPreS Int Block GF (GMap Int)

/-- The GooseLang `FfiInterp` for the disk. -/
@[reducible] def disk_interp : FfiInterp disk_model where
  ffiLocalGS := DiskGS
  ffiGlobalGS _ := Unit
  ffiLocalCtx hL d := genHeapInterp (G := hL.diskGGenHeapG) (d : DiskState)
  ffiGlobalCtx _ _ := iprop(True)

/-- Disk points-to `a d↦{dq} b`: block `a` of the disk holds `b`. -/
def diskPointsto {GF : BundledGFunctors} (hL : DiskGS GF) (a : Int) (dq : DFrac) (b : Block) :
    IProp GF :=
  pointsTo (G := hL.diskGGenHeapG) a dq b

instance diskPointsto_timeless {GF : BundledGFunctors} (hL : DiskGS GF) (a : Int) (dq : DFrac)
    (b : Block) : Timeless (diskPointsto hL a dq b) := by
  unfold diskPointsto; infer_instance


/-! ## Disk lifting lemmas -/

section disk
attribute [local instance] disk_op disk_model disk_semantics disk_interp
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

abbrev gooseDiskGS : DiskGS GF := L.gooseFfiLocalGS

/- Notations `l d↦{dq} v` and `l d↦ v`. -/
namespace disk_ffi
scoped notation:50 l:51 " d↦{" dq "} " v:50 => diskPointsto gooseDiskGS l dq v
scoped notation:50 l:51 " d↦ " v:50 => diskPointsto gooseDiskGS l (DFrac.own 1) v
end disk_ffi
open disk_ffi

theorem disk_local_ctx_eq (d : DiskState) :
    ffiLocalCtx L.gooseFfiLocalGS d ⊣⊢
      genHeapInterp (G := (gooseDiskGS (L := L)).diskGGenHeapG) d := .rfl

/-- Ownership of a block's bytes in the heap at `l` (see the file header for the representation). -/
def pointstoBlock (l : Loc) (q : DFrac) (b : Block) : IProp GF :=
  iprop([∗list] i ↦ v ∈ BlockToVals b, heapPointsto (l +ₗ (i : Int)) q v)

instance pointstoBlock_timeless (l : Loc) (q : DFrac) (b : Block) :
    Timeless (pointstoBlock (GF := GF) l q b) := by
  unfold pointstoBlock; infer_instance

theorem pointstoBlock_extract (i : Int) (l : Loc) (q : DFrac) (b : Block)
    (Hlow : 0 ≤ i) (Hhi : i < 4096) :
    ⊢ pointstoBlock (GF := GF) l q b -∗
      ∃ v, heapPointsto (l +ₗ i) q v ∗ ⌜(BlockToVals b)[i.toNat]? = some v⌝ := by
  have hlen : i.toNat < (BlockToVals b).length := by
    rw [length_Block_to_vals]; unfold blockBytes; omega
  have hlk := List.getElem?_eq_getElem hlen
  unfold pointstoBlock
  iintro Hm
  icases BigSepL.bigSepL_lookup hlk $$ Hm with Hi
  iexists _
  rw [show ((i.toNat : Nat) : Int) = i by omega]
  iframe Hi
  ipureintro; exact hlk

/-- The bytes of a block are in the heap. -/
def BlockInHeap (h : GMap Loc (NonAtomic val)) (l : Loc) (b : Block) : Prop :=
  ∀ i : Int, 0 ≤ i → i < 4096 →
    match h !! (l +ₗ i) with
    | some (Reading _, v) => (BlockToVals b)[i.toNat]? = some v
    | _ => False

theorem heap_valid_block (l : Loc) (b : Block) (q : DFrac) (σ : GMap Loc (NonAtomic val)) :
    ⊢ naHeapCtx (hG := L.goose_na_heapGS) tls σ -∗ pointstoBlock (GF := GF) l q b -∗
      ⌜BlockInHeap σ l b⌝ := by
  iintro Hσ Hm
  unfold BlockInHeap
  iapply pure_forall.mpr
  iintro %i
  by_cases hi : 0 ≤ i ∧ i < 4096
  · icases pointstoBlock_extract i l q b hi.1 hi.2 $$ Hm with ⟨%v, Hi, %Hv⟩
    icases heapPointsto_na_acc _ _ _ $$ Hi with ⟨Hi, -⟩
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

theorem blockToVals_ext_eq (b1 b2 : Block)
    (H : ∀ i : Int, 0 ≤ i → i < 4096 →
      (BlockToVals b1)[i.toNat]? = (BlockToVals b2)[i.toNat]?) :
    b1 = b2 := by
  have Hl : BlockToVals b1 = BlockToVals b2 := by
    apply List.ext_getElem?
    intro n
    by_cases hn : n < 4096
    · have := H n (by omega) (by omega)
      simpa using this
    · rw [List.getElem?_eq_none (by rw [length_Block_to_vals]; unfold blockBytes; omega),
        List.getElem?_eq_none (by rw [length_Block_to_vals]; unfold blockBytes; omega)]
  have Hinj : Function.Injective (fun b : w8 => (#b : val)) := GoGlobalContext.intoVal_inj_w8
  have := (List.map_inj_right (fun x y h => Hinj h)).mp Hl
  exact Vector.toList_inj.mp this

theorem blockInHeap_inj {h : GMap Loc (NonAtomic val)} {l : Loc} {b1 b2 : Block}
    (H1 : BlockInHeap h l b1) (H2 : BlockInHeap h l b2) : b1 = b2 := by
  apply blockToVals_ext_eq
  intro i h0 h1
  have e1 := H1 i h0 h1
  have e2 := H2 i h0 h1
  revert e1 e2
  rcases h !! (l +ₗ i) with _ | ⟨m, v⟩
  · simp
  · cases m with
    | Writing => simp
    | Reading _ => intro e1 e2; rw [e1, e2]

theorem diskFfiStep_ReadOp_inv {v : val} {σg σg' : CfgState} {e' : Expr}
    (h : DiskFfiStep .ReadOp v σg e' σg') :
    ∃ (a : w64) (b : Block) (l : Loc), v = #a ∧ diskWorld σg.1 !! uint.Z a = some b ∧
      IsFresh σg l ∧ e' = Val (#l) ∧
      σg' = (stateInsertList l (BlockToVals b) σg.1, σg.2) := by
  cases h with
  | ReadS a b l _ h1 h2 => exact ⟨a, b, l, rfl, h1, h2, rfl, rfl⟩

theorem diskFfiStep_WriteOp_inv {v : val} {σg σg' : CfgState} {e' : Expr}
    (h : DiskFfiStep .WriteOp v σg e' σg') :
    ∃ (a : w64) (l : Loc) (b0 b : Block), v = PairV (#a) (#l) ∧
      diskWorld σg.1 !! uint.Z a = some b0 ∧ BlockInHeap σg.1.heap l b ∧ e' = Val (#()) ∧
      σg' = ({ σg.1 with world := <[uint.Z a := b]> (diskWorld σg.1) }, σg.2) := by
  cases h with
  | WriteS a l b0 b _ h1 h2 => exact ⟨a, l, b0, b, rfl, h1, h2, rfl, rfl⟩

open EctxLanguage

theorem wp_ReadOp (a : w64) (q : DFrac) (b : Block) :
    {{ ▷ diskPointsto (gooseDiskGS (L := L)) (uint.Z a) q b }} (ExternalOp DiskOp.ReadOp (Val (#a))) @ s; E
    {{ (l : Loc), RET #l; uint.Z a d↦{q} b ∗ pointstoBlock l (.own 1) b }} := by
  iintro %Φ >Ha HΦ
  iapply goose_wp_lift_atomic_base_step_no_fork rfl rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  icases (disk_local_ctx_eq _).mp $$ Hffi with Hffi
  unfold diskPointsto
  icases genHeap_lookup (G := (gooseDiskGS (L := L)).diskGGenHeapG) $$ Hffi Ha with %Hd
  have Hd' : diskWorld σ₁.1 !! uint.Z a = some b := Hd
  imodintro
  isplitr
  · ipureintro
    obtain ⟨l, hl⟩ := exists_isFresh σ₁
    exact ⟨[], _, _, [], BaseStep.ExternalOpS _ _ _ σ₁ _ (DiskFfiStep.ReadS a b l σ₁ Hd' hl)⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  have Hbs : BaseStep _ _ _ _ _ _ := Hstep
  cases Hbs with
  | ExternalOpS _ _ _ _ _ Hffi_step =>
  obtain ⟨a', b', l, Ha', Hd'', Hfresh, rfl, rfl⟩ := diskFfiStep_ReadOp_inv Hffi_step
  cases GoGlobalContext.intoVal_inj_w64 Ha'
  rw [Hd'] at Hd''
  cases Hd''
  imod na_heap_alloc_list _ l (BlockToVals b) (fun i => (Hfresh.1 i).2) $$ Hheap
    with ⟨Hheap, Hpts⟩
  imodintro
  isplitr
  · ipureintro; rfl
  isplitl [Hheap Hffi Hgs Hgffi Hproph]
  · iapply (goose_stateInterp_eq _ _ _ _).mpr
    simp only [List.nil_append]
    dsimp only [stateInsertList]
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
  unfold pointstoBlock
  iapply BigSepL.bigSepL_mono ?_ $$ Hpts
  intro k x _
  exact na_pointsto_to_heap _ _ _ Hfresh.car

theorem wp_WriteOp (a : w64) (b : Block) (q : DFrac) (l : Loc) :
    {{ ▷ ((∃ b0, diskPointsto (gooseDiskGS (L := L)) (uint.Z a) (.own 1) b0) ∗
        pointstoBlock l q b) }}
      (ExternalOp DiskOp.WriteOp (Val (PairV (#a) (#l)))) @ s; E
    {{ RET #(); uint.Z a d↦ b ∗ pointstoBlock l q b }} := by
  iintro %Φ >⟨⟨%b0, Ha⟩, Hl⟩ HΦ
  iapply goose_wp_lift_atomic_base_step_no_fork rfl rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  icases (disk_local_ctx_eq _).mp $$ Hffi with Hffi
  unfold diskPointsto
  icases genHeap_lookup (G := (gooseDiskGS (L := L)).diskGGenHeapG) $$ Hffi Ha with %Hd
  have Hd' : diskWorld σ₁.1 !! uint.Z a = some b0 := Hd
  icases heap_valid_block l b q σ₁.1.heap $$ Hheap Hl with %Hvalid
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.ExternalOpS _ _ _ σ₁ _
      (DiskFfiStep.WriteS a l b0 b σ₁ Hd' Hvalid)⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  have Hbs : BaseStep _ _ _ _ _ _ := Hstep
  cases Hbs with
  | ExternalOpS _ _ _ _ _ Hffi_step =>
  obtain ⟨a', l', b0', b', Hv, -, Hvalid', rfl, rfl⟩ := diskFfiStep_WriteOp_inv Hffi_step
  simp only [val.PairV.injEq] at Hv
  obtain ⟨Ha', Hl'⟩ := Hv
  cases GoGlobalContext.intoVal_inj_w64 Ha'
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases blockInHeap_inj Hvalid Hvalid'
  imod genHeap_update' (G := (gooseDiskGS (L := L)).diskGGenHeapG) (v₂ := b)
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

def diskArray (l : Int) (q : DFrac) (vs : List Block) : IProp GF :=
  iprop([∗list] i ↦ b ∈ vs, (l + (i : Int)) d↦{q} b)

theorem diskArray_cons (l : Int) (q : DFrac) (b : Block) (vs : List Block) :
    diskArray (GF := GF) l q (b :: vs) ⊣⊢ (l d↦{q} b) ∗ diskArray (l + 1) q vs := by
  unfold diskArray
  refine BigSepL.bigSepL_cons.trans ?_
  have Hk : ∀ k : Nat, l + ((k + 1 : Nat) : Int) = l + 1 + (k : Int) := by intro k; omega
  simp only [Int.natCast_zero, Int.add_zero, Hk]
  exact .rfl

theorem diskArray_app (l : Int) (q : DFrac) (vs1 vs2 : List Block) :
    diskArray (GF := GF) l q (vs1 ++ vs2) ⊣⊢
      diskArray l q vs1 ∗ diskArray (l + vs1.length) q vs2 := by
  unfold diskArray
  refine BigSepL.bigSepL_append.trans ?_
  have Hk : ∀ k : Nat, l + ((k + vs1.length : Nat) : Int) = l + vs1.length + (k : Int) := by
    intro k; omega
  simp only [Hk]
  exact .rfl

theorem diskArray_emp (l : Int) (q : DFrac) : diskArray (GF := GF) l q [] ⊣⊢ emp := .rfl

theorem diskArray_split (l : Int) (q : DFrac) (z : Int) (vs : List Block)
    (H : 0 ≤ z ∧ z < vs.length) :
    diskArray (GF := GF) l q vs ⊣⊢
      diskArray l q (vs.take z.toNat) ∗ diskArray (l + z) q (vs.drop z.toNat) := by
  conv => lhs; rw [← List.take_append_drop z.toNat vs]
  refine (diskArray_app l q _ _).trans ?_
  rw [List.length_take, show ((min z.toNat vs.length : Nat) : Int) = z by omega]
  exact .rfl

theorem diskArray_acc (l : Int) (bs : List Block) (z : Int) (b : Block) (q : DFrac)
    (Hpos : 0 ≤ z) (Hlookup : bs[z.toNat]? = some b) :
    ⊢ diskArray (GF := GF) l q bs -∗
      ((l + z) d↦{q} b ∗ ∀ b', (l + z) d↦{q} b' -∗ diskArray l q (bs.set z.toNat b')) := by
  unfold diskArray
  iintro Hl
  icases BigSepL.bigSepL_insert_acc Hlookup $$ Hl with ⟨Hb, Hrest⟩
  rw [show ((z.toNat : Nat) : Int) = z by omega]
  iframe Hb
  iexact Hrest

theorem diskArray_acc_read (l : Int) (bs : List Block) (z : Int) (b : Block) (q : DFrac)
    (Hpos : 0 ≤ z) (Hlookup : bs[z.toNat]? = some b) :
    ⊢ diskArray (GF := GF) l q bs -∗
      ((l + z) d↦{q} b ∗ ((l + z) d↦{q} b -∗ diskArray l q bs)) := by
  iintro Hl
  icases diskArray_acc l bs z b q Hpos Hlookup $$ Hl with ⟨Hb, Hrest⟩
  iframe Hb
  iintro Hb
  have Hset : bs.set z.toNat b = bs := by
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp Hlookup
    exact List.set_getElem_self hlt
  ihave H := Hrest $$ %b Hb
  rw [Hset]
  iexact H

theorem initDisk_sz_lookup_ge (sz : Nat) (z : Int) (Hle : (sz : Int) ≤ z) :
    initDisk ∅ sz !! z = none := by
  induction sz with
  | zero => rfl
  | succ n ih =>
    show (<[(n : Int) := block0]> (initDisk ∅ n)) !! z = none
    rw [GMap.lookup_insert_ne _ _ (by omega)]
    exact ih (by omega)

theorem diskArray_init_disk (sz : Nat) :
    ([∗map] i ↦ b ∈ initDisk ∅ sz, (i d↦ b : IProp GF)) ⊢
      diskArray 0 (.own 1) (List.replicate sz block0) := by
  induction sz with
  | zero =>
    iintro _
    unfold diskArray
    rw [List.replicate_zero]
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | succ n ih =>
    have Hnone : PartialMap.get? (initDisk ∅ n) (n : Int) = none :=
      initDisk_sz_lookup_ge n n (Int.le_refl _)
    refine (BigSepM.bigSepM_insert (Φ := fun i b => (i d↦ b : IProp GF)) Hnone).1.trans ?_
    rw [List.replicate_succ']
    refine (sep_mono_right ih).trans ?_
    refine Entails.trans ?_ (diskArray_app 0 _ _ _).2
    refine sep_comm.1.trans (sep_mono_right ?_)
    rw [List.length_replicate]
    unfold diskArray
    refine Entails.trans ?_ BigSepL.bigSepL_singleton.2
    simp only [Int.natCast_zero, Int.add_zero, Int.zero_add]
    exact .rfl

end disk

end Perennial
