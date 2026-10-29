/-
The proof of `testStatsConcurrent`: two goroutines each add 3 to a `TxStats`'s `WriteTime`
(an atomic add through an `*int64` view of the `*time.Duration`) and 1 to its `PageCount`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testStatsConcurrent
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Spec.sync.WaitGroup__Wait
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.TokSet

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Assumptions]

local notation "TxStats" => github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.TxStats

/-- The ghost names: for each counter, the permits to add to it (two, one per goroutine, the
main thread holding their authority) and the receipts of the adds (the invariant holding their
authority). -/
structure StatsNames where
  permWT : GName
  rcptWT : GName
  permPC : GName
  rcptPC : GName

/-- The counters of `s`: each is the number of adds so far (times 3 for `WriteTime`), each add
having spent a permit and handed out a receipt. -/
abbrev statsInv (s : Loc) (γ : StatsNames) : IProp GF :=
  iprop(∃ a b : Nat,
    structFieldRef TxStats go!"WriteTime" s ↦ (W64 (3 * a : Nat) : w64) ∗
      ownToks γ.permWT a ∗ ownTokAuth γ.rcptWT a ∗
    structFieldRef TxStats go!"PageCount" s ↦ (W64 (b : Nat) : w64) ∗
      ownToks γ.permPC b ∗ ownTokAuth γ.rcptPC b)

abbrev statsN : Namespace := nroot.@"stats"

set_option goose.wp.extras true in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testStatsConcurrent.wp_proof
    (wp_WaitGroup_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wp_WaitGroup_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (wp_WaitGroup_Wait : sync.WaitGroup.Wait.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testStatsConcurrent.spec
      (GF := GF) (hG := hG) := by
  intro Φ
  iintro #Hpkg HΦ
  wp_func_call
  wp_call
  wp_auto
  icases typedPointsto_split _ _ _ $$ «$r0» with H
  simp only [TypedPointsto.typedPointstoDef]
  icases H with ⟨PageCount, WriteTime, -⟩
  ipersist s
  imod ownTokAuth_alloc (GF := GF) with ⟨%γpw, Hpw⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γrw, Hrw⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γpp, Hpp⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γrp, Hrp⟩
  imod ownTokAuth_add 2 γpw 0 $$ Hpw with ⟨Hpw, Hpw2⟩
  imod ownTokAuth_add 2 γpp 0 $$ Hpp with ⟨Hpp, Hpp2⟩
  imod ownToks_0 (GF := GF) γpw with Hpw0
  imod ownToks_0 (GF := GF) γpp with Hpp0
  let γ : StatsNames := ⟨γpw, γrw, γpp, γrp⟩
  imod inv_alloc statsN ⊤ (statsInv «$r0_ptr» γ) $$ [PageCount WriteTime Hpw0 Hpp0 Hrw Hrp] with #Hinv
  · inext
    unfold statsInv
    iexists 0, 0
    rw [show (zero_val TxStats).PageCount' = W64 ((0 : Nat) : Int) from rfl,
      show (zero_val TxStats).WriteTime' = W64 ((3 * 0 : Nat) : Int) from rfl]
    unfold named
    iframe
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, H⟩
  imod sync.join.init wg_ptr γwg $$ H with Hwg
  imod ownToks_0 (GF := GF) γrw with Hrw0
  imod ownToks_0 (GF := GF) γrp with Hrp0
  ihave HH : (∃ n : Nat, "i" ∷ i_ptr ↦ (W64 (n : Nat) : w64) ∗ "%Hn" ∷ ⌜n ≤ 2⌝ ∗
      "Hpw2" ∷ ownToks γpw (2 - n) ∗ "Hpp2" ∷ ownToks γpp (2 - n) ∗
      "Hwg" ∷ sync.join.ownAdder wg_ptr (W32 (n : Nat)) iprop(ownToks γrw n ∗ ownToks γrp n) :
      IProp GF) $$ [i Hpw2 Hpp2 Hwg Hrw0 Hrp0]
  · iexists 0
    iframe i Hpw2 Hpp2
    isplitr
    · ipureintro; omega
    iapply sync.join.ownAdder_wand $$ [Hrw0 Hrp0] Hwg
    iintro -
    iframe
  wp_for HH
  have hz : sint.Z (W64 (n : Int)) = (n : Int) := by
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> rfl
  rw [hz, show sint.Z (W64 2) = 2 from rfl]
  wp_if_destruct
  · -- an iteration: `wg.Add(1); go ...`
    wp_apply sync.join.WaitGroup.wp_Add_of wp_WaitGroup_Add
        iprop(ownToks γrw 1 ∗ ownToks γrp 1) wg_ptr _ (W32 (n : Nat)) $$ [Hwg] as ⟨Hwg, Hdone⟩
    · iframe Hwg
      ipureintro
      have : sint.Z (W32 (n : Int)) = (n : Int) := by
        rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> rfl
      omega
    rw [show 2 - n = (1 - n) + 1 by omega]
    icases ownToks_add_1 1 (1 - n) γpw $$ Hpw2 with ⟨Hpw2, Hpw1⟩
    icases ownToks_add_1 1 (1 - n) γpp $$ Hpp2 with ⟨Hpp2, Hpp1⟩
    wp_apply wp_fork $$ [Hdone Hpw1 Hpp1]
    · unsafememory_steps
      -- `atomic.AddInt64` on `WriteTime`, through its `*int64` view
      wp_bind (AddBytes _ _ _)
      iinv Hinv with ⟨%a, %b, >HWT, >Hpa, >Hra, >HPC, >Hpb, >Hrb⟩
      wp_apply_core wp_add_bytes_typed _ _ _ _ (W64 3) $$ HWT
      iintro HWT
      imod ownTokAuth_S _ _ $$ Hra with ⟨Hra, Hr1⟩
      imodintro
      isplitl [HWT Hpa Hpw1 Hra HPC Hpb Hrb]
      · inext
        iexists a + 1, b
        rw [show W64 ((3 * a : Nat) : Int) + W64 3 = W64 ((3 * (a + 1) : Nat) : Int) by word]
        iframe HWT Hra HPC Hpb Hrb
        iapply ownToks_add_2 $$ [Hpa Hpw1]
        iframe
      unsafememory_steps
      -- `atomic.AddInt64` on `PageCount`
      wp_bind (AddBytes _ _ _)
      iinv Hinv with ⟨%a, %b, >HWT, >Hpa, >Hra, >HPC, >Hpb, >Hrb⟩
      wp_apply_core wp_add_bytes_typed _ _ _ _ (W64 1) $$ HPC
      iintro HPC
      imod ownTokAuth_S _ _ $$ Hrb with ⟨Hrb, Hr1'⟩
      imodintro
      isplitl [HWT Hpa Hra HPC Hpb Hpp1 Hrb]
      · inext
        iexists a, b + 1
        rw [show W64 ((b : Nat) : Int) + W64 1 = W64 ((b + 1 : Nat) : Int) by word]
        iframe HWT Hpa Hra HPC Hrb
        iapply ownToks_add_2 $$ [Hpb Hpp1]
        iframe
      wp_auto
      wp_apply sync.join.WaitGroup.wp_Done_of wp_WaitGroup_Done
        iprop(ownToks γrw 1 ∗ ownToks γrp 1) wg_ptr $$ [Hdone Hr1 Hr1']
      · iframe
      itrivial
    wp_for_post
    iframe HΦ «$res0» Hpw Hpp
    iexists n + 1
    rw [show W64 (n : Int) + W64 1 = W64 ((n + 1 : Nat) : Int) by word,
      show 1 - n = 2 - (n + 1) by omega,
      show W32 (n : Int) + W32 1 = W32 ((n + 1 : Nat) : Int) by word]
    iframe i Hpw2 Hpp2
    isplitr
    · ipureintro; omega
    iapply sync.join.ownAdder_wand $$ [] Hwg
    iintro ⟨⟨H1, H2⟩, H3, H4⟩
    isplitl [H1 H3]
    · iapply ownToks_add_2 $$ [H1 H3]
      iframe
    · iapply ownToks_add_2 $$ [H2 H4]
      iframe
  · -- `wg.Wait()`: both goroutines' receipts
    have hn : n = 2 := by omega
    subst hn
    wp_apply sync.join.WaitGroup.wp_Wait_of wp_WaitGroup_Wait
      iprop(ownToks γrw 2 ∗ ownToks γrp 2) (W32 ((2 : Nat) : Int)) wg_ptr
      $$ [Hwg] as ⟨>Hres, -⟩
    · iexact Hwg
    icases Hres with ⟨Hw2, Hp2⟩
    unsafememory_steps
    -- `s.GetWriteTime()`: `WriteTime` is `3 * 2`
    wp_bind (LoadBytes _ _)
    iinv Hinv with ⟨%a, %b, >HWT, >Hpa, >Hra, >HPC, >Hpb, >Hrb⟩
    icombine Hpw Hpa gives %h1
    icombine Hra Hw2 gives %h2
    have ha : a = 2 := by omega
    subst ha
    wp_apply_core wp_load_bytes_typed _ _ _ _ _ $$ HWT
    iintro HWT
    imodintro
    isplitl [HWT Hpa Hra HPC Hpb Hrb]
    · inext
      iexists 2, b
      iframe
    unsafememory_steps
    -- `atomic.LoadInt64(&s.PageCount)`: `PageCount` is `2`
    wp_bind (LoadBytes _ _)
    iinv Hinv with ⟨%a, %b, >HWT, >Hpa, >Hra, >HPC, >Hpb, >Hrb⟩
    icombine Hpp Hpb gives %h1
    icombine Hrb Hp2 gives %h2
    have hb : b = 2 := by omega
    subst hb
    wp_apply_core wp_load_bytes_typed _ _ _ _ _ $$ HPC
    iintro HPC
    imodintro
    isplitl [HWT Hpa Hra HPC Hpb Hrb]
    · inext
      iexists a, 2
      iframe
    unsafememory_steps
    iexact HΦ

end proof

end Perennial
