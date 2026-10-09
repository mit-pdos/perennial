/-
Time receipts: laws and an example (Lean addition, regression test).

The example is the paper's "clock" (Mével, Jourdan, Pottier, ESOP 2019, §2): a
64-bit counter that is incremented with `atomic.AddUint64` and whose value is
matched by as many exclusive time receipts. Since `receiptBound GF = N`
receipts are contradictory, the counter stays below `N`; under the premise
`N ≤ 2^64` on the (otherwise unspecified) bound, the 64-bit addition never
wraps around, without any precondition on the callers. A client discharges the
premise when it instantiates `N` in `goose_adequacy`.
-/
module

public import Perennial.Proof.sync.atomic
public import Perennial.GooseLang.Adequacy

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace TimeReceiptsTest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The laws (paper, Fig. 3) -/

section laws
variable {GF : BundledGFunctors} [ReceiptGS GF]

example (m n : Nat) : ⧗ (m + n) ⊣⊢@{IProp GF} ⧗ m ∗ ⧗ n := receipt_add m n
example : ⊢@{IProp GF} |==> ⧗ 0 := receipt_zero
example (n : Nat) : Persistent (⧖ n : IProp GF) := inferInstance
example (m n : Nat) : ⧖ (max m n) ⊣⊢@{IProp GF} ⧖ m ∗ ⧖ n := preceipt_max m n
example (m n : Nat) (h : m ≤ n) : ⧖ n ⊢@{IProp GF} ⧖ m := preceipt_mono h
example (n : Nat) : ⧗ n ⊢@{IProp GF} |==> (⧗ n ∗ ⧖ n) := receipt_snapshot n
example : ⧗ (receiptBound GF) ⊢@{IProp GF} False := receiptBound_elim
example : ⧖ (receiptBound GF) ⊢@{IProp GF} False := preceipt_bound_elim
example (n : Nat) : ⧗ n ⊢@{IProp GF} ⌜n < receiptBound GF⌝ := receipt_lt n
example : 0 < receiptBound GF := receiptBound_pos

end laws

/-! ## A clock that cannot overflow -/

section clock
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : sync.atomic.Assumptions]

/-- The clock invariant: the counter `l` holds `n`, and `n` receipts back it. -/
def clockN : Namespace := nroot.@"clock"

def clockInv (l : Loc) : IProp GF :=
  iprop(∃ n : Nat, l ↦ (W64 n : w64) ∗ ⧗ n)

theorem clock_alloc (l : Loc) :
    l ↦ (W64 0 : w64) ⊢@{IProp GF} |={⊤}=> inv clockN (clockInv l) := by
  iintro Hl
  imod receipt_zero (GF := GF) with H0
  iapply inv_alloc clockN ⊤ (clockInv l)
  inext
  unfold clockInv
  iexists 0
  iframe

/-- Incrementing the clock (`atomic.AddUint64(l, 1)`, as emitted by goose)
returns `n + 1` for some `n + 1 < 2^64`: the counter never wraps around,
provided the time-receipt bound is at most `2^64`. -/
theorem wp_clock_incr (Hbound : receiptBound GF ≤ 2 ^ 64) (l : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ inv clockN (clockInv l) }}
      (App (App (App (Val (GoInstruction (FuncResolve sync.atomic.AddUint64 []))) (Val #()))
        (Val #l)) (Val #(W64 1)))
    {{ (n : Nat), RET #(W64 (n + 1)); ⌜n + 1 < 2 ^ 64⌝ }} := by
  iintro %Φ ⟨#Hpkg, #Hinv⟩ HΦ
  iapply sync.atomic.wp_AddUint64_receipt l (W64 1) $$ %_ Hpkg
  iintro Hr
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold clockInv
  icases Hi with ⟨%n, Hl, Hn⟩
  -- the fresh receipt and the `n` receipts of the invariant bound `n + 1`
  icases receipt_add_one_lt n $$ [Hr Hn] with ⟨%Hlt, Hn⟩
  · iframe
  iexists (W64 n)
  iframe Hl
  iintro Hl
  imod Hmask with -
  imod Hclose $$ [Hl Hn] with -
  · inext
    iexists n + 1
    rw [show W64 n + W64 1 = W64 ((n + 1 : Nat) : Int) by word]
    iframe
  imodintro
  rw [show W64 n + W64 1 = W64 ((n : Int) + 1) by word]
  iapply HΦ $$ %n
  ipureintro; omega

end clock

/-! ## Picking the bound at adequacy time

A client whose WP proof assumes `receiptBound GF ≤ 2 ^ 64` (e.g. through
`wp_clock_incr`) instantiates `goose_adequacy` with `N = 2 ^ 64` and gets
safety for executions of fewer than `2 ^ 64` steps. -/

section adequacy
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiInterpAdequacy ffi]
variable [FfiSemantics ext ffi] [GoGlobalContext] {GF : BundledGFunctors}

example [GooseGpreS ffi GF] (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (Hinitg : ffi_initgP g.globalWorld) (Hinit : ffi_initP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF ≤ 2 ^ 64 →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld -∗
        ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        ownGoState σ.goState.packageState ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2)) (Hn : n < 2 ^ 64) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) :=
  goose_adequacy (2 ^ 64) e σ g φ Hinitg Hinit
    (@fun hG HN Hlctx => Hwp (hG := hG) (Nat.le_of_eq HN) Hlctx) n κs t2 σ2 Hsteps Hn

end adequacy

end TimeReceiptsTest

end Perennial
