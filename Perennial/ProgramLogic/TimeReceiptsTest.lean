/-
Time receipts: laws and an example (Lean addition, regression test).

The example is the paper's "clock" (Mével, Jourdan, Pottier, ESOP 2019, §2): a
64-bit counter that is incremented with `atomic.AddUint64` and whose value is
matched by as many exclusive time receipts. Since `receipt_bound = 2^48`
receipts are contradictory, the counter stays below `2^48` and the 64-bit
addition never wraps around, without any precondition on the callers.
-/
import Perennial.Proof.sync.atomic

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace TimeReceiptsTest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The laws (paper, Fig. 3) -/

section laws
variable {GF : BundledGFunctors} [receiptGS GF]

example (m n : Nat) : ⧗ (m + n) ⊣⊢@{IProp GF} ⧗ m ∗ ⧗ n := receipt_add m n
example : ⊢@{IProp GF} |==> ⧗ 0 := receipt_zero
example (n : Nat) : Persistent (⧖ n : IProp GF) := inferInstance
example (m n : Nat) : ⧖ (max m n) ⊣⊢@{IProp GF} ⧖ m ∗ ⧖ n := preceipt_max m n
example (m n : Nat) (h : m ≤ n) : ⧖ n ⊢@{IProp GF} ⧖ m := preceipt_mono h
example (n : Nat) : ⧗ n ⊢@{IProp GF} |==> (⧗ n ∗ ⧖ n) := receipt_snapshot n
example : ⧗ receipt_bound ⊢@{IProp GF} False := receipt_bound_elim
example : ⧖ receipt_bound ⊢@{IProp GF} False := preceipt_bound_elim
example : receipt_bound = 2 ^ 48 := receipt_bound_eq

end laws

/-! ## A clock that cannot overflow -/

section clock
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics] [package_sem : sync.atomic.Assumptions]

/-- The clock invariant: the counter `l` holds `n`, and `n` receipts back it. -/
def clockN : Namespace := nroot.@"clock"

def clock_inv (l : loc) : IProp GF :=
  iprop(∃ n : Nat, l ↦ (W64 n : w64) ∗ ⧗ n)

theorem clock_alloc (l : loc) :
    l ↦ (W64 0 : w64) ⊢@{IProp GF} |={⊤}=> inv clockN (clock_inv l) := by
  iintro Hl
  imod receipt_zero (GF := GF) with H0
  iapply inv_alloc clockN ⊤ (clock_inv l)
  inext
  unfold clock_inv
  iexists 0
  iframe

/-- Incrementing the clock (`atomic.AddUint64(l, 1)`, as emitted by goose)
returns `n + 1` for some `n + 1 < 2^48`: the counter never wraps around. -/
theorem wp_clock_incr (l : loc) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic ∗ inv clockN (clock_inv l) }}
      (App (App (App (Val (GoInstruction (FuncResolve sync.atomic.AddUint64 []))) (Val #()))
        (Val #l)) (Val #(W64 1)))
    {{ (n : Nat), RET #(W64 (n + 1)); ⌜n + 1 < 2 ^ 48⌝ }} := by
  iintro %Φ ⟨#Hpkg, #Hinv⟩ HΦ
  iapply sync.atomic.wp_AddUint64_receipt l (W64 1) $$ %_ Hpkg
  iintro Hr
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold clock_inv
  icases Hi with ⟨%n, Hl, Hn⟩
  -- the fresh receipt and the `n` receipts of the invariant bound `n + 1`
  icases receipt_add_one_lt n $$ [Hr Hn] with ⟨%Hlt, Hn⟩
  · iframe
  rw [receipt_bound_eq] at Hlt
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
  ipureintro; exact Hlt

end clock

end TimeReceiptsTest

end Perennial
