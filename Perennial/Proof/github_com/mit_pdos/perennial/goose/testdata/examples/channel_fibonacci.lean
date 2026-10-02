/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel_fibonacci.v`:
a producer sends the Fibonacci numbers over a single-producer single-consumer
channel (`go.dev/tour/concurrency/4`).
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel_examples_init
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Spsc

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

/-- The Fibonacci numbers (wrapping on overflow). -/
def fib : Nat → w64
  | 0 => W64 0
  | 1 => W64 1
  | n + 2 => fib (n + 1) + fib n

def fib_list (n : Nat) : List w64 := (List.range n).map fib

theorem fib_list_succ (n : Nat) : fib_list (n + 1) = fib_list n ++ [fib n] := by
  simp [fib_list, List.range_succ]

theorem fib_list_length (n : Nat) : (fib_list n).length = n := by
  simp [fib_list]

theorem fib_succ (k : Nat) :
    fib (k + 1) = match k with | 0 => W64 1 | k' + 1 => fib (k' + 1) + fib k' := by
  cases k <;> rfl

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

set_option maxHeartbeats 400000 in
theorem wp_fibonacci (n : w64) (c_ptr : loc) (γ : spsc_names) (Hn : 0 < sint.Z n) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗
        is_spsc γ c_ptr (fun i v => iprop(⌜v = fib i.toNat⌝))
          (fun sent => iprop(⌜sent = fib_list (sint.nat n)⌝)) ∗
        spsc_producer γ ([] : List w64) }}
      (App (App (Val (@! fibonacci)) (Val #n)) (Val #c_ptr))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hspsc, Hprod⟩
  wp_auto
  sorry

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
