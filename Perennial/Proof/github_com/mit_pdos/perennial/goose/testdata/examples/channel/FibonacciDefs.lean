/-
A producer sends the Fibonacci numbers over a single-producer single-consumer
channel (`go.dev/tour/concurrency/4`).

This file: the Fibonacci numbers and their lists.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Base

@[expose] public section

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

def fibList (n : Nat) : List w64 := (List.range n).map fib

theorem fibList_succ (n : Nat) : fibList (n + 1) = fibList n ++ [fib n] := by
  simp [fibList, List.range_succ]

theorem fibList_length (n : Nat) : (fibList n).length = n := by
  simp [fibList]

theorem fib_succ (k : Nat) :
    fib (k + 1) = match k with | 0 => W64 1 | k' + 1 => fib (k' + 1) + fib k' := by
  cases k <;> rfl

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
