/-
`assume` and overflow-assumption helpers used by generated code.
-/
import Perennial.Golang.Defn.Exception

namespace Perennial

section defn
variable [FfiSyntax] [GoGlobalContext]

/-- `assume e` goes into an infinite loop if e does not hold -/
def assume : val :=
  λ: "cond", if: "cond" then #() else
               (rec: "infloop" <> := "infloop" #()) #()

/-- Assume "a" + "b" doesn't overflow. -/
def assumeSumNoOverflow : val :=
  λ: "a" "b", assume ("a" ≤⟨go.uint64⟩ #(W64 (2^64-1)) -⟨go.uint64⟩ "b") ;; #()

/-- Assume "a" + "b" doesn't overflow and return the sum. -/
def sumAssumeNoOverflow : val :=
  λ: "a" "b", assumeSumNoOverflow "a" "b" ;;
              "a" +⟨go.uint64⟩ "b"

/-- Assume "x" + "y" doesn't overflow. -/
def assumeSumNoOverflowSigned : val :=
  λ: "x" "y",
  let: "max_int" := #(W64 (2^63-1)) in
  let: "min_int" := #(W64 (-2^63)) in
  assume (((#(W64 0) <⟨go.int⟩ "y") && ("x" <⟨go.int⟩ ("max_int" -⟨go.int⟩ "y"))) ||
    (("y" <⟨go.int⟩ #(W64 0)) && (("min_int" -⟨go.int⟩ "y") <⟨go.int⟩ "x")))

/-- Assume "x" + "y" doesn't overflow and return the sum. -/
def sumAssumeNoOverflowSigned : val :=
  λ: "a" "b", assumeSumNoOverflowSigned "a" "b" ;;
              "a" +⟨go.uint64⟩ "b"

def mulOverflows : val :=
  λ: "a" "b", if: ("a" =⟨go.uint64⟩ #(W64 0)) || ("b" =⟨go.uint64⟩ #(W64 0)) then #false
              else "a" >⟨go.uint64⟩ #(W64 (2^64-1)) /⟨go.uint64⟩ "b"

/-- Assume "a" * "b" doesn't overflow (as unsigned 64-bit integers) -/
def assumeMulNoOverflow : val :=
  λ: "a" "b", assume (⟨go.bool⟩! mulOverflows "a" "b")

end defn

end Perennial
