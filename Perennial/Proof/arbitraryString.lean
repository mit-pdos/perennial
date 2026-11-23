/-
The spec of `fmt.arbitraryString` (`Perennial/TrustedCode/arbitraryString.lean`), the arbitrary
string of the models of `fmt.Sprintf` and of `syscall`'s `runtime_envs`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import Perennial.TrustedCode.arbitraryString

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace fmt

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The helper `fmt.arbitraryString` of the model of `Sprintf` returns some string. -/
theorem wp_arbitraryString :
    {{ (True : IProp GF) }}
      (App (Val arbitraryString) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  iintro %Φ - HΦ
  unfold arbitraryString
  wp_auto
  ihave IH : iprop(∃ str : GoString, "s" ∷ s_ptr ↦ str) $$ [s]
  · iexists _; iframe
  wp_for IH
  wp_apply wp_ArbitraryInt as %c -
  wp_if_destruct
  · wp_apply wp_ArbitraryInt as %b -
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z b)]
    wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.byte #(W8 (uint.Z b)))] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, -⟩
    wp_apply wp_bytes_to_string $$ Hsl as -
    wp_for_post
    iframe
    iexists _
    iframe
  · have Hf : (!decide (c = W64 0)) = false := by
      revert Hif; cases (!decide (c = W64 0)) <;> simp
    rw [Hf]
    simp only [_root_.decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial

end wps

end fmt

end Perennial
