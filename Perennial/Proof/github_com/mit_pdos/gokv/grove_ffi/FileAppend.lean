/-
The proof of `github.com/mit-pdos/gokv/grove_ffi.FileAppend`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.FileAppend
public import Perennial.Proof.github_com.mit_pdos.gokv.grove_ffi.AtomicOps

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode grove_ext

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt groveExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.gokv.grove_ffi.Assumptions]

/-- The model's `pieceLen n`: `n`, or a length in `1..n`. -/
theorem github_com.mit_pdos.gokv.grove_ffi.FileAppend.wp_pieceLen (n : w64) :
    {{ (True : IProp GF) }} (App (Val github_com.mit_pdos.gokv.grove_ffi.FileAppend.pieceLen) (Val #n))
    {{ (k : w64), RET #k; ⌜k = n ∨ (0 < sint.Z k ∧ sint.Z k ≤ sint.Z n)⌝ }} := by
  iintro %Φ _ HΦ
  unfold github_com.mit_pdos.gokv.grove_ffi.FileAppend.pieceLen
  wp_pures
  wp_apply wp_ArbitraryInt as %k -
  wp_pures
  wp_if_destruct
  · wp_pures
    wp_if_destruct
    · iapply HΦ; ipureintro; right; constructor <;> word
    · iapply HΦ; ipureintro; left; rfl
  · iapply HΦ; ipureintro; left; rfl

/-- The model's `appendPieces f str`: `str` is appended to file `f`, piece by piece. -/
theorem github_com.mit_pdos.gokv.grove_ffi.FileAppend.wp_appendPieces (f : GoString)
    (Hf : ValidFileName f) :
    ⊢ ∀ (str old : List w8) (Φ : val → IProp GF), ⌜str.length < 2 ^ 63⌝ -∗
      f f↦ old -∗ (f f↦ (old ++ str) -∗ Φ #()) -∗
      WP (App (App (Val github_com.mit_pdos.gokv.grove_ffi.FileAppend.appendPieces) (Val #f))
        (Val #str)) {{ Φ }} := by
  unfold github_com.mit_pdos.gokv.grove_ffi.FileAppend.appendPieces
  iloeb as IH
  iintro %str %old %Φ %Hstr Hfile HΦ
  wp_pures
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
  wp_pures
  wp_apply github_com.mit_pdos.gokv.grove_ffi.FileAppend.wp_pieceLen with %k %Hk
  have Hn : sint.Z (W64 (str.length : Int)) = str.length := by word
  have Hk0 : 0 ≤ sint.Z k ∧ sint.Z k ≤ str.length := by
    rcases Hk with rfl | ⟨h1, h2⟩
    · omega
    · omega
  wp_pures
  rw [ite_eq_left ⟨by decide, Hk0.1, Hk0.2⟩]
  wp_bind (ExternalOp _ _ _)
  wp_apply wp_FileAppendOp f old _ Hf $$ Hfile with Hfile
  wp_pures
  have Hnn : sint.nat (W64 (str.length : Int)) = str.length := by word
  wp_if_destruct
  · rw [ite_eq_left ⟨Hk0.1, by omega, by omega⟩]
    have Hrest : ((List.drop (sint.nat k) str).take
        (sint.nat (W64 (str.length : Int)) - sint.nat k)).length < 2 ^ 63 := by
      simp only [List.length_take, List.length_drop]; omega
    iapply IH $$ %_ %_ %_ %Hrest Hfile
    iintro Hfile
    iapply HΦ
    simp only [Nat.sub_zero, List.drop_zero, Hnn, List.append_assoc]
    rw [List.take_of_length_le
      (show (List.drop (sint.nat k) str).length ≤ str.length - sint.nat k by simp),
      List.take_append_drop]
    iexact Hfile
  · iapply HΦ
    simp only [Nat.sub_zero, List.drop_zero]
    rw [List.take_of_length_le (show str.length ≤ sint.nat k by word)]
    iexact Hfile

theorem github_com.mit_pdos.gokv.grove_ffi.FileAppend.wp_proof :
    github_com.mit_pdos.gokv.grove_ffi.FileAppend.spec (GF := GF) (hG := hG) :=
    fun f s dq data old Hf => by
  iintro %Φ ⟨Hs, Hfile⟩ HΦ
  wp_func_call
  unfold FileAppend.impl
  wp_pures
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_apply wp_bytes_to_string s data dq $$ Hs with Hs
  try wp_pures
  have Hdl : data.length < 2 ^ 63 := by word
  iapply github_com.mit_pdos.gokv.grove_ffi.FileAppend.wp_appendPieces f Hf $$ %data %old %Φ
    %Hdl Hfile
  iintro Hfile
  iapply HΦ
  iframe

end proof

end Perennial
