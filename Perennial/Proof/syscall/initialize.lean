/-
The proof of `syscall.initialize'`: it initializes `sync`, allocates the variables, and runs the
trusted models of `runtime_envs` (an arbitrary `[]string`) and of `init.0` (a no-op).
-/
module

public import Perennial.Spec.syscall.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.sync.OnceFunc
public import Perennial.Proof.fmt.SprintfModel

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : syscall.Assumptions]

omit package_sem in
/-- The model `syscall.arbitraryStrings` returns some slice of strings (owned, with its
capacity). -/
theorem syscall.wp_arbitraryStrings :
    {{ (True : IProp GF) }}
      (App (Val syscall.arbitraryStrings) (Val #()))
    {{ (s : GoSlice), RET #s; ∃ xs : List GoString,
        s ↦* xs ∗ ownSliceCap GoString s (DFrac.own 1) }} := by
  iintro %Φ - HΦ
  unfold syscall.arbitraryStrings
  wp_auto
  -- `if arbitrary() != 0 { a = []string{} }`: then the loop, from either slice
  wp_apply wp_ArbitraryInt as %c0 -
  wp_if_destruct
  · ihave HI : (∃ (sl : GoSlice) (xs : List GoString),
        "a" ∷ a_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* xs ∗
        "Hcap" ∷ ownSliceCap GoString sl (DFrac.own 1) : IProp GF) $$ [a]
    · iexists slice.nil, []
      iframe
      isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil

    wp_for HI
    wp_apply wp_ArbitraryInt as %c -
    wp_if_destruct
    · wp_apply fmt.wp_arbitraryString as %str -
      wp_apply wp_slice_literal (V := GoString) [str]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [Hsl Hcap Hsl2] with %sl' ⟨Hsl, Hcap, -⟩
      · iframe
      wp_for_post
      iframe
      iexists _, _
      iframe
    · have Hf : (!decide (c = W64 0)) = false := by
        revert Hif; cases (!decide (c = W64 0)) <;> simp
      rw [Hf]
      simp only [_root_.decide_true, ↓reduceIte]
      wp_auto
      iapply HΦ
      iexists _
      iframe
  · wp_apply wp_slice_literal (V := GoString) []
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl0, Hcap0⟩
    wp_auto
    ihave HI : (∃ (sl : GoSlice) (xs : List GoString),
        "a" ∷ a_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* xs ∗
        "Hcap" ∷ ownSliceCap GoString sl (DFrac.own 1) : IProp GF) $$ [a Hsl0 Hcap0]
    · iexists _, []
      iframe

    wp_for HI
    wp_apply wp_ArbitraryInt as %c -
    wp_if_destruct
    · wp_apply fmt.wp_arbitraryString as %str -
      wp_apply wp_slice_literal (V := GoString) [str]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [Hsl Hcap Hsl2] with %sl' ⟨Hsl, Hcap, -⟩
      · iframe
      wp_for_post
      iframe
      iexists _, _
      iframe
    · have Hf : (!decide (c = W64 0)) = false := by
        revert Hif; cases (!decide (c = W64 0)) <;> simp
      rw [Hf]
      simp only [_root_.decide_true, ↓reduceIte]
      wp_auto
      iapply HΦ
      iexists _
      iframe

open syscall in
-- over the default budget since fix-semantics Cases 35–38 (regenerated `sync`, a longer
-- `arbitraryStrings`): 400000 suffices, 200000 does not
set_option maxHeartbeats 400000 in
theorem syscall.initialize'.wp_proof
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_OnceFunc : sync.OnceFunc.spec (GF := GF) (hG := hG)) :
    syscall.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc as H1
  wp_apply wp_GlobalAlloc as H2
  wp_apply wp_GlobalAlloc as H3
  wp_apply wp_GlobalAlloc as H4
  wp_apply wp_GlobalAlloc as H5
  wp_apply wp_GlobalAlloc as H6
  wp_apply wp_GlobalAlloc as H7
  wp_apply wp_GlobalAlloc as H8
  wp_apply wp_GlobalAlloc as H9
  wp_apply wp_GlobalAlloc as H10
  wp_apply wp_GlobalAlloc as H11
  wp_apply wp_GlobalAlloc as H12
  wp_apply wp_GlobalAlloc as H13
  wp_apply wp_GlobalAlloc as H14
  wp_apply wp_GlobalAlloc as H15
  wp_apply wp_GlobalAlloc as H16
  wp_apply wp_GlobalAlloc as H17
  wp_apply wp_sync_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_func_call
  unfold runtime_envs.impl
  wp_apply syscall.wp_arbitraryStrings as %envsl ⟨%xs, Henvs, Henvscap⟩
  set_option maxRecDepth 20000 in
  wp_apply wp_OnceFunc as %cpe -
  unfold EAGAIN EINVAL ENOENT
  repeat (first
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  wp_apply wp_map_make1 (K := Loc) (V := GoSlice) as %mref Hm
  -- `init.0`: the trusted no-op model
  wp_func_call
  wp_call
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
