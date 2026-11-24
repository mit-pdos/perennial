/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/grovefile.Run`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.Run
public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.FileWrite
public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.FileRead
public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.GetTSC

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode grove_ext

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt groveExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.Assumptions]

/-- The write and the read of `"f"` own its points-to, so the read returns
`"hello"`; the first reading of the TSC is at least `0` (`tscLb_0`), the second
at least the first. -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.Run.wp_proof
    (wp_FileWrite : github_com.mit_pdos.gokv.grove_ffi.FileWrite.spec (GF := GF) (hG := hG))
    (wp_FileRead : github_com.mit_pdos.gokv.grove_ffi.FileRead.spec (GF := GF) (hG := hG))
    (wp_GetTSC : github_com.mit_pdos.gokv.grove_ffi.GetTSC.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.Run.spec (GF := GF) (hG := hG) := fun old => by
  have wp_FileWrite' := fun f s dq data =>
    (FuncUnfold.func_unfold (f := github_com.mit_pdos.gokv.grove_ffi.FileWrite) (type_args := [])) ▸ wp_FileWrite f s dq data
  have wp_FileRead' := fun f =>
    (FuncUnfold.func_unfold (f := github_com.mit_pdos.gokv.grove_ffi.FileRead) (type_args := [])) ▸ wp_FileRead f
  have wp_GetTSC' : ⊢ ∀ Φ : val → IProp GF,
      (|={⊤,∅}=> ∃ prev : Nat, tscLb prev ∗
        (∀ t : w64, ⌜prev ≤ t.toNat⌝ -∗ tscLb t.toNat ={∅,⊤}=∗ Φ #t)) -∗
      WP (App (Val github_com.mit_pdos.gokv.grove_ffi.GetTSC.impl) (Val #())) {{ Φ }} :=
    (FuncUnfold.func_unfold (f := github_com.mit_pdos.gokv.grove_ffi.GetTSC) (type_args := [])) ▸ wp_GetTSC
  wp_start as Hf
  try wp_auto
  wp_apply wp_string_to_bytes go!"hello" with %sl ⟨Hsl, Hcap⟩
  -- write the file
  wp_func_call
  wp_apply_core wp_FileWrite' go!"f" sl (DFrac.own 1) go!"hello" $$ Hsl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists old
  iframe Hf
  iintro Hf
  imod Hmask
  imodintro
  iintro Hsl
  try wp_auto
  -- read it back
  wp_func_call
  wp_apply_core wp_FileRead' go!"f"
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (DFrac.own 1), go!"hello"
  iframe Hf
  iintro Hf
  imod Hmask
  imodintro
  iintro %got Hgot Hgotcap
  try wp_auto
  -- the lengths are equal
  ihave %Hgl := ownSlice_len _ _ _ $$ Hgot
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have Hlen : got.len = sl.len := by
    simp only [List.length_cons, List.length_nil] at Hgl Hsll
    word
  wp_if_destruct
  all_goals first | exact absurd Hlen Hif | skip
  try wp_auto
  -- the loop compares the bytes: `forRange`'s counter is `i_ptr`, Go's `i` is `gi_ptr`
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => gi
  ihave IH : iprop(∃ (j kv : w64),
      "i" ∷ i_ptr ↦ j ∗ "gi" ∷ gi_ptr ↦ kv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 5⌝) $$ [i gi]
  · iexists (W64 0), _
    iframe
    ipureintro
    exact ⟨by decide, by decide⟩
  wp_for IH
  wp_if_destruct
  · -- the bytes at `j` are equal
    have Hlt : (sint.Z j).toNat < (go!"hello" : GoString).length := by
      simp only [List.length_cons, List.length_nil] at Hsll ⊢
      word
    obtain ⟨x, Hx⟩ : ∃ x, (go!"hello" : GoString)[(sint.Z j).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨Hj.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z j) _ (DFrac.own 1) x Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hx
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z got.len from ⟨Hj.1, Hlen ▸ Hif⟩]
    wp_apply wp_load_slice_index got (sint.Z j) _ (DFrac.own 1) x Hj.1 $$ [Hgot] as Hgot
    · iframe; ipureintro; exact Hx
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨Hj.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z j) _ (DFrac.own 1) x Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hx
    have Hsl5 : sint.Z sl.len = 5 := by
      simp only [List.length_cons, List.length_nil] at Hsll
      word
    wp_for_post
    iframe
    iexists (j + W64 1), j
    iframe
    ipureintro
    word
  · -- the TSC does not decrease: the first reading is at least `0`
    imod tscLb_0 with #H0
    wp_func_call
    wp_apply_core wp_GetTSC'
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists 0
    iframe H0
    iintro %t1 %_ #Ht1
    imod Hmask
    imodintro
    try wp_auto
    wp_func_call
    wp_apply_core wp_GetTSC'
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists t1.toNat
    iframe Ht1
    iintro %t2 %Ht12 #Ht2
    imod Hmask
    imodintro
    try wp_auto
    wp_if_destruct
    all_goals first | (exfalso; word) | skip
    iapply HΦ
    iexact Hf

end proof

end Perennial
