/-
The proof of `channel.Google`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Google
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Web
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Image
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Video

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

set_option maxHeartbeats 400000 in
open github_com.mit_pdos.perennial.goose.testdata.examples.channel.Kind in
/-- In `wp_Google`, the received contract is identified from
`map (contractOf q) remk = pre ++ P :: post` with `List.map_eq_append_iff` /
`List.map_eq_cons_iff`, which gives the index into `remk` directly, so the
loop invariant does not need `NoDup remk` (`pureContractOf_inj` and the
related lemmas are still available). -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.Google.wp_proof
    (wp_Web :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.Web.spec
        (GF := GF) (hG := hG))
    (wp_Image :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.Image.spec
        (GF := GF) (hG := hG))
    (wp_Video :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.Video.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.Google.spec
      (GF := GF) (hG := hG) := fun q => by
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := GoString) (W64 3) $$ [] as %c %γch ⟨#Hchan, %Hcap3, Hown⟩
  · ipureintro; decide
  imod start_future (V := GoString) c γch (.Buffered []) (.inr rfl) $$ Hchan Hown
    with ⟨%γmf, #Hmf, HAwait⟩
  imod future_alloc_promise γmf c (contractOf q KWeb) [] $$ Hmf HAwait
    with ⟨Hprom_web, HAwait⟩
  imod future_alloc_promise γmf c (contractOf q KImg) _ $$ Hmf HAwait
    with ⟨Hprom_img, HAwait⟩
  imod future_alloc_promise γmf c (contractOf q KVid) _ $$ Hmf HAwait
    with ⟨Hprom_vid, HAwait⟩
  rw [show (([] ++ [contractOf q KWeb]) ++ [contractOf q KImg]) ++ [contractOf q KVid] =
      pendingk.map (contractOf (GF := GF) q) from rfl]
  ipersist c
  ipersist query
  wp_apply wp_fork $$ [Hprom_web]
  · wp_auto
    wp_apply wp_Web q
    wp_apply wp_future_fulfill (t := go.string) γmf c (q ++ go!".html") $$ [Hprom_web]
    · iframe Hmf
      unfold Fulfilled
      iexists _
      iframe Hprom_web
      unfold contractOf PureContractOf
      ipureintro; rfl
    itrivial
  wp_apply wp_fork $$ [Hprom_img]
  · wp_auto
    wp_apply wp_Image q
    wp_apply wp_future_fulfill (t := go.string) γmf c (q ++ go!".png") $$ [Hprom_img]
    · iframe Hmf
      unfold Fulfilled
      iexists _
      iframe Hprom_img
      unfold contractOf PureContractOf
      ipureintro; rfl
    itrivial
  wp_apply wp_fork $$ [Hprom_vid]
  · wp_auto
    wp_apply wp_Video q
    wp_apply wp_future_fulfill (t := go.string) γmf c (q ++ go!".mp4") $$ [Hprom_vid]
    · iframe Hmf
      unfold Fulfilled
      iexists _
      iframe Hprom_vid
      unfold contractOf PureContractOf
      ipureintro; rfl
    itrivial
  wp_apply wp_slice_make3 (V := GoString) (W64 0) (W64 3) (by decide) as %sl ⟨Hsl, Hcap_sl, %Hcap⟩
  ihave HI : (∃ (xs : List GoString) (donek remk : List Kind) (sl0 : GoSlice),
      "i" ∷ i_ptr ↦ W64 xs.length ∗
      "results" ∷ results_ptr ↦ sl0 ∗
      "Hsl" ∷ sl0 ↦* xs ∗
      "Hcap" ∷ ownSliceCap GoString sl0 (DFrac.own 1) ∗
      "HAwait" ∷ Await (V := GoString) γmf (remk.map (contractOf q)) ∗
      "%Hi" ∷ ⌜xs.length ≤ 3⌝ ∗
      "%Hrem" ∷ ⌜remk.length = 3 - xs.length⌝ ∗
      "%Hsplit" ∷ ⌜pendingk.Perm (donek ++ remk)⌝ ∗
      "%Hperm" ∷ ⌜xs.Perm (donek.map (valueOf q))⌝ : IProp GF)
    $$ [i results Hsl Hcap_sl HAwait]
  · iexists [], [], pendingk, sl
    iframe
    ipureintro
    exact ⟨by decide, rfl, .refl _, .nil⟩
  wp_for HI
  wp_if_destruct
  · wp_apply wp_future_await (t := go.string) γmf c (remk.map (contractOf q)) $$ [$Hmf $HAwait]
      as %v %P %pre %post ⟨%HsplitP, HPv, HAwait⟩
    obtain ⟨remk1, remk2, rfl, rfl, Hrest⟩ := List.map_eq_append_iff.1 HsplitP
    obtain ⟨k, remk3, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 Hrest
    ihave %Hv := contractOf_sound q k v $$ HPv
    subst Hv
    wp_apply wp_slice_literal (V := GoString) [valueOf q k]
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hsl Hcap Hsl1] as %sl' ⟨Hsl', Hcap', -⟩
    · iframe
    wp_for_post
    iframe
    iexists xs ++ [valueOf q k], donek ++ [k], remk1 ++ remk3, sl'
    rw [show (W64 (xs ++ [valueOf q k]).length : w64) = W64 xs.length + W64 1 by
      simp [BitVec.ofInt_add]]
    rw [List.map_append]
    iframe
    ipureintro
    simp only [List.length_append, List.length_cons, List.length_nil] at Hrem ⊢
    refine ⟨by word, by omega, ?_, ?_⟩
    · rw [List.append_assoc, List.singleton_append]
      exact Hsplit.trans (List.Perm.append_left donek List.perm_middle)
    · rw [List.map_append]
      exact Hperm.append_right _
  · have Hlen : xs.length = 3 := by word
    have Hremk : remk = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst Hremk
    iapply HΦ
    iexists xs
    iframe
    ipureintro
    rw [List.append_nil] at Hsplit
    exact Hperm.trans (Hsplit.symm.map (valueOf q))

end proof

end Perennial
