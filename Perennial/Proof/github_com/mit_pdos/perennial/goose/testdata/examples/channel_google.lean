/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel_google.v`:
Rob Pike's "Google search" example, using the future channel idiom.

Lean notes:
* In `wp_Google`, the received contract is identified from
  `map (contract_of q) remk = pre ++ P :: post` with `List.map_eq_append_iff` /
  `List.map_eq_cons_iff`, which gives the index into `remk` directly; Rocq instead
  identifies it with `pure_contract_of_inj` and a `NoDup remk` invariant. Those
  lemmas are still ported, but the loop invariant does not need `NoDup`.
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel_examples_init
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Bag
import Perennial.Golang.Theory.Chan.Idioms.Future

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

/-! ### Pure part -/

def google_expected (q : go_string) : List go_string :=
  [q ++ go!".html", q ++ go!".png", q ++ go!".mp4"]

inductive kind where
  | KWeb | KImg | KVid
  deriving DecidableEq

open kind

def value_of (q : go_string) (k : kind) : go_string :=
  match k with
  | KWeb => q ++ go!".html"
  | KImg => q ++ go!".png"
  | KVid => q ++ go!".mp4"

def pure_contract_of (q : go_string) (k : kind) : go_string → Prop :=
  fun v => v = value_of q k

theorem value_of_inj (q : go_string) (k1 k2 : kind) (h : value_of q k1 = value_of q k2) :
    k1 = k2 := by
  cases k1 <;> cases k2 <;> simp only [value_of, List.append_cancel_left_eq] at h <;>
    first | rfl | exact absurd h (by decide)

theorem pure_contract_of_inj (q : go_string) (k1 k2 : kind) :
    pure_contract_of q k1 = pure_contract_of q k2 → k1 = k2 := by
  intro Heq
  have h := congrFun Heq (value_of q k1)
  simp only [pure_contract_of, eq_iff_iff, true_iff] at h
  exact value_of_inj q k1 k2 h

def pendingk : List kind := [KWeb, KImg, KVid]

theorem pendingk_nodup : pendingk.Nodup := by decide

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

theorem wp_Web (q : go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! Web)) (Val #q))
    {{ RET #(q ++ go!".html"); True }} := by
  wp_start
  wp_auto
  wp_end

theorem wp_Image (q : go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! Image)) (Val #q))
    {{ RET #(q ++ go!".png"); True }} := by
  wp_start
  wp_auto
  wp_end

theorem wp_Video (q : go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! Video)) (Val #q))
    {{ RET #(q ++ go!".mp4"); True }} := by
  wp_start
  wp_auto
  wp_end

def contract_of (q : go_string) (k : kind) : go_string → IProp GF :=
  fun v => iprop(⌜pure_contract_of q k v⌝)

theorem contract_of_sound (q : go_string) (k : kind) (v : go_string) :
    contract_of (GF := GF) q k v ⊢ ⌜v = value_of q k⌝ := by
  unfold contract_of pure_contract_of
  iintro %Hv
  ipureintro
  exact Hv

theorem mem_map_contract_of (q : go_string) (remk : List kind) (P : go_string → IProp GF) :
    P ∈ remk.map (contract_of q) → ∃ k, k ∈ remk ∧ P = contract_of q k := by
  intro HP
  obtain ⟨k, Hk, rfl⟩ := List.mem_map.1 HP
  exact ⟨k, Hk, rfl⟩

set_option maxHeartbeats 400000 in
theorem wp_Google (q : go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! Google)) (Val #q))
    {{ (sl : slice.t), RET #sl;
        ∃ xs : List go_string, sl ↦* xs ∗ ⌜xs.Perm (google_expected q)⌝ }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := go_string) (W64 3) $$ [] as %c %γch ⟨#Hchan, %Hcap3, Hown⟩
  · ipureintro; decide
  imod start_future (V := go_string) c γch (.Buffered []) (.inr rfl) $$ Hchan Hown
    with ⟨%γmf, #Hmf, HAwait⟩
  imod future_alloc_promise γmf c (contract_of q KWeb) [] $$ Hmf HAwait
    with ⟨Hprom_web, HAwait⟩
  imod future_alloc_promise γmf c (contract_of q KImg) _ $$ Hmf HAwait
    with ⟨Hprom_img, HAwait⟩
  imod future_alloc_promise γmf c (contract_of q KVid) _ $$ Hmf HAwait
    with ⟨Hprom_vid, HAwait⟩
  rw [show (([] ++ [contract_of q KWeb]) ++ [contract_of q KImg]) ++ [contract_of q KVid] =
      pendingk.map (contract_of (GF := GF) q) from rfl]
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
      unfold contract_of pure_contract_of
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
      unfold contract_of pure_contract_of
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
      unfold contract_of pure_contract_of
      ipureintro; rfl
    itrivial
  wp_apply wp_slice_make3 (V := go_string) (W64 0) (W64 3) (by decide) as %sl ⟨Hsl, Hcap_sl, %Hcap⟩
  ihave HI : (∃ (xs : List go_string) (donek remk : List kind) (sl0 : slice.t),
      "i" ∷ i_ptr ↦ W64 xs.length ∗
      "results" ∷ results_ptr ↦ sl0 ∗
      "Hsl" ∷ sl0 ↦* xs ∗
      "Hcap" ∷ own_slice_cap go_string sl0 (DFrac.own 1) ∗
      "HAwait" ∷ Await (V := go_string) γmf (remk.map (contract_of q)) ∗
      "%Hi" ∷ ⌜xs.length ≤ 3⌝ ∗
      "%Hrem" ∷ ⌜remk.length = 3 - xs.length⌝ ∗
      "%Hsplit" ∷ ⌜pendingk.Perm (donek ++ remk)⌝ ∗
      "%Hperm" ∷ ⌜xs.Perm (donek.map (value_of q))⌝ : IProp GF)
    $$ [i results Hsl Hcap_sl HAwait]
  · iexists [], [], pendingk, sl
    iframe
    ipureintro
    exact ⟨by decide, rfl, .refl _, .nil⟩
  wp_for HI
  wp_if_destruct
  · wp_apply wp_future_await (t := go.string) γmf c (remk.map (contract_of q)) $$ [$Hmf $HAwait]
      as %v %P %pre %post ⟨%HsplitP, HPv, HAwait⟩
    obtain ⟨remk1, remk2, rfl, rfl, Hrest⟩ := List.map_eq_append_iff.1 HsplitP
    obtain ⟨k, remk3, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 Hrest
    ihave %Hv := contract_of_sound q k v $$ HPv
    subst Hv
    wp_apply wp_slice_literal (V := go_string) [value_of q k]
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hsl Hcap Hsl1] as %sl' ⟨Hsl', Hcap', -⟩
    · iframe
    wp_for_post
    iframe
    iexists xs ++ [value_of q k], donek ++ [k], remk1 ++ remk3, sl'
    rw [show (W64 (xs ++ [value_of q k]).length : w64) = W64 xs.length + W64 1 by
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
    exact Hperm.trans (Hsplit.symm.map (value_of q))

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
