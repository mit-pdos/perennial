/-
Port of `new/proof/github_com/goose_lang/std.v`: specs for
`github.com/goose-lang/std`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Proof.math
import Perennial.Proof.time
import Perennial.Code.github_com.goose_lang.std
import Perennial.GeneratedProof.github_com.goose_lang.std
import Perennial.Proof.github_com.goose_lang.primitive
import Perennial.Proof.github_com.goose_lang.std.std_core
import Perennial.Proof.sync

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace github_com.goose_lang.std

theorem sint_nonneg_of_lt (i n : w64) (h : uint.Z i < uint.Z n) (hn : 0 ≤ sint.Z n) :
    0 ≤ sint.Z i ∧ sint.Z i = uint.Z i := by
  constructor <;> word

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.goose_lang.std :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.goose_lang.std :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.goose_lang.std get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply github_com.goose_lang.std.std_core.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown
    as ⟨Hown, #H1⟩
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply time.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
  wp_apply sync.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H4⟩
  wp_apply math.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H5⟩
  iframe Hown
  is_pkg_init_finish

theorem wp_Assert (cond : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std ∗ ⌜cond = true⌝ }}
      (App (Val (@! Assert)) (Val #cond))
    {{ RET #(); True }} := by
  wp_start as %Hc
  subst Hc
  wp_auto
  wp_end

theorem wp_SumNoOverflow (x y : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std }}
      (App (App (Val (@! SumNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(decide (uint.Z (x + y) = uint.Z x + uint.Z y)); True }} := by
  wp_start
  wp_auto
  wp_apply github_com.goose_lang.std.std_core.wp_SumNoOverflow
  wp_end

theorem wp_SumAssumeNoOverflow (x y : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std }}
      (App (App (Val (@! SumAssumeNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(x + y); ⌜uint.Z (x + y) = uint.Z x + uint.Z y⌝ }} := by
  wp_start
  wp_auto
  wp_apply github_com.goose_lang.std.std_core.wp_SumAssumeNoOverflow as %H
  wp_end

theorem wp_SignedSumAssumeNoOverflow (x y : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std }}
      (App (App (Val (@! SignedSumAssumeNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(x + y); ⌜sint.Z (x + y) = sint.Z x + sint.Z y⌝ }} := by
  wp_start
  wp_auto
  simp only [math.MaxInt, math.MinInt]
  wp_if_destruct
  · wp_if_destruct
    · wp_apply github_com.goose_lang.primitive.wp_Assume as %_
      iapply HΦ; ipureintro; word
    · wp_if_destruct
      · wp_if_destruct
        · wp_apply github_com.goose_lang.primitive.wp_Assume as %_
          iapply HΦ; ipureintro; word
        · wp_apply github_com.goose_lang.primitive.wp_Assume as %h
          cases h
      · wp_apply github_com.goose_lang.primitive.wp_Assume as %h
        cases h
  · wp_if_destruct
    · wp_if_destruct
      · wp_apply github_com.goose_lang.primitive.wp_Assume as %_
        iapply HΦ; ipureintro; word
      · wp_apply github_com.goose_lang.primitive.wp_Assume as %h
        cases h
    · wp_apply github_com.goose_lang.primitive.wp_Assume as %h
      cases h

theorem wp_BytesEqual (s1 s2 : slice.t) (xs1 xs2 : List w8) (dq1 dq2 : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std ∗
        s1 ↦*{dq1} xs1 ∗ s2 ↦*{dq2} xs2 }}
      (App (App (Val (@! BytesEqual)) (Val #s1)) (Val #s2))
    {{ RET #(decide (xs1 = xs2)); s1 ↦*{dq1} xs1 ∗ s2 ↦*{dq2} xs2 }} := by
  wp_start as ⟨Hs1, Hs2⟩
  wp_auto
  ihave %Hl1 := ownSlice_len _ _ _ $$ Hs1
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hs2
  by_cases hlen : s1.len = s2.len
  · simp only [hlen, _root_.decide_true, Bool.not_true]
    wp_auto
    have hl : xs1.length = xs2.length := by rw [Hl1.1, Hl2.1, hlen]
    ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
        "%Hbound" ∷ ⌜uint.Z i ≤ xs1.length⌝ ∗
        "%Hi" ∷ ⌜∀ n : Nat, n < uint.nat i → xs1[n]? = xs2[n]?⌝ : IProp GF) $$ [i]
    · iexists (W64 0); iframe; ipureintro
      exact ⟨by simp [uint.Z], fun n h => by simp [uint.nat] at h⟩
    wp_for HI
    by_cases Hif : uint.Z i < uint.Z s2.len
    · simp only [Hif, _root_.decide_true, ↓reduceIte]
      wp_auto
      have hi := sint_nonneg_of_lt i s2.len Hif Hl2.2
      have hi1 : sint.Z i < sint.Z s1.len := by rw [hlen]; simp only [sint.Z, uint.Z] at *; word
      have hi2 : sint.Z i < sint.Z s2.len := by simp only [sint.Z, uint.Z] at *; word
      list_elem xs1 (sint.nat i) as a
      list_elem xs2 (sint.nat i) as b
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hi.1, hi1⟩)]
      wp_apply wp_load_slice_index s1 (sint.Z i) xs1 dq1 a hi.1 $$ [Hs1] with Hs1
      · iframe Hs1; ipureintro; exact Ha_lookup
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hi.1, hi2⟩)]
      wp_apply wp_load_slice_index s2 (sint.Z i) xs2 dq2 b hi.1 $$ [Hs2] with Hs2
      · iframe Hs2; ipureintro; exact Hb_lookup
      by_cases hab : a = b
      · subst hab
        simp only [_root_.decide_true, Bool.not_true]
        wp_auto
        wp_for_post
        iframe
        iexists (i + W64 1)
        iframe
        ipureintro
        have hu : uint.Z (i + W64 1) = uint.Z i + 1 := by simp only [sint.Z, uint.Z] at *; word
        constructor
        · simp only [sint.nat, sint.Z, uint.Z] at *; omega
        · intro n hn
          by_cases hn' : n < uint.nat i
          · exact Hi n hn'
          · have : n = sint.nat i := by simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega
            subst this; rw [Ha_lookup, Hb_lookup]
      · simp only [hab, _root_.decide_false, Bool.not_false]
        wp_auto
        wp_for_post
        rw [decide_eq_false (fun h => hab (by subst h; rw [Ha_lookup] at Hb_lookup; exact Option.some.inj Hb_lookup))]
        wp_end
    · simp only [Hif, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      have hl2u := github_com.goose_lang.std.std_core.sint_eq_uint _ Hl2.2
      rw [decide_eq_true (List.ext_getElem? fun n => by
        by_cases hn : n < uint.nat i
        · exact Hi n hn
        · rw [List.getElem?_eq_none (by simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega),
            List.getElem?_eq_none (by simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega)])]
      wp_end
  · simp only [hlen, _root_.decide_false, Bool.not_false]
    wp_auto
    rw [decide_eq_false (fun h => hlen (by
      have := congrArg List.length h
      simp only [sint.nat, sint.Z] at *
      apply BitVec.eq_of_toInt_eq; omega))]
    wp_end

theorem wp_BytesClone (b : slice.t) (xs : List w8) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std ∗ b ↦*{dq} xs }}
      (App (Val (@! BytesClone)) (Val #b))
    {{ (b' : slice.t), RET #b'; b' ↦* xs ∗ ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as Hb
  wp_auto
  by_cases Hif : b = slice.nil
  · subst Hif
    simp only [_root_.decide_true]
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    have hb : xs = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen.1]; rfl)
    subst hb
    iapply HΦ
    isplitl []
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  · simp only [decide_eq_false Hif]
    wp_pure; wp_pure; wp_pure; wp_pure; wp_pure; wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) []
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, Hsl_cap⟩
    wp_auto
    wp_apply wp_slice_append (V := w8) (t := go.byte) _ [] b xs dq $$ [Hsl Hsl_cap Hb]
      with %s' ⟨Hs', Hs'_cap, Hb⟩
    · iframe Hsl Hsl_cap Hb
    rw [List.nil_append]
    iapply HΦ
    iframe Hs' Hs'_cap

/-- `if done_b then P else True` (a `def`, so that the proof mode does not
unfold the `if`). -/
def jhP (done_b : Bool) (P : IProp GF) : IProp GF := if done_b then P else iprop(True)

abbrev jhInv (l : Loc) (P : IProp GF) : IProp GF :=
  iprop(∃ done_b : Bool,
    "done_b" ∷ typedPointsto (structFieldRef JoinHandle go!"done" l) done_b (DFrac.own 1) ∗
    "HP" ∷ jhP done_b P)

def isJoinHandle (l : Loc) (P : IProp GF) : IProp GF :=
  iprop(∃ (mu_l cond_l : Loc),
    "#mu" ∷ typedPointsto (structFieldRef JoinHandle go!"mu" l) mu_l DFrac.discard ∗
    "#cond" ∷ typedPointsto (structFieldRef JoinHandle go!"cond" l) cond_l DFrac.discard ∗
    "#Hcond" ∷ sync.isCond cond_l (interface.mk (go.GoType.PointerType sync.Mutex.ty) #mu_l) ∗
    "#Hlock" ∷ sync.isMutex mu_l (jhInv l P))

instance isJoinHandle_persistent (l : Loc) (P : IProp GF) :
    Persistent (isJoinHandle (GF := GF) l P) := by
  unfold isJoinHandle named; infer_instance

theorem wp_newJoinHandle (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std }}
      (App (Val (@! newJoinHandle)) (Val #()))
    {{ (l : Loc), RET #l; isJoinHandle l P }} := by
  wp_start
  wp_auto
  wp_apply sync.wp_NewCond as %cond_l #Hcond
  wp_alloc jh_l as Hjh
  iStructNamed Hjh
  ipersist mu
  ipersist cond
  imod sync.init_Mutex (jhInv jh_l P) ⊤ «$r0_ptr» $$ «$r0» [done] with #Hlock
  · inext; iexists false; iframe; unfold jhP; simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  wp_auto
  iapply HΦ
  unfold isJoinHandle
  iexists «$r0_ptr», cond_l
  iframe #

theorem JoinHandle.wp_finish (l : Loc) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std ∗ isJoinHandle l P ∗ P }}
      (App (Val (l @!! go.GoType.PointerType JoinHandle.ty @!! go!"finish")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hhandle, HPin⟩
  unfold isJoinHandle
  iNamed Hhandle
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨locked, Hinv⟩
  iNamed Hinv
  wp_auto
  wp_apply sync.Cond.wp_Signal $$ [$Hcond]
  wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $locked done_b HPin HP]
  · iclear HP
    inext; iexists true; iframe done_b; unfold jhP; simp only [↓reduceIte]; iframe HPin
  wp_end

theorem wp_Spawn (P : IProp GF) (f : func.t) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std ∗
        (∀ Φ : val → IProp GF, ▷ (P -∗ Φ #()) -∗ WP (App (Val #f) (Val #())) {{ Φ }}) }}
      (App (Val (@! Spawn)) (Val #f))
    {{ (l : Loc), RET #l; isJoinHandle l P }} := by
  wp_start as Hwp
  wp_auto
  wp_apply wp_newJoinHandle P as %l #Hhandle
  ipersist f
  ipersist h
  wp_bind (Fork _)
  iapply wp_fork $$ [Hwp] [-]
  · inext
    wp_auto
    wp_apply Hwp
    iintro HP
    wp_auto
    wp_apply JoinHandle.wp_finish $$ [$Hhandle $HP]
    itrivial
  · inext
    wp_auto
    iapply HΦ $$ Hhandle

theorem JoinHandle.wp_Join (l : Loc) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std ∗ isJoinHandle l P }}
      (App (Val (l @!! go.GoType.PointerType JoinHandle.ty @!! go!"Join")) (Val #()))
    {{ RET #(); P }} := by
  wp_start as #Hjh
  unfold isJoinHandle
  iNamed Hjh
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hinv⟩
  iNamed Hinv
  ihave HI : (∃ done_b : Bool,
      "locked" ∷ sync.ownMutex mu_l ∗
      "done" ∷ typedPointsto (structFieldRef JoinHandle go!"done" l) done_b (DFrac.own 1) ∗
      "HP" ∷ jhP done_b P : IProp GF) $$ [Hlocked done_b HP]
  · iexists done_b; iframe
  wp_for HI
  cases done_b with
  | false =>
    wp_auto
    ihave #Hlk := sync.Mutex_is_Locker mu_l (jhInv l P) $$ [] Hlock
    · iPkgInit
    wp_apply sync.Cond.wp_Wait cond_l _ iprop(sync.ownMutex mu_l ∗ jhInv l P)
      $$ [$Hcond $Hlk locked done HP] as ⟨Hlocked, Hlinv⟩
    · iframe locked; iexists false; iframe
    iNamed Hlinv
    wp_for_post
    iframe
    iexists done_b
    iframe
  | true =>
    wp_auto
    wp_for_post
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $locked done]
    · inext; iexists false; iframe done; unfold jhP; simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial
    iapply HΦ
    unfold jhP
    simp only [↓reduceIte]
    iexact HP

end wps

end github_com.goose_lang.std

end Perennial
end
